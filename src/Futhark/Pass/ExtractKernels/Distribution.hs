{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
module Futhark.Pass.ExtractKernels.Distribution
       (
         Target
       , Targets
       , ppTargets
       , singleTarget
       , innerTarget
       , outerTarget
       , pushOuterTarget
       , pushInnerTarget

       , LoopNesting (..)
       , ppLoopNesting

       , Nesting (..)
       , Nestings
       , ppNestings
       , letBindInInnerNesting
       , singleNesting
       , pushInnerNesting

       , KernelNest
       , kernelNestLoops
       , kernelNestWidths
       , boundInKernelNest
       , constructKernel
       , flatKernel

       , tryDistribute
       , tryDistributeBinding
       )
       where

import Control.Applicative
import Control.Monad.RWS.Strict
import Control.Monad.Trans.Maybe
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe
import Data.List
import Data.Ord

import Futhark.Representation.AST.Attributes.Aliases
import Futhark.Representation.Kernels
import qualified Futhark.Representation.AST as AST
import Futhark.MonadFreshNames
import Futhark.Tools
import Futhark.Util
import Futhark.Transform.Rename
import qualified Futhark.Analysis.Alias as Alias
import Futhark.Util.Log

import Prelude

type Target = (Pattern, Result)

-- | First pair element is the very innermost ("current") target.  In
-- the list, the outermost target comes first.
type Targets = (Target, [Target])

ppTargets :: Targets -> String
ppTargets (target, targets) =
  unlines $ map ppTarget $ targets ++ [target]
  where ppTarget (pat, res) =
          pretty pat ++ " <- " ++ pretty res

singleTarget :: Target -> Targets
singleTarget = (,[])

innerTarget :: Targets -> Target
innerTarget = fst

outerTarget :: Targets -> Target
outerTarget (inner_target, []) = inner_target
outerTarget (_, outer_target : _) = outer_target

pushOuterTarget :: Target -> Targets -> Targets
pushOuterTarget target (inner_target, targets) =
  (inner_target, target : targets)

pushInnerTarget :: Target -> Targets -> Targets
pushInnerTarget target (inner_target, targets) =
  (target, targets ++ [inner_target])

data LoopNesting = MapNesting { loopNestingPattern :: Pattern
                              , loopNestingCertificates :: Certificates
                              , loopNestingWidth :: SubExp
                              , loopNestingParamsAndArrs :: [(Param Type, VName)]
                              }
                 deriving (Show)

ppLoopNesting :: LoopNesting -> String
ppLoopNesting (MapNesting _ _ _ params_and_arrs) =
  pretty (map fst params_and_arrs) ++
  " <- " ++
  pretty (map snd params_and_arrs)

loopNestingParams :: LoopNesting -> [LParam]
loopNestingParams  = map fst . loopNestingParamsAndArrs

instance FreeIn LoopNesting where
  freeIn (MapNesting pat cs w params_and_arrs) =
    freeIn pat <>
    freeIn cs <>
    freeIn w <>
    freeIn params_and_arrs

consumedIn :: LoopNesting -> Names
consumedIn (MapNesting pat _ _ params_and_arrs) =
  consumedInPattern pat <>
  mconcat (map (vnameAliases . snd) params_and_arrs)

data Nesting = Nesting { nestingLetBound :: Names
                       , nestingLoop :: LoopNesting
                       }
             deriving (Show)

letBindInNesting :: Names -> Nesting -> Nesting
letBindInNesting newnames (Nesting oldnames loop) =
  Nesting (oldnames <> newnames) loop

-- ^ First pair element is the very innermost ("current") nest.  In
-- the list, the outermost nest comes first.
type Nestings = (Nesting, [Nesting])

ppNestings :: Nestings -> String
ppNestings (nesting, nestings) =
  unlines $ map ppNesting $ nestings ++ [nesting]
  where ppNesting (Nesting _ loop) =
          ppLoopNesting loop

singleNesting :: Nesting -> Nestings
singleNesting = (,[])

pushInnerNesting :: Nesting -> Nestings -> Nestings
pushInnerNesting nesting (inner_nesting, nestings) =
  (nesting, nestings ++ [inner_nesting])

-- | Both parameters and let-bound.
boundInNesting :: Nesting -> Names
boundInNesting nesting =
  HS.fromList (map paramName (loopNestingParams loop)) <>
  nestingLetBound nesting
  where loop = nestingLoop nesting

letBindInInnerNesting :: Names -> Nestings -> Nestings
letBindInInnerNesting names (nest, nestings) =
  (letBindInNesting names nest, nestings)


-- | Note: first element is *outermost* nesting.  This is different
-- from the similar types elsewhere!
type KernelNest = (LoopNesting, [LoopNesting])

-- | Add new outermost nesting, pushing the current outermost to the
-- list, also taking care to swap patterns if necessary.
pushKernelNesting :: Target -> LoopNesting -> KernelNest -> KernelNest
pushKernelNesting target newnest (nest, nests) =
  (fixNestingPatternOrder newnest target (loopNestingPattern nest),
   nest : nests)

fixNestingPatternOrder :: LoopNesting -> Target -> Pattern -> LoopNesting
fixNestingPatternOrder nest (_,res) inner_pat =
  nest { loopNestingPattern = basicPattern' [] pat' }
  where pat = loopNestingPattern nest
        pat' = map fst fixed_target
        fixed_target = sortBy (comparing posInInnerPat) $ zip (patternValueIdents pat) res
        posInInnerPat (_, Var v) = fromMaybe 0 $ elemIndex v $ patternNames inner_pat
        posInInnerPat _          = 0

newKernel :: LoopNesting -> KernelNest
newKernel nest = (nest, [])

kernelNestLoops :: KernelNest -> [LoopNesting]
kernelNestLoops (loop, loops) = loop : loops

boundInKernelNest :: KernelNest -> Names
boundInKernelNest = HS.fromList .
                    map paramName .
                    concatMap (map fst . loopNestingParamsAndArrs) .
                    kernelNestLoops

kernelNestWidths :: KernelNest -> [SubExp]
kernelNestWidths = map loopNestingWidth . kernelNestLoops

constructKernel :: MonadFreshNames m =>
                   KernelNest -> Body -> m ([Binding], Binding)
constructKernel kernel_nest inner_body = do
  (w_bnds, w, ispace, inps, rts) <- flatKernel kernel_nest
  let rank = length ispace
      returns = [ (rt, [0..rank + arrayRank rt - 1]) | rt <- rts ]
      used_inps = filter inputIsUsed inps
  index <- newVName "kernel_thread_index"
  return (w_bnds,
          Let (loopNestingPattern first_nest) () $ Op $
          MapKernel (loopNestingCertificates first_nest) w index ispace used_inps returns inner_body)
  where
    first_nest = fst kernel_nest
    inputIsUsed input = kernelInputName input `HS.member`
                        freeInBody inner_body

-- | Flatten a kernel nesting to:
--
--  (0) Ancillary prologue bindings.
--
--  (1) The total number of threads, equal to the product of all
--  nesting widths, and equal to the product of the index space.
--
--  (2) The index space.
--
--  (3) The kernel inputs - not that some of these may be unused.
--
--  (4) The per-thread return type.
flatKernel :: MonadFreshNames m =>
              KernelNest
           -> m ([Binding],
                 SubExp,
                 [(VName, SubExp)],
                 [KernelInput Kernels],
                 [Type])
flatKernel (MapNesting pat _ nesting_w params_and_arrs, []) = do
  i <- newVName "i"
  let inps = [ KernelInput param arr [Var i] |
               (param, arr) <- params_and_arrs ]
  return ([], nesting_w, [(i,nesting_w)], inps,
          map rowType $ patternTypes pat)

flatKernel (MapNesting _ _ nesting_w params_and_arrs, nest : nests) = do
  (w_bnds, w, ispace, inps, returns) <- flatKernel (nest, nests)
  i <- newVName "i"

  w' <- newVName "nesting_size"
  let w_bnd = mkLet' [] [Ident w' $ Prim int32] $
              PrimOp $ BinOp (Mul Int32) w nesting_w

  let inps' = map fixupInput inps
      isParam inp =
        snd <$> find ((==kernelInputArray inp) . paramName . fst) params_and_arrs
      fixupInput inp
        | Just arr <- isParam inp =
            inp { kernelInputArray = arr
                , kernelInputIndices = Var i : kernelInputIndices inp }
        | otherwise =
            inp

  return (w_bnds++[w_bnd], Var w', (i, nesting_w) : ispace, extra_inps i <> inps', returns)
  where extra_inps i =
          [ KernelInput param arr [Var i] |
            (param, arr) <- params_and_arrs ]

-- | Description of distribution to do.
data DistributionBody = DistributionBody {
    distributionTarget :: Targets
  , distributionFreeInBody :: Names
  , distributionConsumedInBody :: Names
  , distributionIdentityMap :: HM.HashMap VName Ident
  , distributionExpandTarget :: Target -> Target
    -- ^ Also related to avoiding identity mapping.
  }

distributionInnerPattern :: DistributionBody -> Pattern
distributionInnerPattern = fst . innerTarget . distributionTarget

distributionBodyFromBindings :: (Attributes lore, CanBeAliased (Op lore)) =>
                                Targets -> [AST.Binding lore] -> (DistributionBody, Result)
distributionBodyFromBindings ((inner_pat, inner_res), targets) bnds =
  let bound_by_bnds = boundByBindings bnds
      (inner_pat', inner_res', inner_identity_map, inner_expand_target) =
        removeIdentityMappingGeneral bound_by_bnds inner_pat inner_res
  in (DistributionBody
      { distributionTarget = ((inner_pat', inner_res'), targets)
      , distributionFreeInBody = mconcat (map freeInBinding bnds)
                                 `HS.difference` bound_by_bnds
      , distributionConsumedInBody =
        mconcat (map (consumedInBinding . Alias.analyseBinding) bnds)
        `HS.difference` bound_by_bnds
      , distributionIdentityMap = inner_identity_map
      , distributionExpandTarget = inner_expand_target
      },
      inner_res')

distributionBodyFromBinding :: (Attributes lore, CanBeAliased (Op lore)) =>
                               Targets -> AST.Binding lore -> (DistributionBody, Result)
distributionBodyFromBinding targets bnd =
  distributionBodyFromBindings targets [bnd]

createKernelNest :: (MonadFreshNames m, HasScope t m) =>
                    Nestings
                 -> DistributionBody
                 -> m (Maybe (Targets, KernelNest))
createKernelNest (inner_nest, nests) distrib_body = do
  let (target, targets) = distributionTarget distrib_body
  unless (length nests == length targets) $
    fail $ "Nests and targets do not match!\n" ++
    "nests: " ++ ppNestings (inner_nest, nests) ++
    "\ntargets:" ++ ppTargets (target, targets)
  runMaybeT $ fmap prepare $ recurse $ zip nests targets

  where prepare (x, _, _, z) = (z, x)
        bound_in_nest =
          mconcat $ map boundInNesting $ inner_nest : nests
        -- | Can something of this type be taken outside the nest?
        -- I.e. are none of its dimensions bound inside the nest.
        distributableType =
          HS.null . HS.intersection bound_in_nest . freeIn . arrayDims

        distributeAtNesting :: (HasScope t m, MonadFreshNames m) =>
                               Nesting
                            -> Pattern
                            -> (LoopNesting -> KernelNest, Names, Names)
                            -> HM.HashMap VName Ident
                            -> [Ident]
                            -> (Target -> Targets)
                            -> MaybeT m (KernelNest, Names, Names, Targets)
        distributeAtNesting
          (Nesting nest_let_bound nest)
          pat
          (add_to_kernel, free_in_kernel, consumed_in_kernel)
          identity_map
          inner_returned_arrs
          addTarget = do
          let nest'@(MapNesting _ cs w params_and_arrs) =
                removeUnusedNestingParts free_in_kernel nest
              (params,arrs) = unzip params_and_arrs
              param_names = HS.fromList $ map paramName params
              free_in_kernel' =
                (freeIn nest' <> free_in_kernel) `HS.difference` param_names
              required_from_nest =
                free_in_kernel' `HS.intersection` nest_let_bound

          required_from_nest_idents <-
            forM (HS.toList required_from_nest) $ \name -> do
              t <- lift $ lookupType name
              return $ Ident name t

          (free_params, free_arrs, bind_in_target) <-
            fmap unzip3 $
            forM (inner_returned_arrs++required_from_nest_idents) $
            \(Ident pname ptype) ->
              case HM.lookup pname identity_map of
                Nothing -> do
                  arr <- newIdent (baseString pname ++ "_r") $
                         arrayOfRow ptype w
                  return (Param pname ptype,
                          arr,
                          True)
                Just arr ->
                  return (Param pname ptype,
                          arr,
                          False)

          let free_arrs_pat =
                basicPattern [] $ map ((,BindVar) . snd) $
                filter fst $ zip bind_in_target free_arrs
              free_params_pat =
                map snd $ filter fst $ zip bind_in_target free_params

              (actual_params, actual_arrs) =
                (params++free_params,
                 arrs++map identName free_arrs)
              actual_param_names =
                HS.fromList $ map paramName actual_params

              nest'' =
                removeUnusedNestingParts free_in_kernel $
                MapNesting pat cs w $ zip actual_params actual_arrs

              free_in_kernel'' =
                (freeIn nest'' <> free_in_kernel) `HS.difference` actual_param_names

              consumed_in_kernel' =
                (consumedIn nest'' <> consumed_in_kernel) `HS.difference` actual_param_names

          unless (all (distributableType . paramType) $
                  loopNestingParams nest'') $
            fail "Would induce irregular array"
          return (add_to_kernel nest'',

                  free_in_kernel'',

                  consumed_in_kernel',

                  addTarget (free_arrs_pat, map (Var . paramName) free_params_pat))

        recurse :: (HasScope t m, MonadFreshNames m) =>
                   [(Nesting,Target)]
                -> MaybeT m (KernelNest, Names, Names, Targets)
        recurse [] =
          distributeAtNesting
          inner_nest
          (distributionInnerPattern distrib_body)
          (newKernel,
           distributionFreeInBody distrib_body `HS.intersection` bound_in_nest,
           distributionConsumedInBody distrib_body `HS.intersection` bound_in_nest)
          (distributionIdentityMap distrib_body)
          [] $
          singleTarget . distributionExpandTarget distrib_body

        recurse ((nest, (pat,res)) : nests') = do
          (kernel@(outer, _), kernel_free, kernel_consumed, kernel_targets) <- recurse nests'

          let (pat', res', identity_map, expand_target) =
                removeIdentityMappingFromNesting
                (HS.fromList $ patternNames $ loopNestingPattern outer) pat res

          distributeAtNesting
            nest
            pat'
            (\k -> pushKernelNesting (pat',res') k kernel,
             kernel_free,
             kernel_consumed)
            identity_map
            (patternIdents $ fst $ outerTarget kernel_targets)
            ((`pushOuterTarget` kernel_targets) . expand_target)

removeUnusedNestingParts :: Names -> LoopNesting -> LoopNesting
removeUnusedNestingParts used (MapNesting pat cs w params_and_arrs) =
  MapNesting pat cs w $ zip used_params used_arrs
  where (params,arrs) = unzip params_and_arrs
        (used_params, used_arrs) =
          unzip $
          filter ((`HS.member` used) . paramName . fst) $
          zip params arrs

removeIdentityMappingGeneral :: Names -> Pattern -> Result
                             -> (Pattern,
                                 Result,
                                 HM.HashMap VName Ident,
                                 Target -> Target)
removeIdentityMappingGeneral bound pat res =
  let (identities, not_identities) =
        mapEither isIdentity $ zip (patternElements pat) res
      (not_identity_patElems, not_identity_res) = unzip not_identities
      (identity_patElems, identity_res) = unzip identities
      expandTarget (tpat, tres) =
        (Pattern [] $ patternElements tpat ++ identity_patElems,
         tres ++ map Var identity_res)
      identity_map = HM.fromList $ zip identity_res $
                      map patElemIdent identity_patElems
  in (Pattern [] not_identity_patElems,
      not_identity_res,
      identity_map,
      expandTarget)
  where isIdentity (patElem, Var v)
          | not (v `HS.member` bound) = Left (patElem, v)
        isIdentity x                  = Right x

removeIdentityMappingFromNesting :: Names -> Pattern -> Result
                                 -> (Pattern,
                                     Result,
                                     HM.HashMap VName Ident,
                                     Target -> Target)
removeIdentityMappingFromNesting bound_in_nesting pat res =
  let (pat', res', identity_map, expand_target) =
        removeIdentityMappingGeneral bound_in_nesting pat res
  in (pat', res', identity_map, expand_target)

tryDistribute :: (MonadFreshNames m, HasScope t m, MonadLogger m) =>
                 Nestings -> Targets -> [Binding]
              -> m (Maybe (Targets, [Binding]))
tryDistribute _ targets [] =
  -- No point in distributing an empty kernel.
  return $ Just (targets, [])
tryDistribute nest targets bnds =
  createKernelNest nest dist_body >>=
  \case
    Just (targets', distributed) -> do
      (w_bnds, kernel_bnd) <- constructKernel distributed inner_body
      distributed' <- optimiseKernel <$> renameBinding kernel_bnd
      logMsg $ "distributing\n" ++
        pretty (mkBody bnds $ snd $ innerTarget targets) ++
        "\nas\n" ++ pretty distributed' ++
        "\ndue to targets\n" ++ ppTargets targets ++
        "\nand with new targets\n" ++ ppTargets targets'
      return $ Just (targets', w_bnds ++ [distributed'])
    Nothing ->
      return Nothing
  where (dist_body, inner_body_res) = distributionBodyFromBindings targets bnds
        inner_body = mkBody bnds inner_body_res

tryDistributeBinding :: (MonadFreshNames m, HasScope t m,
                         Attributes lore, CanBeAliased (Op lore)) =>
                        Nestings -> Targets -> AST.Binding lore
                     -> m (Maybe (Result, Targets, KernelNest))
tryDistributeBinding nest targets bnd =
  fmap addRes <$> createKernelNest nest dist_body
  where (dist_body, res) = distributionBodyFromBinding targets bnd
        addRes (targets', kernel_nest) = (res, targets', kernel_nest)

optimiseKernel :: Binding -> Binding
optimiseKernel bnd = fromMaybe bnd $
                     tryOptimiseKernel bnd

tryOptimiseKernel :: Binding -> Maybe Binding
tryOptimiseKernel bnd = kernelIsRearrange bnd <|>
                        kernelIsReshape bnd <|>
                        kernelIsCopy bnd

singleBindingBody :: Body -> Maybe Binding
singleBindingBody (Body _ [bnd] [res])
  | [res] == map Var (patternNames $ bindingPattern bnd) =
      Just bnd
singleBindingBody _ = Nothing

singleExpBody :: Body -> Maybe Exp
singleExpBody = fmap bindingExp . singleBindingBody

fullIndexInput :: [(VName, SubExp)] -> [KernelInput lore]
               -> Maybe (KernelInput lore)
fullIndexInput ispace =
  find $ (==map (Var . fst) ispace) . kernelInputIndices

kernelIsRearrange :: Binding -> Maybe Binding
kernelIsRearrange (Let (Pattern [] [outer_patElem]) _
                   (Op (MapKernel outer_cs _ _ ispace [inp] [_] body)))
  | Just (PrimOp (Rearrange inner_cs perm arr)) <- singleExpBody body,
    map (Var . fst) ispace == kernelInputIndices inp,
    arr == kernelInputName inp =
      let rank = length ispace
          cs' = outer_cs ++ inner_cs
          perm' = [0..rank-1] ++ map (rank+) perm
      in Just $ Let (Pattern [] [outer_patElem]) () $
         PrimOp $ Rearrange cs' perm' $ kernelInputArray inp
kernelIsRearrange _ = Nothing

kernelIsReshape :: Binding -> Maybe Binding
kernelIsReshape (Let (Pattern [] [outer_patElem]) ()
                 (Op (MapKernel outer_cs _ _ ispace inps [_] body)))
  | Just (PrimOp (Reshape inner_cs new_inner_shape arr)) <- singleExpBody body,
    Just inp <- fullIndexInput ispace inps,
    map (Var . fst) ispace == kernelInputIndices inp,
    arr == kernelInputName inp =
      let new_outer_shape =
            take (length new_shape - length new_inner_shape) new_shape
          cs' = outer_cs ++ inner_cs
      in Just $ Let (Pattern [] [outer_patElem]) () $
         PrimOp $ Reshape cs' (map DimCoercion new_outer_shape ++ new_inner_shape) $
         kernelInputArray inp
  where new_shape = arrayDims $ patElemType outer_patElem
kernelIsReshape _ = Nothing

kernelIsCopy :: Binding -> Maybe Binding
kernelIsCopy (Let pat ()
              (Op (MapKernel _ _ _ ispace inps [_] body)))
  | Just (PrimOp (Copy arr)) <- singleExpBody body,
    Just inp <- fullIndexInput ispace inps,
    map (Var . fst) ispace == kernelInputIndices inp,
    arr == kernelInputName inp =
      Just $ Let pat () $
      PrimOp $ Copy $ kernelInputArray inp
kernelIsCopy _ = Nothing
