{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- | Expand allocations inside of maps when possible.
module Futhark.Pass.ExpandAllocations (expandAllocations) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List (find, foldl')
import qualified Data.Map.Strict as M
import Data.Maybe
import Futhark.Analysis.Rephrase
import qualified Futhark.Analysis.SymbolTable as ST
import Futhark.Error
import Futhark.IR
import qualified Futhark.IR.GPU.Simplify as GPU
import Futhark.IR.GPUMem
import qualified Futhark.IR.Mem.IxFun as IxFun
import Futhark.MonadFreshNames
import Futhark.Optimise.Simplify.Rep (addScopeWisdom)
import Futhark.Pass
import Futhark.Pass.ExplicitAllocations.GPU (explicitAllocationsInStms)
import Futhark.Pass.ExtractKernels.BlockedKernel (nonSegRed)
import Futhark.Pass.ExtractKernels.ToGPU (segThread)
import Futhark.Tools
import Futhark.Transform.CopyPropagate (copyPropagateInFun)
import Futhark.Transform.Rename (renameStm)
import Futhark.Util (mapAccumLM)
import Futhark.Util.IntegralExp
import Prelude hiding (quot)

-- | The memory expansion pass definition.
expandAllocations :: Pass GPUMem GPUMem
expandAllocations =
  Pass "expand allocations" "Expand allocations" $
    \(Prog consts funs) -> do
      consts' <-
        modifyNameSource $ limitationOnLeft . runStateT (runReaderT (transformStms consts) mempty)
      Prog consts' <$> mapM (transformFunDef $ scopeOf consts') funs

-- Cannot use intraproceduralTransformation because it might create
-- duplicate size keys (which are not fixed by renamer, and size
-- keys must currently be globally unique).

type ExpandM = ReaderT (Scope GPUMem) (StateT VNameSource (Either String))

limitationOnLeft :: Either String a -> a
limitationOnLeft = either compilerLimitationS id

transformFunDef ::
  Scope GPUMem ->
  FunDef GPUMem ->
  PassM (FunDef GPUMem)
transformFunDef scope fundec = do
  body' <- modifyNameSource $ limitationOnLeft . runStateT (runReaderT m mempty)
  copyPropagateInFun
    simpleGPUMem
    (ST.fromScope (addScopeWisdom scope))
    fundec {funDefBody = body'}
  where
    m =
      localScope scope $
        inScopeOf fundec $
          transformBody $ funDefBody fundec

transformBody :: Body GPUMem -> ExpandM (Body GPUMem)
transformBody (Body () stms res) = Body () <$> transformStms stms <*> pure res

transformLambda :: Lambda GPUMem -> ExpandM (Lambda GPUMem)
transformLambda (Lambda params body ret) =
  Lambda params
    <$> localScope (scopeOfLParams params) (transformBody body)
    <*> pure ret

transformStms :: Stms GPUMem -> ExpandM (Stms GPUMem)
transformStms stms =
  inScopeOf stms $ mconcat <$> mapM transformStm (stmsToList stms)

transformStm :: Stm GPUMem -> ExpandM (Stms GPUMem)
-- It is possible that we are unable to expand allocations in some
-- code versions.  If so, we can remove the offending branch.  Only if
-- both versions fail do we propagate the error.
transformStm (Let pat aux (If cond tbranch fbranch (IfDec ts IfEquiv))) = do
  tbranch' <- (Right <$> transformBody tbranch) `catchError` (return . Left)
  fbranch' <- (Right <$> transformBody fbranch) `catchError` (return . Left)
  case (tbranch', fbranch') of
    (Left _, Right fbranch'') ->
      return $ useBranch fbranch''
    (Right tbranch'', Left _) ->
      return $ useBranch tbranch''
    (Right tbranch'', Right fbranch'') ->
      return $ oneStm $ Let pat aux $ If cond tbranch'' fbranch'' (IfDec ts IfEquiv)
    (Left e, _) ->
      throwError e
  where
    bindRes pe se = Let (Pattern [] [pe]) (defAux ()) $ BasicOp $ SubExp se

    useBranch b =
      bodyStms b
        <> stmsFromList (zipWith bindRes (patternElements pat) (bodyResult b))
transformStm (Let pat aux e) = do
  (bnds, e') <- transformExp =<< mapExpM transform e
  return $ bnds <> oneStm (Let pat aux e')
  where
    transform =
      identityMapper
        { mapOnBody = \scope -> localScope scope . transformBody
        }

transformExp :: Exp GPUMem -> ExpandM (Stms GPUMem, Exp GPUMem)
transformExp (Op (Inner (SegOp (SegMap lvl space ts kbody)))) = do
  (alloc_stms, (_, kbody')) <- transformScanRed lvl space [] kbody
  return
    ( alloc_stms,
      Op $ Inner $ SegOp $ SegMap lvl space ts kbody'
    )
transformExp (Op (Inner (SegOp (SegRed lvl space reds ts kbody)))) = do
  (alloc_stms, (lams, kbody')) <-
    transformScanRed lvl space (map segBinOpLambda reds) kbody
  let reds' = zipWith (\red lam -> red {segBinOpLambda = lam}) reds lams
  return
    ( alloc_stms,
      Op $ Inner $ SegOp $ SegRed lvl space reds' ts kbody'
    )
transformExp (Op (Inner (SegOp (SegScan lvl space scans ts kbody)))) = do
  (alloc_stms, (lams, kbody')) <-
    transformScanRed lvl space (map segBinOpLambda scans) kbody
  let scans' = zipWith (\red lam -> red {segBinOpLambda = lam}) scans lams
  return
    ( alloc_stms,
      Op $ Inner $ SegOp $ SegScan lvl space scans' ts kbody'
    )
transformExp (Op (Inner (SegOp (SegHist lvl space ops ts kbody)))) = do
  (alloc_stms, (lams', kbody')) <- transformScanRed lvl space lams kbody
  let ops' = zipWith onOp ops lams'
  return
    ( alloc_stms,
      Op $ Inner $ SegOp $ SegHist lvl space ops' ts kbody'
    )
  where
    lams = map histOp ops
    onOp op lam = op {histOp = lam}
transformExp (WithAcc inputs lam) = do
  lam' <- transformLambda lam
  (input_alloc_stms, inputs') <- unzip <$> mapM onInput inputs
  pure
    ( mconcat input_alloc_stms,
      WithAcc inputs' lam'
    )
  where
    onInput (shape, arrs, Nothing) =
      pure (mempty, (shape, arrs, Nothing))
    onInput (shape, arrs, Just (op_lam, nes)) = do
      bound_outside <- asks $ namesFromList . M.keys
      let -- XXX: fake a SegLevel, which we don't have here.  We will not
          -- use it for anything, as we will not allow irregular
          -- allocations inside the update function.
          lvl = SegThread (Count $ intConst Int64 0) (Count $ intConst Int64 0) SegNoVirt
          (op_lam', lam_allocs) =
            extractLambdaAllocations (lvl, [0]) bound_outside mempty op_lam
          variantAlloc (_, Var v, _) = not $ v `nameIn` bound_outside
          variantAlloc _ = False
          (variant_allocs, invariant_allocs) = M.partition variantAlloc lam_allocs

      case M.elems variant_allocs of
        (_, v, _) : _ ->
          throwError $
            "Cannot handle un-sliceable allocation size: " ++ pretty v
              ++ "\nLikely cause: irregular nested operations inside accumulator update operator."
        [] ->
          return ()

      let num_is = shapeRank shape
          is = map paramName $ take num_is $ lambdaParams op_lam
      (alloc_stms, alloc_offsets) <-
        genericExpandedInvariantAllocations (const (shape, map le64 is)) invariant_allocs

      scope <- askScope
      let scope' = scopeOf op_lam <> scope
      either throwError pure $
        runOffsetM scope' alloc_offsets $ do
          op_lam'' <- offsetMemoryInLambda op_lam'
          return (alloc_stms, (shape, arrs, Just (op_lam'', nes)))
transformExp e =
  return (mempty, e)

transformScanRed ::
  SegLevel ->
  SegSpace ->
  [Lambda GPUMem] ->
  KernelBody GPUMem ->
  ExpandM (Stms GPUMem, ([Lambda GPUMem], KernelBody GPUMem))
transformScanRed lvl space ops kbody = do
  bound_outside <- asks $ namesFromList . M.keys
  let user = (lvl, [le64 $ segFlat space])
      (kbody', kbody_allocs) =
        extractKernelBodyAllocations user bound_outside bound_in_kernel kbody
      (ops', ops_allocs) = unzip $ map (extractLambdaAllocations user bound_outside mempty) ops
      variantAlloc (_, Var v, _) = not $ v `nameIn` bound_outside
      variantAlloc _ = False
      (variant_allocs, invariant_allocs) =
        M.partition variantAlloc $ kbody_allocs <> mconcat ops_allocs
      badVariant (_, Var v, _) = not $ v `nameIn` bound_in_kernel
      badVariant _ = False

  case find badVariant $ M.elems variant_allocs of
    Just v ->
      throwError $
        "Cannot handle un-sliceable allocation size: " ++ pretty v
          ++ "\nLikely cause: irregular nested operations inside parallel constructs."
    Nothing ->
      return ()

  case lvl of
    SegGroup {}
      | not $ null variant_allocs ->
        throwError "Cannot handle invariant allocations in SegGroup."
    _ ->
      return ()

  allocsForBody variant_allocs invariant_allocs lvl space kbody' $ \alloc_stms kbody'' -> do
    ops'' <- forM ops' $ \op' ->
      localScope (scopeOf op') $ offsetMemoryInLambda op'
    return (alloc_stms, (ops'', kbody''))
  where
    bound_in_kernel =
      namesFromList (M.keys $ scopeOfSegSpace space)
        <> boundInKernelBody kbody

boundInKernelBody :: KernelBody GPUMem -> Names
boundInKernelBody = namesFromList . M.keys . scopeOf . kernelBodyStms

allocsForBody ::
  Extraction ->
  Extraction ->
  SegLevel ->
  SegSpace ->
  KernelBody GPUMem ->
  (Stms GPUMem -> KernelBody GPUMem -> OffsetM b) ->
  ExpandM b
allocsForBody variant_allocs invariant_allocs lvl space kbody' m = do
  (alloc_offsets, alloc_stms) <-
    memoryRequirements
      lvl
      space
      (kernelBodyStms kbody')
      variant_allocs
      invariant_allocs

  scope <- askScope
  let scope' = scopeOfSegSpace space <> scope
  either throwError pure $
    runOffsetM scope' alloc_offsets $ do
      kbody'' <- offsetMemoryInKernelBody kbody'
      m alloc_stms kbody''

memoryRequirements ::
  SegLevel ->
  SegSpace ->
  Stms GPUMem ->
  Extraction ->
  Extraction ->
  ExpandM (RebaseMap, Stms GPUMem)
memoryRequirements lvl space kstms variant_allocs invariant_allocs = do
  (num_threads, num_threads_stms) <-
    runBuilder . letSubExp "num_threads" . BasicOp $
      BinOp
        (Mul Int64 OverflowUndef)
        (unCount $ segNumGroups lvl)
        (unCount $ segGroupSize lvl)

  (invariant_alloc_stms, invariant_alloc_offsets) <-
    inScopeOf num_threads_stms $
      expandedInvariantAllocations
        num_threads
        (segNumGroups lvl)
        (segGroupSize lvl)
        invariant_allocs

  (variant_alloc_stms, variant_alloc_offsets) <-
    inScopeOf num_threads_stms $
      expandedVariantAllocations
        num_threads
        space
        kstms
        variant_allocs

  return
    ( invariant_alloc_offsets <> variant_alloc_offsets,
      num_threads_stms <> invariant_alloc_stms <> variant_alloc_stms
    )

-- | Identifying the spot where an allocation occurs in terms of its
-- level and unique thread ID.
type User = (SegLevel, [TPrimExp Int64 VName])

-- | A description of allocations that have been extracted, and how
-- much memory (and which space) is needed.
type Extraction = M.Map VName (User, SubExp, Space)

extractKernelBodyAllocations ::
  User ->
  Names ->
  Names ->
  KernelBody GPUMem ->
  ( KernelBody GPUMem,
    Extraction
  )
extractKernelBodyAllocations lvl bound_outside bound_kernel =
  extractGenericBodyAllocations lvl bound_outside bound_kernel kernelBodyStms $
    \stms kbody -> kbody {kernelBodyStms = stms}

extractBodyAllocations ::
  User ->
  Names ->
  Names ->
  Body GPUMem ->
  (Body GPUMem, Extraction)
extractBodyAllocations user bound_outside bound_kernel =
  extractGenericBodyAllocations user bound_outside bound_kernel bodyStms $
    \stms body -> body {bodyStms = stms}

extractLambdaAllocations ::
  User ->
  Names ->
  Names ->
  Lambda GPUMem ->
  (Lambda GPUMem, Extraction)
extractLambdaAllocations user bound_outside bound_kernel lam = (lam {lambdaBody = body'}, allocs)
  where
    (body', allocs) = extractBodyAllocations user bound_outside bound_kernel $ lambdaBody lam

extractGenericBodyAllocations ::
  User ->
  Names ->
  Names ->
  (body -> Stms GPUMem) ->
  (Stms GPUMem -> body -> body) ->
  body ->
  ( body,
    Extraction
  )
extractGenericBodyAllocations user bound_outside bound_kernel get_stms set_stms body =
  let bound_kernel' = bound_kernel <> boundByStms (get_stms body)
      (stms, allocs) =
        runWriter $
          fmap catMaybes $
            mapM (extractStmAllocations user bound_outside bound_kernel') $
              stmsToList $ get_stms body
   in (set_stms (stmsFromList stms) body, allocs)

expandable, notScalar :: Space -> Bool
expandable (Space "local") = False
expandable ScalarSpace {} = False
expandable _ = True
notScalar ScalarSpace {} = False
notScalar _ = True

extractStmAllocations ::
  User ->
  Names ->
  Names ->
  Stm GPUMem ->
  Writer Extraction (Maybe (Stm GPUMem))
extractStmAllocations user bound_outside bound_kernel (Let (Pattern [] [patElem]) _ (Op (Alloc size space)))
  | expandable space && expandableSize size
      -- FIXME: the '&& notScalar space' part is a hack because we
      -- don't otherwise hoist the sizes out far enough, and we
      -- promise to be super-duper-careful about not having variant
      -- scalar allocations.
      || (boundInKernel size && notScalar space) = do
    tell $ M.singleton (patElemName patElem) (user, size, space)
    return Nothing
  where
    expandableSize (Var v) = v `nameIn` bound_outside || v `nameIn` bound_kernel
    expandableSize Constant {} = True
    boundInKernel (Var v) = v `nameIn` bound_kernel
    boundInKernel Constant {} = False
extractStmAllocations user bound_outside bound_kernel stm = do
  e <- mapExpM (expMapper user) $ stmExp stm
  return $ Just $ stm {stmExp = e}
  where
    expMapper user' =
      identityMapper
        { mapOnBody = const $ onBody user',
          mapOnOp = onOp user'
        }

    onBody user' body = do
      let (body', allocs) = extractBodyAllocations user' bound_outside bound_kernel body
      tell allocs
      return body'

    onOp (_, user_ids) (Inner (SegOp op)) =
      Inner . SegOp <$> mapSegOpM (opMapper user'') op
      where
        user'' =
          (segLevel op, user_ids ++ [le64 (segFlat (segSpace op))])
    onOp _ op = return op

    opMapper user' =
      identitySegOpMapper
        { mapOnSegOpLambda = onLambda user',
          mapOnSegOpBody = onKernelBody user'
        }

    onKernelBody user' body = do
      let (body', allocs) = extractKernelBodyAllocations user' bound_outside bound_kernel body
      tell allocs
      return body'

    onLambda user' lam = do
      body <- onBody user' $ lambdaBody lam
      return lam {lambdaBody = body}

genericExpandedInvariantAllocations ::
  (User -> (Shape, [TPrimExp Int64 VName])) -> Extraction -> ExpandM (Stms GPUMem, RebaseMap)
genericExpandedInvariantAllocations getNumUsers invariant_allocs = do
  -- We expand the invariant allocations by adding an inner dimension
  -- equal to the number of kernel threads.
  (rebases, alloc_stms) <- runBuilder $ mapM expand $ M.toList invariant_allocs

  return (alloc_stms, mconcat rebases)
  where
    expand (mem, (user, per_thread_size, space)) = do
      let num_users = fst $ getNumUsers user
          allocpat = Pattern [] [PatElem mem $ MemMem space]
      total_size <-
        letExp "total_size" <=< toExp . product $
          pe64 per_thread_size : map pe64 (shapeDims num_users)
      letBind allocpat $ Op $ Alloc (Var total_size) space
      pure $ M.singleton mem $ newBase user

    untouched d = DimSlice 0 d 1

    newBase user@(SegThread {}, _) (old_shape, _) =
      let (users_shape, user_ids) = getNumUsers user
          num_dims = length old_shape
          perm = [num_dims .. num_dims + shapeRank users_shape -1] ++ [0 .. num_dims -1]
          root_ixfun = IxFun.iota (old_shape ++ map pe64 (shapeDims users_shape))
          permuted_ixfun = IxFun.permute root_ixfun perm
          offset_ixfun =
            IxFun.slice permuted_ixfun $
              map DimFix user_ids ++ map untouched old_shape
       in offset_ixfun
    newBase user@(SegGroup {}, _) (old_shape, _) =
      let (users_shape, user_ids) = getNumUsers user
          root_ixfun = IxFun.iota $ map pe64 (shapeDims users_shape) ++ old_shape
          offset_ixfun =
            IxFun.slice root_ixfun $
              map DimFix user_ids ++ map untouched old_shape
       in offset_ixfun

expandedInvariantAllocations ::
  SubExp ->
  Count NumGroups SubExp ->
  Count GroupSize SubExp ->
  Extraction ->
  ExpandM (Stms GPUMem, RebaseMap)
expandedInvariantAllocations num_threads (Count num_groups) (Count group_size) =
  genericExpandedInvariantAllocations getNumUsers
  where
    getNumUsers (SegThread {}, [gtid]) = (Shape [num_threads], [gtid])
    getNumUsers (SegThread {}, [gid, ltid]) = (Shape [num_groups, group_size], [gid, ltid])
    getNumUsers (SegGroup {}, [gid]) = (Shape [num_groups], [gid])
    getNumUsers user = error $ "getNumUsers: unhandled " ++ show user

expandedVariantAllocations ::
  SubExp ->
  SegSpace ->
  Stms GPUMem ->
  Extraction ->
  ExpandM (Stms GPUMem, RebaseMap)
expandedVariantAllocations _ _ _ variant_allocs
  | null variant_allocs = return (mempty, mempty)
expandedVariantAllocations num_threads kspace kstms variant_allocs = do
  let sizes_to_blocks = removeCommonSizes variant_allocs
      variant_sizes = map fst sizes_to_blocks

  (slice_stms, offsets, size_sums) <-
    sliceKernelSizes num_threads variant_sizes kspace kstms
  -- Note the recursive call to expand allocations inside the newly
  -- produced kernels.
  (_, slice_stms_tmp) <-
    simplifyStms =<< explicitAllocationsInStms slice_stms
  slice_stms' <- transformStms slice_stms_tmp

  let variant_allocs' :: [(VName, (SubExp, SubExp, Space))]
      variant_allocs' =
        concat $
          zipWith
            memInfo
            (map snd sizes_to_blocks)
            (zip offsets size_sums)
      memInfo blocks (offset, total_size) =
        [(mem, (Var offset, Var total_size, space)) | (mem, space) <- blocks]

  -- We expand the invariant allocations by adding an inner dimension
  -- equal to the sum of the sizes required by different threads.
  (alloc_bnds, rebases) <- unzip <$> mapM expand variant_allocs'

  return (slice_stms' <> stmsFromList alloc_bnds, mconcat rebases)
  where
    expand (mem, (offset, total_size, space)) = do
      let allocpat = Pattern [] [PatElem mem $ MemMem space]
      return
        ( Let allocpat (defAux ()) $ Op $ Alloc total_size space,
          M.singleton mem $ newBase offset
        )

    num_threads' = pe64 num_threads
    gtid = le64 $ segFlat kspace

    -- For the variant allocations, we add an inner dimension,
    -- which is then offset by a thread-specific amount.
    newBase size_per_thread (old_shape, pt) =
      let elems_per_thread =
            pe64 size_per_thread `quot` primByteSize pt
          root_ixfun = IxFun.iota [elems_per_thread, num_threads']
          offset_ixfun =
            IxFun.slice
              root_ixfun
              [ DimSlice 0 num_threads' 1,
                DimFix gtid
              ]
          shapechange =
            if length old_shape == 1
              then map DimCoercion old_shape
              else map DimNew old_shape
       in IxFun.reshape offset_ixfun shapechange

-- | A map from memory block names to new index function bases.
type RebaseMap = M.Map VName (([TPrimExp Int64 VName], PrimType) -> IxFun)

newtype OffsetM a
  = OffsetM
      ( ReaderT
          (Scope GPUMem)
          (ReaderT RebaseMap (Either String))
          a
      )
  deriving
    ( Applicative,
      Functor,
      Monad,
      HasScope GPUMem,
      LocalScope GPUMem,
      MonadError String
    )

runOffsetM :: Scope GPUMem -> RebaseMap -> OffsetM a -> Either String a
runOffsetM scope offsets (OffsetM m) =
  runReaderT (runReaderT m scope) offsets

askRebaseMap :: OffsetM RebaseMap
askRebaseMap = OffsetM $ lift ask

lookupNewBase :: VName -> ([TPrimExp Int64 VName], PrimType) -> OffsetM (Maybe IxFun)
lookupNewBase name x = do
  offsets <- askRebaseMap
  return $ ($ x) <$> M.lookup name offsets

offsetMemoryInKernelBody :: KernelBody GPUMem -> OffsetM (KernelBody GPUMem)
offsetMemoryInKernelBody kbody = do
  scope <- askScope
  stms' <-
    stmsFromList . snd
      <$> mapAccumLM
        (\scope' -> localScope scope' . offsetMemoryInStm)
        scope
        (stmsToList $ kernelBodyStms kbody)
  return kbody {kernelBodyStms = stms'}

offsetMemoryInBody :: Body GPUMem -> OffsetM (Body GPUMem)
offsetMemoryInBody (Body dec stms res) = do
  scope <- askScope
  stms' <-
    stmsFromList . snd
      <$> mapAccumLM
        (\scope' -> localScope scope' . offsetMemoryInStm)
        scope
        (stmsToList stms)
  return $ Body dec stms' res

offsetMemoryInStm :: Stm GPUMem -> OffsetM (Scope GPUMem, Stm GPUMem)
offsetMemoryInStm (Let pat dec e) = do
  pat' <- offsetMemoryInPattern pat
  e' <- localScope (scopeOfPattern pat') $ offsetMemoryInExp e
  scope <- askScope
  -- Try to recompute the index function.  Fall back to creating rebase
  -- operations with the RebaseMap.
  rts <- runReaderT (expReturns e') scope
  let pat'' =
        Pattern
          (patternContextElements pat')
          (zipWith pick (patternValueElements pat') rts)
      stm = Let pat'' dec e'
  let scope' = scopeOf stm <> scope
  return (scope', stm)
  where
    pick ::
      PatElemT (MemInfo SubExp NoUniqueness MemBind) ->
      ExpReturns ->
      PatElemT (MemInfo SubExp NoUniqueness MemBind)
    pick
      (PatElem name (MemArray pt s u _ret))
      (MemArray _ _ _ (Just (ReturnsInBlock m extixfun)))
        | Just ixfun <- instantiateIxFun extixfun =
          PatElem name (MemArray pt s u (ArrayIn m ixfun))
    pick p _ = p

    instantiateIxFun :: ExtIxFun -> Maybe IxFun
    instantiateIxFun = traverse (traverse inst)
      where
        inst Ext {} = Nothing
        inst (Free x) = return x

offsetMemoryInPattern :: Pattern GPUMem -> OffsetM (Pattern GPUMem)
offsetMemoryInPattern (Pattern ctx vals) = do
  mapM_ inspectCtx ctx
  Pattern ctx <$> mapM inspectVal vals
  where
    inspectVal patElem = do
      new_dec <- offsetMemoryInMemBound $ patElemDec patElem
      return patElem {patElemDec = new_dec}
    inspectCtx patElem
      | Mem space <- patElemType patElem,
        expandable space =
        throwError $
          unwords
            [ "Cannot deal with existential memory block",
              pretty (patElemName patElem),
              "when expanding inside kernels."
            ]
      | otherwise = return ()

offsetMemoryInParam :: Param (MemBound u) -> OffsetM (Param (MemBound u))
offsetMemoryInParam fparam = do
  fparam' <- offsetMemoryInMemBound $ paramDec fparam
  return fparam {paramDec = fparam'}

offsetMemoryInMemBound :: MemBound u -> OffsetM (MemBound u)
offsetMemoryInMemBound summary@(MemArray pt shape u (ArrayIn mem ixfun)) = do
  new_base <- lookupNewBase mem (IxFun.base ixfun, pt)
  return $
    fromMaybe summary $ do
      new_base' <- new_base
      return $ MemArray pt shape u $ ArrayIn mem $ IxFun.rebase new_base' ixfun
offsetMemoryInMemBound summary = return summary

offsetMemoryInBodyReturns :: BodyReturns -> OffsetM BodyReturns
offsetMemoryInBodyReturns br@(MemArray pt shape u (ReturnsInBlock mem ixfun))
  | Just ixfun' <- isStaticIxFun ixfun = do
    new_base <- lookupNewBase mem (IxFun.base ixfun', pt)
    return $
      fromMaybe br $ do
        new_base' <- new_base
        return $
          MemArray pt shape u $
            ReturnsInBlock mem $
              IxFun.rebase (fmap (fmap Free) new_base') ixfun
offsetMemoryInBodyReturns br = return br

offsetMemoryInLambda :: Lambda GPUMem -> OffsetM (Lambda GPUMem)
offsetMemoryInLambda lam = inScopeOf lam $ do
  body <- offsetMemoryInBody $ lambdaBody lam
  return $ lam {lambdaBody = body}

offsetMemoryInExp :: Exp GPUMem -> OffsetM (Exp GPUMem)
offsetMemoryInExp (DoLoop ctx val form body) = do
  let (ctxparams, ctxinit) = unzip ctx
      (valparams, valinit) = unzip val
  ctxparams' <- mapM offsetMemoryInParam ctxparams
  valparams' <- mapM offsetMemoryInParam valparams
  body' <- localScope (scopeOfFParams ctxparams' <> scopeOfFParams valparams' <> scopeOf form) (offsetMemoryInBody body)
  return $ DoLoop (zip ctxparams' ctxinit) (zip valparams' valinit) form body'
offsetMemoryInExp e = mapExpM recurse e
  where
    recurse =
      identityMapper
        { mapOnBody = \bscope -> localScope bscope . offsetMemoryInBody,
          mapOnBranchType = offsetMemoryInBodyReturns,
          mapOnOp = onOp
        }
    onOp (Inner (SegOp op)) =
      Inner . SegOp
        <$> localScope (scopeOfSegSpace (segSpace op)) (mapSegOpM segOpMapper op)
      where
        segOpMapper =
          identitySegOpMapper
            { mapOnSegOpBody = offsetMemoryInKernelBody,
              mapOnSegOpLambda = offsetMemoryInLambda
            }
    onOp op = return op

---- Slicing allocation sizes out of a kernel.

unAllocGPUStms :: Stms GPUMem -> Either String (Stms GPU.GPU)
unAllocGPUStms = unAllocStms False
  where
    unAllocBody (Body dec stms res) =
      Body dec <$> unAllocStms True stms <*> pure res

    unAllocKernelBody (KernelBody dec stms res) =
      KernelBody dec <$> unAllocStms True stms <*> pure res

    unAllocStms nested =
      fmap (stmsFromList . catMaybes) . mapM (unAllocStm nested) . stmsToList

    unAllocStm nested stm@(Let _ _ (Op Alloc {}))
      | nested = throwError $ "Cannot handle nested allocation: " ++ pretty stm
      | otherwise = return Nothing
    unAllocStm _ (Let pat dec e) =
      Just <$> (Let <$> unAllocPattern pat <*> pure dec <*> mapExpM unAlloc' e)

    unAllocLambda (Lambda params body ret) =
      Lambda (unParams params) <$> unAllocBody body <*> pure ret

    unParams = mapMaybe $ traverse unMem

    unAllocPattern pat@(Pattern ctx val) =
      Pattern <$> maybe bad return (mapM (rephrasePatElem unMem) ctx)
        <*> maybe bad return (mapM (rephrasePatElem unMem) val)
      where
        bad = Left $ "Cannot handle memory in pattern " ++ pretty pat

    unAllocOp Alloc {} = Left "unAllocOp: unhandled Alloc"
    unAllocOp (Inner OtherOp {}) = Left "unAllocOp: unhandled OtherOp"
    unAllocOp (Inner (SizeOp op)) =
      return $ SizeOp op
    unAllocOp (Inner (SegOp op)) = SegOp <$> mapSegOpM mapper op
      where
        mapper =
          identitySegOpMapper
            { mapOnSegOpLambda = unAllocLambda,
              mapOnSegOpBody = unAllocKernelBody
            }

    unParam p = maybe bad return $ traverse unMem p
      where
        bad = Left $ "Cannot handle memory-typed parameter '" ++ pretty p ++ "'"

    unT t = maybe bad return $ unMem t
      where
        bad = Left $ "Cannot handle memory type '" ++ pretty t ++ "'"

    unAlloc' =
      Mapper
        { mapOnBody = const unAllocBody,
          mapOnRetType = unT,
          mapOnBranchType = unT,
          mapOnFParam = unParam,
          mapOnLParam = unParam,
          mapOnOp = unAllocOp,
          mapOnSubExp = Right,
          mapOnVName = Right
        }

unMem :: MemInfo d u ret -> Maybe (TypeBase (ShapeBase d) u)
unMem (MemPrim pt) = Just $ Prim pt
unMem (MemArray pt shape u _) = Just $ Array pt shape u
unMem (MemAcc acc ispace ts u) = Just $ Acc acc ispace ts u
unMem MemMem {} = Nothing

unAllocScope :: Scope GPUMem -> Scope GPU.GPU
unAllocScope = M.mapMaybe unInfo
  where
    unInfo (LetName dec) = LetName <$> unMem dec
    unInfo (FParamName dec) = FParamName <$> unMem dec
    unInfo (LParamName dec) = LParamName <$> unMem dec
    unInfo (IndexName it) = Just $ IndexName it

removeCommonSizes ::
  Extraction ->
  [(SubExp, [(VName, Space)])]
removeCommonSizes = M.toList . foldl' comb mempty . M.toList
  where
    comb m (mem, (_, size, space)) = M.insertWith (++) size [(mem, space)] m

sliceKernelSizes ::
  SubExp ->
  [SubExp] ->
  SegSpace ->
  Stms GPUMem ->
  ExpandM (Stms GPU.GPU, [VName], [VName])
sliceKernelSizes num_threads sizes space kstms = do
  kstms' <- either throwError return $ unAllocGPUStms kstms
  let num_sizes = length sizes
      i64s = replicate num_sizes $ Prim int64

  kernels_scope <- asks unAllocScope

  (max_lam, _) <- flip runBuilderT kernels_scope $ do
    xs <- replicateM num_sizes $ newParam "x" (Prim int64)
    ys <- replicateM num_sizes $ newParam "y" (Prim int64)
    (zs, stms) <- localScope (scopeOfLParams $ xs ++ ys) $
      collectStms $
        forM (zip xs ys) $ \(x, y) ->
          letSubExp "z" $ BasicOp $ BinOp (SMax Int64) (Var $ paramName x) (Var $ paramName y)
    return $ Lambda (xs ++ ys) (mkBody stms zs) i64s

  flat_gtid_lparam <- Param <$> newVName "flat_gtid" <*> pure (Prim (IntType Int64))

  (size_lam', _) <- flip runBuilderT kernels_scope $ do
    params <- replicateM num_sizes $ newParam "x" (Prim int64)
    (zs, stms) <- localScope
      ( scopeOfLParams params
          <> scopeOfLParams [flat_gtid_lparam]
      )
      $ collectStms $ do
        -- Even though this SegRed is one-dimensional, we need to
        -- provide indexes corresponding to the original potentially
        -- multi-dimensional construct.
        let (kspace_gtids, kspace_dims) = unzip $ unSegSpace space
            new_inds =
              unflattenIndex
                (map pe64 kspace_dims)
                (pe64 $ Var $ paramName flat_gtid_lparam)
        zipWithM_ letBindNames (map pure kspace_gtids) =<< mapM toExp new_inds

        mapM_ addStm kstms'
        return sizes

    localScope (scopeOfSegSpace space) $
      GPU.simplifyLambda (Lambda [flat_gtid_lparam] (Body () stms zs) i64s)

  ((maxes_per_thread, size_sums), slice_stms) <- flip runBuilderT kernels_scope $ do
    pat <-
      basicPattern []
        <$> replicateM
          num_sizes
          (newIdent "max_per_thread" $ Prim int64)

    w <-
      letSubExp "size_slice_w"
        =<< foldBinOp (Mul Int64 OverflowUndef) (intConst Int64 1) (segSpaceDims space)

    thread_space_iota <-
      letExp "thread_space_iota" $
        BasicOp $
          Iota w (intConst Int64 0) (intConst Int64 1) Int64
    let red_op =
          SegBinOp
            Commutative
            max_lam
            (replicate num_sizes $ intConst Int64 0)
            mempty
    lvl <- segThread "segred"

    addStms =<< mapM renameStm
      =<< nonSegRed lvl pat w [red_op] size_lam' [thread_space_iota]

    size_sums <- forM (patternNames pat) $ \threads_max ->
      letExp "size_sum" $
        BasicOp $ BinOp (Mul Int64 OverflowUndef) (Var threads_max) num_threads

    return (patternNames pat, size_sums)

  return (slice_stms, maxes_per_thread, size_sums)
