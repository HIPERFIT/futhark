{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
-- | Extract kernels.
-- In the following, I will use the term "width" to denote the amount
-- of immediate parallelism in a map - that is, the row size of the
-- array(s) being used as input.
--
-- = Basic Idea
--
-- If we have:
--
-- @
--   map
--     map(f)
--     bnds_a...
--     map(g)
-- @
--
-- Then we want to distribute to:
--
-- @
--   map
--     map(f)
--   map
--     bnds_a
--   map
--     map(g)
-- @
--
-- But for now only if
--
--  (0) it can be done without creating irregular arrays.
--      Specifically, the size of the arrays created by @map(f)@, by
--      @map(g)@ and whatever is created by @bnds_a@ that is also used
--      in @map(g)@, must be invariant to the outermost loop.
--
--  (1) the maps are _balanced_.  That is, the functions @f@ and @g@
--      must do the same amount of work for every iteration.
--
-- The advantage is that the map-nests containing @map(f)@ and
-- @map(g)@ can now be trivially flattened at no cost, thus exposing
-- more parallelism.  Note that the @bnds_a@ map constitutes array
-- expansion, which requires additional storage.
--
-- = Distributing Sequential Loops
--
-- As a starting point, sequential loops are treated like scalar
-- expressions.  That is, not distributed.  However, sometimes it can
-- be worthwhile to distribute if they contain a map:
--
-- @
--   map
--     loop
--       map
--     map
-- @
--
-- If we distribute the loop and interchange the outer map into the
-- loop, we get this:
--
-- @
--   loop
--     map
--       map
--   map
--     map
-- @
--
-- Now more parallelism may be available.
--
-- = Unbalanced Maps
--
-- Unbalanced maps will as a rule be sequentialised, but sometimes,
-- there is another way.  Assume we find this:
--
-- @
--   map
--     map(f)
--       map(g)
--     map
-- @
--
-- Presume that @map(f)@ is unbalanced.  By the simple rule above, we
-- would then fully sequentialise it, resulting in this:
--
-- @
--   map
--     loop
--   map
--     map
-- @
--
-- == Balancing by Loop Interchange
--
-- This is not ideal, as we cannot flatten the @map-loop@ nest, and we
-- are thus limited in the amount of parallelism available.
--
-- But assume now that the width of @map(g)@ is invariant to the outer
-- loop.  Then if possible, we can interchange @map(f)@ and @map(g)@,
-- sequentialise @map(f)@ and distribute, interchanging the outer
-- parallel loop into the sequential loop:
--
-- @
--   loop(f)
--     map
--       map(g)
--   map
--     map
-- @
--
-- After flattening the two nests we can obtain more parallelism.
--
-- When distributing a map, we also need to distribute everything that
-- the map depends on - possibly as its own map.  When distributing a
-- set of scalar bindings, we will need to know which of the binding
-- results are used afterwards.  Hence, we will need to compute usage
-- information.
--
-- = Redomap
--
-- Redomap is handled much like map.  Distributed loops are
-- distributed as maps, with the parameters corresponding to the
-- neutral elements added to their bodies.  The remaining loop will
-- remain a redomap.  Example:
--
-- @
-- redomap(op,
--         fn (acc,v) =>
--           map(f)
--           map(g),
--         e,a)
-- @
--
-- distributes to
--
-- @
-- let b = map(fn v =>
--               let acc = e
--               map(f),
--               a)
-- redomap(op,
--         fn (acc,v,dist) =>
--           map(g),
--         e,a,b)
-- @
--
module Futhark.Pass.ExtractKernels
       (extractKernels)
       where

import Control.Arrow (second)
import Control.Applicative
import Control.Monad.RWS.Strict
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe
import Data.List

import Prelude

import Futhark.Optimise.Simplifier.Simple (bindableSimpleOps)
import Futhark.Representation.Basic
import Futhark.MonadFreshNames
import Futhark.Tools
import qualified Futhark.Transform.FirstOrderTransform as FOT
import Futhark.Pass
import Futhark.Transform.CopyPropagate
import Futhark.Pass.ExtractKernels.Distribution
import Futhark.Pass.ExtractKernels.ISRWIM
import Futhark.Pass.ExtractKernels.BlockedReduction
import Futhark.Util.Log
import Futhark.Transform.Rename

extractKernels :: Pass Basic Basic
extractKernels =
  Pass { passName = "extract kernels"
       , passDescription = "Perform kernel extraction"
       , passFunction = runDistribM . liftM Prog . mapM transformFunDec . progFunctions
       }

newtype DistribM a = DistribM (RWS TypeEnv Log VNameSource a)
                   deriving (Functor, Applicative, Monad,
                             HasTypeEnv,
                             LocalTypeEnv,
                             MonadFreshNames,
                             MonadLogger)

runDistribM :: (MonadLogger m, MonadFreshNames m) =>
               DistribM a -> m a
runDistribM (DistribM m) = do
  (x, msgs) <- modifyNameSource $ positionNameSource . runRWS m HM.empty
  addLog msgs
  return x
  where positionNameSource (x, src, msgs) = ((x, msgs), src)

transformFunDec :: FunDec -> DistribM FunDec
transformFunDec fundec = do
  body' <- localTypeEnv (typeEnvFromParams $ funDecParams fundec) $
           transformBody $ funDecBody fundec
  return fundec { funDecBody = body' }

transformBody :: Body -> DistribM Body
transformBody body = do bnds <- transformBindings $ bodyBindings body
                        return body { bodyBindings = bnds }

transformBindings :: [Binding] -> DistribM [Binding]
transformBindings [] =
  return []
transformBindings (bnd:bnds) =
  sequentialisedUnbalancedBinding bnd >>= \case
    Nothing -> do
      bnd' <- transformBinding bnd
      localTypeEnv (typeEnvFromBindings bnd') $
        (bnd'++) <$> transformBindings bnds
    Just bnds' ->
      transformBindings $ bnds' <> bnds

sequentialisedUnbalancedBinding :: Binding -> DistribM (Maybe [Binding])
sequentialisedUnbalancedBinding bnd@(Let _ _ (LoopOp (Map _ _ lam _)))
  | unbalancedLambda lam =
    Just <$> runBinder_ (FOT.transformBinding bnd)
sequentialisedUnbalancedBinding bnd@(Let _ _ (LoopOp (Redomap _ _ lam1 lam2 _ _)))
  | unbalancedLambda lam1 || unbalancedLambda lam2 =
    Just <$> runBinder_ (FOT.transformBinding bnd)
sequentialisedUnbalancedBinding _ =
  return Nothing

transformBinding :: Binding -> DistribM [Binding]

transformBinding (Let pat () (If c tb fb rt)) = do
  tb' <- transformBody tb
  fb' <- transformBody fb
  return [Let pat () $ If c tb' fb' rt]

transformBinding (Let pat () (LoopOp (DoLoop res mergepat form body))) =
  localTypeEnv (boundInForm form $ typeEnvFromParams mergeparams) $ do
    body' <- transformBody body
    return [Let pat () $ LoopOp $ DoLoop res mergepat form body']
  where boundInForm (ForLoop i _) = HM.insert i (Basic Int)
        boundInForm (WhileLoop _) = id
        mergeparams = map fst mergepat

transformBinding (Let pat () (LoopOp (Map cs w lam arrs))) =
  distributeMap pat $ MapLoop cs w lam arrs

transformBinding (Let pat () (LoopOp (Redomap cs w lam1 lam2 nes arrs))) = do
  lam1_sequential <- FOT.transformLambda lam1
  lam2_sequential <- FOT.transformLambda lam2
  blockedReduction pat cs w lam1_sequential lam2_sequential nes arrs

transformBinding (Let pat () (LoopOp (Reduce cs w red_fun red_input))) = do
  red_fun_sequential <- FOT.transformLambda red_fun
  red_fun_sequential' <- renameLambda red_fun_sequential
  blockedReduction pat cs w red_fun_sequential' red_fun_sequential nes arrs
  where (nes, arrs) = unzip red_input

transformBinding (Let pat () (LoopOp (Stream cs w form lam arrs c))) =
  localTypeEnv (typeEnvFromParams $ extLambdaParams lam) $ do
    body' <- transformBody $ extLambdaBody lam
    let lam' = lam { extLambdaBody = body' }
    return [Let pat () $ LoopOp $ Stream cs w form lam' arrs c]

transformBinding (Let res_pat () (LoopOp op))
  | Scan cs w scan_fun scan_input <- op,
    Just do_iswim <- iswim res_pat cs w scan_fun scan_input =
      transformBindings =<< runBinder_ do_iswim

transformBinding bnd = do
  e' <- mapExpM transform $ bindingExp bnd
  return [bnd { bindingExp = e' }]
  where transform = identityMapper { mapOnLambda = transformLambda }

transformLambda :: Lambda -> DistribM Lambda
transformLambda lam =
  localTypeEnv (typeEnvFromParams $ lambdaParams lam) $
  localTypeEnv (HM.singleton (lambdaIndex lam) $ Basic Int ) $ do
    body' <- transformBody $ lambdaBody lam
    return lam { lambdaBody = body' }

data MapLoop = MapLoop Certificates SubExp Lambda [VName]

mapLoopExp :: MapLoop -> Exp
mapLoopExp (MapLoop cs w lam arrs) = LoopOp $ Map cs w lam arrs

distributeMap :: (HasTypeEnv m, MonadFreshNames m, MonadLogger m) =>
                 Pattern -> MapLoop -> m [Binding]
distributeMap pat (MapLoop cs w lam arrs) = do
  types <- askTypeEnv
  let env = KernelEnv { kernelNest =
                        singleNesting (Nesting mempty $
                                       MapNesting pat cs w (lambdaIndex lam) $
                                       zip (lambdaParams lam) arrs)
                      , kernelTypeEnv =
                        types <> typeEnvFromParams (lambdaParams lam)
                      }
  liftM (postKernelBindings . snd) $ runKernelM env $
    distribute =<< distributeMapBodyBindings acc (bodyBindings $ lambdaBody lam)
    where acc = KernelAcc { kernelTargets = singleTarget (pat, bodyResult $ lambdaBody lam)
                          , kernelBindings = mempty
                          }

data KernelEnv = KernelEnv { kernelNest :: Nestings
                           , kernelTypeEnv :: TypeEnv
                           }

data KernelAcc = KernelAcc { kernelTargets :: Targets
                           , kernelBindings :: [Binding]
                           }

data KernelRes = KernelRes { accPostKernels :: PostKernels
                           , accLog :: Log
                           }

instance Monoid KernelRes where
  KernelRes ks1 log1 `mappend` KernelRes ks2 log2 =
    KernelRes (ks1 <> ks2) (log1 <> log2)
  mempty = KernelRes mempty mempty

newtype PostKernels = PostKernels [[Binding]]

instance Monoid PostKernels where
  mempty = PostKernels mempty
  PostKernels xs `mappend` PostKernels ys = PostKernels $ ys ++ xs

postKernelBindings :: PostKernels -> [Binding]
postKernelBindings (PostKernels kernels) = concat kernels

addBindingToKernel :: (HasTypeEnv m, MonadFreshNames m) =>
                      Binding -> KernelAcc -> m KernelAcc
addBindingToKernel bnd acc = do
  bnds <- runBinder_ $ FOT.transformBindingRecursively bnd
  return acc { kernelBindings = bnds <> kernelBindings acc }

newtype KernelM a = KernelM (RWS KernelEnv KernelRes VNameSource a)
  deriving (Functor, Applicative, Monad,
            MonadReader KernelEnv,
            MonadWriter KernelRes,
            MonadFreshNames)

instance HasTypeEnv KernelM where
  askTypeEnv = asks kernelTypeEnv

instance MonadLogger KernelM where
  addLog msgs = tell mempty { accLog = msgs }

runKernelM :: (HasTypeEnv m, MonadFreshNames m, MonadLogger m) =>
              KernelEnv -> KernelM a -> m (a, PostKernels)
runKernelM env (KernelM m) = do
  (x, res) <- modifyNameSource $ getKernels . runRWS m env
  addLog $ accLog res
  return (x, accPostKernels res)
  where getKernels (x,s,a) = ((x, a), s)

addKernels :: PostKernels -> KernelM ()
addKernels ks = tell $ mempty { accPostKernels = ks }

addKernel :: [Binding] -> KernelM ()
addKernel bnds = addKernels $ PostKernels [bnds]

withBinding :: Binding -> KernelM a -> KernelM a
withBinding bnd = local $ \env ->
  env { kernelTypeEnv =
          kernelTypeEnv env <> typeEnvFromBindings [bnd]
      , kernelNest =
        letBindInInnerNesting provided $
        kernelNest env
      }
  where provided = HS.fromList $ patternNames $ bindingPattern bnd

mapNesting :: Pattern -> Certificates -> SubExp -> Lambda -> [VName]
           -> KernelM a
           -> KernelM a
mapNesting pat cs w lam arrs = local $ \env ->
  env { kernelNest = pushInnerNesting nest $ kernelNest env
      , kernelTypeEnv = kernelTypeEnv env <>
                        typeEnvFromParams (lambdaParams lam)
      }
  where nest = Nesting mempty $
               MapNesting pat cs w (lambdaIndex lam) $
               zip (lambdaParams lam) arrs

unbalancedLambda :: Lambda -> Bool
unbalancedLambda lam =
  unbalancedBody
  (HS.fromList $ map paramName $ lambdaParams lam) $
  lambdaBody lam

  where subExpBound (Var i) bound = i `HS.member` bound
        subExpBound (Constant _) _ = False

        unbalancedBody bound body =
          any (unbalancedBinding (bound <> boundInBody body) . bindingExp) $
          bodyBindings body

        -- XXX - our notion of balancing is probably still too naive.
        unbalancedBinding bound (LoopOp (Map _ w _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (LoopOp (Reduce _ w _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (LoopOp (Scan _ w _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (LoopOp (Redomap _ w _ _ _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (LoopOp (ConcatMap _ w _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (LoopOp (Stream _ w _ _ _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (LoopOp (Kernel _ w _ _ _ _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (LoopOp (ReduceKernel _ w _ _ _ _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (LoopOp (DoLoop _ merge (ForLoop i iterations) body)) =
          iterations `subExpBound` bound ||
          unbalancedBody bound' body
          where bound' = foldr HS.insert bound $
                         i : map (paramName . fst) merge
        unbalancedBinding _ (LoopOp (DoLoop _ _ (WhileLoop _) _)) =
          True

        unbalancedBinding bound (If _ tbranch fbranch _) =
          unbalancedBody bound tbranch || unbalancedBody bound fbranch

        unbalancedBinding bound (SegOp (SegReduce _ w _ _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (SegOp (SegScan _ w _ _ _ _)) =
          w `subExpBound` bound
        unbalancedBinding bound (SegOp (SegReplicate _ w _ _)) =
          w `HS.member` bound

        unbalancedBinding _ (PrimOp _) =
          False
        unbalancedBinding _ (Apply fname _ _) =
          not $ isBuiltInFunction fname

distributeInnerMap :: Pattern -> MapLoop -> KernelAcc
                   -> KernelM KernelAcc
distributeInnerMap pat maploop@(MapLoop cs w lam arrs) acc
  | unbalancedLambda lam =
      addBindingToKernel (Let pat () $ mapLoopExp maploop) acc
  | otherwise =
      distribute =<<
      leavingNesting maploop =<<
      mapNesting pat cs w lam arrs
      (distribute =<< distributeMapBodyBindings acc' (bodyBindings $ lambdaBody lam))
      where acc' = KernelAcc { kernelTargets = pushInnerTarget
                                               (pat, bodyResult $ lambdaBody lam) $
                                               kernelTargets acc
                             , kernelBindings = mempty
                             }

leavingNesting :: MapLoop -> KernelAcc -> KernelM KernelAcc
leavingNesting (MapLoop cs w lam arrs) acc =
  case second reverse $ kernelTargets acc of
   (_, []) ->
     fail "The kernel targets list is unexpectedly small"
   ((pat,res), x:xs) -> do
     let acc' = acc { kernelTargets = (x, reverse xs) }
     case kernelBindings acc' of
       []      -> return acc'
       remnant ->
         let body = mkBody remnant res
             used_in_body = freeInBody body
             (used_params, used_arrs) =
               unzip $
               filter ((`HS.member` used_in_body) . paramName . fst) $
               zip (lambdaParams lam) arrs
             lam' = Lambda { lambdaBody = body
                           , lambdaReturnType = map rowType $ patternTypes pat
                           , lambdaParams = used_params
                           , lambdaIndex = lambdaIndex lam
                           }
         in addBindingToKernel (Let pat () $ LoopOp $ Map cs w lam' used_arrs)
            acc' { kernelBindings = [] }

distributeMapBodyBindings :: KernelAcc -> [Binding] -> KernelM KernelAcc

distributeMapBodyBindings acc [] =
  return acc

distributeMapBodyBindings acc
  (Let pat () (LoopOp (Stream cs w (Sequential accs) lam arrs _)):bnds) = do
  let (body_bnds,res) = sequentialStreamWholeArray w accs lam arrs
      reshapeRes t (Var v)
        | null (arrayDims t) = PrimOp $ SubExp $ Var v
        | otherwise          = shapeCoerce cs (arrayDims t) v
      reshapeRes _ se      = PrimOp $ SubExp se
      res_bnds = [ mkLet' [] [ident] $ reshapeRes (identType ident) se
                 | (ident,se) <- zip (patternIdents pat) res ]
  stream_bnds <- copyPropagateInBindings bindableSimpleOps $
                 body_bnds ++ res_bnds
  distributeMapBodyBindings acc $ stream_bnds ++ bnds

distributeMapBodyBindings acc
  (Let pat () (LoopOp (Redomap cs w lam1 lam2 nes arrs)):bnds) = do
    (mapbnd, redbnd) <- redomapToMapAndReduce pat () (cs, w, lam1, lam2, nes, arrs)
    distributeMapBodyBindings acc $ mapbnd : redbnd : bnds

distributeMapBodyBindings acc (bnd:bnds) =
  -- It is important that bnd is in scope if 'maybeDistributeBinding'
  -- wants to distribute, even if this causes the slightly silly
  -- situation that bnd is in scope of itself.
  withBinding bnd $
  maybeDistributeBinding bnd =<<
  distributeMapBodyBindings acc bnds

maybeDistributeBinding :: Binding -> KernelAcc
                       -> KernelM KernelAcc
maybeDistributeBinding bnd@(Let pat _ (LoopOp (Map cs w lam arrs))) acc =
  -- Only distribute inside the map if we can distribute everything
  -- following the map.
  distributeIfPossible acc >>= \case
    Nothing -> addBindingToKernel bnd acc
    Just acc' -> distribute =<< distributeInnerMap pat (MapLoop cs w lam arrs) acc'

maybeDistributeBinding bnd@(Let pat _ (LoopOp (DoLoop ret merge form body))) acc
  | any (isMap . bindingExp) $ bodyBindings body =
  distributeSingleBinding acc bnd >>= \case
    Just (kernels, res, nest, acc')
      | length res == patternSize pat -> do
      addKernels kernels
      addKernel =<<
        interchangeLoops nest (SeqLoop pat ret merge form body)
      return acc'
    _ ->
      addBindingToKernel bnd acc
  where isMap (LoopOp (Map {})) = True
        isMap _                 = False

-- We keep reduce and scan in the program if they can be distributed
-- by themselves, as this means they can be turned into segmented
-- parallel operations.  We currently sequentialise their lambda
-- bodies.  This may lose us some parallelism as it is possible there
-- may have been maps in there that we could interchange out via
-- transposition.
--
-- If the reduce or scan cannot be distributed by itself, it will be
-- sequentialised in the default case for this function.
maybeDistributeBinding bnd@(Let _ _ (LoopOp op)) acc
  | Just (lam, call_with_new_lam) <- reduceOrScan op =
      distributeSingleBinding acc bnd >>= \case
        Just (kernels, res, nest, acc') -> do
          addKernels kernels
          lam' <- FOT.transformLambda lam
          (w_bnds, kern_bnd) <-
            constructKernel nest $
            mkBody [bnd { bindingExp = call_with_new_lam lam' }] res
          kern_bnd' <- runBinder_ $ FOT.transformBindingRecursively kern_bnd
          addKernel $ w_bnds++kern_bnd'
          return acc'
        _ ->
          addBindingToKernel bnd acc

  where reduceOrScan (Scan cs w lam input) =
          Just (lam, \lam' -> LoopOp $ Scan cs w lam' input)
        reduceOrScan (Reduce cs w lam input) =
          Just (lam, \lam' -> LoopOp $ Reduce cs w lam' input)
        reduceOrScan _ =
           Nothing

maybeDistributeBinding bnd@(Let _ _ (PrimOp (Copy {}))) acc = do
  acc' <- distribute acc
  distribute =<< addBindingToKernel bnd acc'

maybeDistributeBinding bnd@(Let _ _ (PrimOp (Rearrange {}))) acc = do
  acc' <- distribute acc
  distribute =<< addBindingToKernel bnd acc'

maybeDistributeBinding bnd@(Let _ _ (PrimOp (Reshape {}))) acc = do
  acc' <- distribute acc
  distribute =<< addBindingToKernel bnd acc'

maybeDistributeBinding bnd acc =
  addBindingToKernel bnd acc

distribute :: KernelAcc -> KernelM KernelAcc
distribute acc =
  fromMaybe acc <$> distributeIfPossible acc

distributeIfPossible :: KernelAcc -> KernelM (Maybe KernelAcc)
distributeIfPossible acc = do
  nest <- asks kernelNest
  tryDistribute nest (kernelTargets acc) (kernelBindings acc) >>= \case
    Nothing -> return Nothing
    Just (targets, kernel) -> do
      addKernel kernel
      return $ Just KernelAcc { kernelTargets = targets
                              , kernelBindings = []
                              }

distributeSingleBinding :: KernelAcc -> Binding
                        -> KernelM (Maybe (PostKernels, Result, KernelNest, KernelAcc))
distributeSingleBinding acc bnd = do
  nest <- asks kernelNest
  tryDistribute nest (kernelTargets acc) (kernelBindings acc) >>= \case
    Nothing -> return Nothing
    Just (targets, distributed_bnds) ->
      tryDistributeBinding nest targets bnd >>= \case
        Nothing -> return Nothing
        Just (res, targets', new_kernel_nest) ->
          return $ Just (PostKernels [distributed_bnds],
                         res,
                         new_kernel_nest,
                         KernelAcc { kernelTargets = targets'
                                   , kernelBindings = []
                                   })
