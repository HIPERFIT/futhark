{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A generic transformation for adding memory allocations to a
-- Futhark program.  Specialised by specific representations in
-- submodules.
module Futhark.Pass.ExplicitAllocations
  ( explicitAllocationsGeneric,
    explicitAllocationsInStmsGeneric,
    ExpHint (..),
    defaultExpHints,
    Allocable,
    Allocator (..),
    AllocM,
    AllocEnv (..),
    SizeSubst (..),
    allocInStms,
    allocForArray,
    simplifiable,
    arraySizeInBytesExp,
    mkLetNamesB',
    mkLetNamesB'',

    -- * Module re-exports

    --
    -- These are highly likely to be needed by any downstream
    -- users.
    module Control.Monad.Reader,
    module Futhark.MonadFreshNames,
    module Futhark.Pass,
    module Futhark.Tools,
  )
where

import Control.Monad.RWS.Strict
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List (foldl', partition, zip4)
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Set as S
import qualified Futhark.Analysis.UsageTable as UT
import Futhark.IR.Mem
import qualified Futhark.IR.Mem.IxFun as IxFun
import Futhark.MonadFreshNames
import Futhark.Optimise.Simplify.Engine (SimpleOps (..))
import qualified Futhark.Optimise.Simplify.Engine as Engine
import Futhark.Optimise.Simplify.Rep (mkWiseBody)
import Futhark.Pass
import Futhark.Tools
import Futhark.Util (maybeNth, splitAt3, splitFromEnd, takeLast)

data AllocStm
  = SizeComputation VName (PrimExp VName)
  | Allocation VName SubExp Space
  | ArrayCopy VName VName
  deriving (Eq, Ord, Show)

bindAllocStm ::
  (MonadBuilder m, Op (Rep m) ~ MemOp inner) =>
  AllocStm ->
  m ()
bindAllocStm (SizeComputation name pe) =
  letBindNames [name] =<< toExp (coerceIntPrimExp Int64 pe)
bindAllocStm (Allocation name size space) =
  letBindNames [name] $ Op $ Alloc size space
bindAllocStm (ArrayCopy name src) =
  letBindNames [name] $ BasicOp $ Copy src

class
  (MonadFreshNames m, LocalScope rep m, Mem rep) =>
  Allocator rep m
  where
  addAllocStm :: AllocStm -> m ()
  askDefaultSpace :: m Space

  default addAllocStm ::
    ( Allocable fromrep rep,
      m ~ AllocM fromrep rep
    ) =>
    AllocStm ->
    m ()
  addAllocStm (SizeComputation name se) =
    letBindNames [name] =<< toExp (coerceIntPrimExp Int64 se)
  addAllocStm (Allocation name size space) =
    letBindNames [name] $ Op $ allocOp size space
  addAllocStm (ArrayCopy name src) =
    letBindNames [name] $ BasicOp $ Copy src

  -- | The subexpression giving the number of elements we should
  -- allocate space for.  See 'ChunkMap' comment.
  dimAllocationSize :: SubExp -> m SubExp
  default dimAllocationSize ::
    m ~ AllocM fromrep rep =>
    SubExp ->
    m SubExp
  dimAllocationSize (Var v) =
    -- It is important to recurse here, as the substitution may itself
    -- be a chunk size.
    maybe (return $ Var v) dimAllocationSize =<< asks (M.lookup v . chunkMap)
  dimAllocationSize size =
    return size

  -- | Get those names that are known to be constants at run-time.
  askConsts :: m (S.Set VName)

  expHints :: Exp rep -> m [ExpHint]
  expHints = defaultExpHints

allocateMemory ::
  Allocator rep m =>
  String ->
  SubExp ->
  Space ->
  m VName
allocateMemory desc size space = do
  v <- newVName desc
  addAllocStm $ Allocation v size space
  return v

computeSize ::
  Allocator rep m =>
  String ->
  PrimExp VName ->
  m SubExp
computeSize desc se = do
  v <- newVName desc
  addAllocStm $ SizeComputation v se
  return $ Var v

type Allocable fromrep torep =
  ( PrettyRep fromrep,
    PrettyRep torep,
    Mem torep,
    FParamInfo fromrep ~ DeclType,
    LParamInfo fromrep ~ Type,
    BranchType fromrep ~ ExtType,
    RetType fromrep ~ DeclExtType,
    BodyDec fromrep ~ (),
    BodyDec torep ~ (),
    ExpDec torep ~ (),
    SizeSubst (Op torep),
    BuilderOps torep
  )

-- | A mapping from chunk names to their maximum size.  XXX FIXME
-- HACK: This is part of a hack to add loop-invariant allocations to
-- reduce kernels, because memory expansion does not use range
-- analysis yet (it should).
type ChunkMap = M.Map VName SubExp

data AllocEnv fromrep torep = AllocEnv
  { chunkMap :: ChunkMap,
    -- | Aggressively try to reuse memory in do-loops -
    -- should be True inside kernels, False outside.
    aggressiveReuse :: Bool,
    -- | When allocating memory, put it in this memory space.
    -- This is primarily used to ensure that group-wide
    -- statements store their results in local memory.
    allocSpace :: Space,
    -- | The set of names that are known to be constants at
    -- kernel compile time.
    envConsts :: S.Set VName,
    allocInOp :: Op fromrep -> AllocM fromrep torep (Op torep),
    envExpHints :: Exp torep -> AllocM fromrep torep [ExpHint]
  }

-- | Monad for adding allocations to an entire program.
newtype AllocM fromrep torep a
  = AllocM (BuilderT torep (ReaderT (AllocEnv fromrep torep) (State VNameSource)) a)
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadFreshNames,
      HasScope torep,
      LocalScope torep,
      MonadReader (AllocEnv fromrep torep)
    )

instance
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  MonadBuilder (AllocM fromrep torep)
  where
  type Rep (AllocM fromrep torep) = torep

  mkExpDecM _ _ = return ()

  mkLetNamesM names e = do
    pat <- patWithAllocations names e
    return $ Let pat (defAux ()) e

  mkBodyM bnds res = return $ Body () bnds res

  addStms = AllocM . addStms
  collectStms (AllocM m) = AllocM $ collectStms m

instance
  (Allocable fromrep torep) =>
  Allocator torep (AllocM fromrep torep)
  where
  expHints e = do
    f <- asks envExpHints
    f e
  askDefaultSpace = asks allocSpace

  askConsts = asks envConsts

runAllocM ::
  MonadFreshNames m =>
  (Op fromrep -> AllocM fromrep torep (Op torep)) ->
  (Exp torep -> AllocM fromrep torep [ExpHint]) ->
  AllocM fromrep torep a ->
  m a
runAllocM handleOp hints (AllocM m) =
  fmap fst $ modifyNameSource $ runState $ runReaderT (runBuilderT m mempty) env
  where
    env =
      AllocEnv
        { chunkMap = mempty,
          aggressiveReuse = False,
          allocSpace = DefaultSpace,
          envConsts = mempty,
          allocInOp = handleOp,
          envExpHints = hints
        }

-- | Monad for adding allocations to a single pattern.
newtype PatAllocM rep a
  = PatAllocM
      ( RWS
          (Scope rep)
          [AllocStm]
          VNameSource
          a
      )
  deriving
    ( Applicative,
      Functor,
      Monad,
      HasScope rep,
      LocalScope rep,
      MonadWriter [AllocStm],
      MonadFreshNames
    )

instance Mem rep => Allocator rep (PatAllocM rep) where
  addAllocStm = tell . pure
  dimAllocationSize = return
  askDefaultSpace = return DefaultSpace
  askConsts = pure mempty

runPatAllocM ::
  MonadFreshNames m =>
  PatAllocM rep a ->
  Scope rep ->
  m (a, [AllocStm])
runPatAllocM (PatAllocM m) mems =
  modifyNameSource $ frob . runRWS m mems
  where
    frob (a, s, w) = ((a, w), s)

elemSize :: Num a => Type -> a
elemSize = primByteSize . elemType

arraySizeInBytesExp :: Type -> PrimExp VName
arraySizeInBytesExp t =
  untyped $ foldl' (*) (elemSize t) $ map pe64 (arrayDims t)

arraySizeInBytesExpM :: Allocator rep m => Type -> m (PrimExp VName)
arraySizeInBytesExpM t = do
  dims <- mapM dimAllocationSize (arrayDims t)
  let dim_prod_i64 = product $ map pe64 dims
      elm_size_i64 = elemSize t
  return $
    BinOpExp (SMax Int64) (ValueExp $ IntValue $ Int64Value 0) $
      untyped $
        dim_prod_i64 * elm_size_i64

arraySizeInBytes :: Allocator rep m => Type -> m SubExp
arraySizeInBytes = computeSize "bytes" <=< arraySizeInBytesExpM

-- | Allocate memory for a value of the given type.
allocForArray ::
  Allocator rep m =>
  Type ->
  Space ->
  m VName
allocForArray t space = do
  size <- arraySizeInBytes t
  allocateMemory "mem" size space

allocsForStm ::
  (Allocator rep m, ExpDec rep ~ ()) => [Ident] -> Exp rep -> m (Stm rep)
allocsForStm idents e = do
  rts <- expReturns e
  hints <- expHints e
  pes <- allocsForPat idents rts hints
  return $ Let (Pat pes) (defAux ()) e

patWithAllocations ::
  (Allocator rep m, ExpDec rep ~ ()) =>
  [VName] ->
  Exp rep ->
  m (Pat rep)
patWithAllocations names e = do
  ts' <- instantiateShapes' names <$> expExtType e
  stmPat <$> allocsForStm (zipWith Ident names ts') e

mkMissingIdents :: MonadFreshNames m => [Ident] -> [ExpReturns] -> m [Ident]
mkMissingIdents idents rts =
  reverse <$> zipWithM f (reverse rts) (map Just (reverse idents) ++ repeat Nothing)
  where
    f _ (Just ident) = pure ident
    f (MemMem space) Nothing = newIdent "ext_mem" $ Mem space
    f _ Nothing = newIdent "ext" $ Prim int64

allocsForPat ::
  Allocator rep m => [Ident] -> [ExpReturns] -> [ExpHint] -> m [PatElem rep]
allocsForPat some_idents rts hints = do
  idents <- mkMissingIdents some_idents rts

  forM (zip3 idents rts hints) $ \(ident, rt, hint) -> do
    let ident_shape = arrayShape $ identType ident
    case rt of
      MemPrim _ -> do
        summary <- summaryForBindage (identType ident) hint
        pure $ PatElem (identName ident) summary
      MemMem space ->
        pure $ PatElem (identName ident) $ MemMem space
      MemArray bt _ u (Just (ReturnsInBlock mem extixfun)) -> do
        let ixfn = instantiateExtIxFun idents extixfun
        pure . PatElem (identName ident) . MemArray bt ident_shape u $ ArrayIn mem ixfn
      MemArray _ extshape _ Nothing
        | Just _ <- knownShape extshape -> do
          summary <- summaryForBindage (identType ident) hint
          pure $ PatElem (identName ident) summary
      MemArray bt _ u (Just (ReturnsNewBlock _ i extixfn)) -> do
        let ixfn = instantiateExtIxFun idents extixfn
        pure . PatElem (identName ident) . MemArray bt ident_shape u $
          ArrayIn (getIdent idents i) ixfn
      MemAcc acc ispace ts u ->
        pure $ PatElem (identName ident) $ MemAcc acc ispace ts u
      _ -> error "Impossible case reached in allocsForPat!"
  where
    knownShape = mapM known . shapeDims
    known (Free v) = Just v
    known Ext {} = Nothing

    getIdent idents i =
      case maybeNth i idents of
        Just ident -> identName ident
        Nothing ->
          error $ "getIdent: Ext " <> show i <> " but pattern has " <> show (length idents) <> " elements: " <> pretty idents

    instantiateExtIxFun idents = fmap $ fmap inst
      where
        inst (Free v) = v
        inst (Ext i) = getIdent idents i

instantiateIxFun :: Monad m => ExtIxFun -> m IxFun
instantiateIxFun = traverse $ traverse inst
  where
    inst Ext {} = error "instantiateIxFun: not yet"
    inst (Free x) = return x

summaryForBindage ::
  Allocator rep m =>
  Type ->
  ExpHint ->
  m (MemBound NoUniqueness)
summaryForBindage (Prim bt) _ =
  return $ MemPrim bt
summaryForBindage (Mem space) _ =
  return $ MemMem space
summaryForBindage (Acc acc ispace ts u) _ =
  return $ MemAcc acc ispace ts u
summaryForBindage t@(Array pt shape u) NoHint = do
  m <- allocForArray t =<< askDefaultSpace
  return $ directIxFun pt shape u m t
summaryForBindage t@(Array pt _ _) (Hint ixfun space) = do
  bytes <-
    computeSize "bytes" $
      untyped $
        product
          [ product $ IxFun.base ixfun,
            fromIntegral (primByteSize pt :: Int64)
          ]
  m <- allocateMemory "mem" bytes space
  return $ MemArray pt (arrayShape t) NoUniqueness $ ArrayIn m ixfun

lookupMemSpace :: (HasScope rep m, Monad m) => VName -> m Space
lookupMemSpace v = do
  t <- lookupType v
  case t of
    Mem space -> return space
    _ -> error $ "lookupMemSpace: " ++ pretty v ++ " is not a memory block."

directIxFun :: PrimType -> Shape -> u -> VName -> Type -> MemBound u
directIxFun bt shape u mem t =
  let ixf = IxFun.iota $ map pe64 $ arrayDims t
   in MemArray bt shape u $ ArrayIn mem ixf

allocInFParams ::
  (Allocable fromrep torep) =>
  [(FParam fromrep, Space)] ->
  ([FParam torep] -> AllocM fromrep torep a) ->
  AllocM fromrep torep a
allocInFParams params m = do
  (valparams, (ctxparams, memparams)) <-
    runWriterT $ mapM (uncurry allocInFParam) params
  let params' = ctxparams <> memparams <> valparams
      summary = scopeOfFParams params'
  localScope summary $ m params'

allocInFParam ::
  (Allocable fromrep torep) =>
  FParam fromrep ->
  Space ->
  WriterT
    ([FParam torep], [FParam torep])
    (AllocM fromrep torep)
    (FParam torep)
allocInFParam param pspace =
  case paramDeclType param of
    Array pt shape u -> do
      let memname = baseString (paramName param) <> "_mem"
          ixfun = IxFun.iota $ map pe64 $ shapeDims shape
      mem <- lift $ newVName memname
      tell ([], [Param mem $ MemMem pspace])
      return param {paramDec = MemArray pt shape u $ ArrayIn mem ixfun}
    Prim pt ->
      return param {paramDec = MemPrim pt}
    Mem space ->
      return param {paramDec = MemMem space}
    Acc acc ispace ts u ->
      return param {paramDec = MemAcc acc ispace ts u}

allocInMergeParams ::
  ( Allocable fromrep torep,
    Allocator torep (AllocM fromrep torep)
  ) =>
  [(FParam fromrep, SubExp)] ->
  ( [FParam torep] ->
    [FParam torep] ->
    ([SubExp] -> AllocM fromrep torep ([SubExp], [SubExp])) ->
    AllocM fromrep torep a
  ) ->
  AllocM fromrep torep a
allocInMergeParams merge m = do
  ((valparams, handle_loop_subexps), (ctx_params, mem_params)) <-
    runWriterT $ unzip <$> mapM allocInMergeParam merge
  let mergeparams' = ctx_params <> mem_params <> valparams
      summary = scopeOfFParams mergeparams'

      mk_loop_res ses = do
        (valargs, (ctxargs, memargs)) <-
          runWriterT $ zipWithM ($) handle_loop_subexps ses
        return (ctxargs <> memargs, valargs)

  localScope summary $ m (ctx_params <> mem_params) valparams mk_loop_res
  where
    allocInMergeParam ::
      (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
      (Param DeclType, SubExp) ->
      WriterT
        ([FParam torep], [FParam torep])
        (AllocM fromrep torep)
        (FParam torep, SubExp -> WriterT ([SubExp], [SubExp]) (AllocM fromrep torep) SubExp)
    allocInMergeParam (mergeparam, Var v)
      | Array pt shape u <- paramDeclType mergeparam = do
        (mem', _) <- lift $ lookupArraySummary v
        mem_space <- lift $ lookupMemSpace mem'

        (_, ext_ixfun, substs, _) <- lift $ existentializeArray mem_space v

        (ctx_params, param_ixfun_substs) <-
          unzip
            <$> mapM
              ( \e -> do
                  let e_t = primExpType $ untyped e
                  vname <- lift $ newVName "ctx_param_ext"
                  return
                    ( Param vname $ MemPrim e_t,
                      fmap Free $ pe64 $ Var vname
                    )
              )
              substs

        tell (ctx_params, [])

        param_ixfun <-
          instantiateIxFun $
            IxFun.substituteInIxFun
              (M.fromList $ zip (fmap Ext [0 ..]) param_ixfun_substs)
              ext_ixfun

        mem_name <- newVName "mem_param"
        tell ([], [Param mem_name $ MemMem mem_space])

        return
          ( mergeparam {paramDec = MemArray pt shape u $ ArrayIn mem_name param_ixfun},
            ensureArrayIn mem_space
          )
    allocInMergeParam (mergeparam, _) = doDefault mergeparam =<< lift askDefaultSpace

    doDefault mergeparam space = do
      mergeparam' <- allocInFParam mergeparam space
      return (mergeparam', linearFuncallArg (paramType mergeparam) space)

-- Returns the existentialized index function, the list of substituted values and the memory location.
existentializeArray ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  Space ->
  VName ->
  AllocM fromrep torep (SubExp, ExtIxFun, [TPrimExp Int64 VName], VName)
existentializeArray ScalarSpace {} v = do
  (mem', ixfun) <- lookupArraySummary v
  return (Var v, fmap (fmap Free) ixfun, mempty, mem')
existentializeArray space v = do
  (mem', ixfun) <- lookupArraySummary v
  sp <- lookupMemSpace mem'

  let (ext_ixfun', substs') = runState (IxFun.existentialize ixfun) []

  case (ext_ixfun', sp == space) of
    (Just x, True) -> return (Var v, x, substs', mem')
    _ -> do
      (mem, subexp) <- allocLinearArray space (baseString v) v
      ixfun' <- fromJust <$> subExpIxFun subexp
      let (ext_ixfun, substs) = runState (IxFun.existentialize ixfun') []
      return (subexp, fromJust ext_ixfun, substs, mem)

ensureArrayIn ::
  ( Allocable fromrep torep,
    Allocator torep (AllocM fromrep torep)
  ) =>
  Space ->
  SubExp ->
  WriterT ([SubExp], [SubExp]) (AllocM fromrep torep) SubExp
ensureArrayIn _ (Constant v) =
  error $ "ensureArrayIn: " ++ pretty v ++ " cannot be an array."
ensureArrayIn space (Var v) = do
  (sub_exp, _, substs, mem) <- lift $ existentializeArray space v
  (ctx_vals, _) <-
    unzip
      <$> mapM
        ( \s -> do
            vname <- lift $ letExp "ctx_val" =<< toExp s
            return (Var vname, fmap Free $ primExpFromSubExp int64 $ Var vname)
        )
        substs

  tell (ctx_vals, [Var mem])

  return sub_exp

ensureDirectArray ::
  ( Allocable fromrep torep,
    Allocator torep (AllocM fromrep torep)
  ) =>
  Maybe Space ->
  VName ->
  AllocM fromrep torep (VName, SubExp)
ensureDirectArray space_ok v = do
  (mem, ixfun) <- lookupArraySummary v
  mem_space <- lookupMemSpace mem
  default_space <- askDefaultSpace
  if IxFun.isDirect ixfun && maybe True (== mem_space) space_ok
    then return (mem, Var v)
    else needCopy (fromMaybe default_space space_ok)
  where
    needCopy space =
      -- We need to do a new allocation, copy 'v', and make a new
      -- binding for the size of the memory block.
      allocLinearArray space (baseString v) v

allocLinearArray ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  Space ->
  String ->
  VName ->
  AllocM fromrep torep (VName, SubExp)
allocLinearArray space s v = do
  t <- lookupType v
  case t of
    Array pt shape u -> do
      mem <- allocForArray t space
      v' <- newIdent (s ++ "_linear") t
      let ixfun = directIxFun pt shape u mem t
          pat = Pat [PatElem (identName v') ixfun]
      addStm $ Let pat (defAux ()) $ BasicOp $ Copy v
      return (mem, Var $ identName v')
    _ ->
      error $ "allocLinearArray: " ++ pretty t

funcallArgs ::
  ( Allocable fromrep torep,
    Allocator torep (AllocM fromrep torep)
  ) =>
  [(SubExp, Diet)] ->
  AllocM fromrep torep [(SubExp, Diet)]
funcallArgs args = do
  (valargs, (ctx_args, mem_and_size_args)) <- runWriterT $
    forM args $ \(arg, d) -> do
      t <- lift $ subExpType arg
      space <- lift askDefaultSpace
      arg' <- linearFuncallArg t space arg
      return (arg', d)
  return $ map (,Observe) (ctx_args <> mem_and_size_args) <> valargs

linearFuncallArg ::
  ( Allocable fromrep torep,
    Allocator torep (AllocM fromrep torep)
  ) =>
  Type ->
  Space ->
  SubExp ->
  WriterT ([SubExp], [SubExp]) (AllocM fromrep torep) SubExp
linearFuncallArg Array {} space (Var v) = do
  (mem, arg') <- lift $ ensureDirectArray (Just space) v
  tell ([], [Var mem])
  return arg'
linearFuncallArg _ _ arg =
  return arg

explicitAllocationsGeneric ::
  ( Allocable fromrep torep,
    Allocator torep (AllocM fromrep torep)
  ) =>
  (Op fromrep -> AllocM fromrep torep (Op torep)) ->
  (Exp torep -> AllocM fromrep torep [ExpHint]) ->
  Pass fromrep torep
explicitAllocationsGeneric handleOp hints =
  Pass "explicit allocations" "Transform program to explicit memory representation" $
    intraproceduralTransformationWithConsts onStms allocInFun
  where
    onStms stms =
      runAllocM handleOp hints $ collectStms_ $ allocInStms stms $ pure ()

    allocInFun consts (FunDef entry attrs fname rettype params fbody) =
      runAllocM handleOp hints . inScopeOf consts $
        allocInFParams (zip params $ repeat DefaultSpace) $ \params' -> do
          (fbody', mem_rets) <-
            allocInFunBody (map (const $ Just DefaultSpace) rettype) fbody
          let rettype' = mem_rets ++ memoryInDeclExtType (length mem_rets) rettype
          return $ FunDef entry attrs fname rettype' params' fbody'

explicitAllocationsInStmsGeneric ::
  ( MonadFreshNames m,
    HasScope torep m,
    Allocable fromrep torep
  ) =>
  (Op fromrep -> AllocM fromrep torep (Op torep)) ->
  (Exp torep -> AllocM fromrep torep [ExpHint]) ->
  Stms fromrep ->
  m (Stms torep)
explicitAllocationsInStmsGeneric handleOp hints stms = do
  scope <- askScope
  runAllocM handleOp hints $
    localScope scope $ collectStms_ $ allocInStms stms $ pure ()

memoryInDeclExtType :: Int -> [DeclExtType] -> [FunReturns]
memoryInDeclExtType k dets = evalState (mapM addMem dets) 0
  where
    addMem (Prim t) = return $ MemPrim t
    addMem Mem {} = error "memoryInDeclExtType: too much memory"
    addMem (Array pt shape u) = do
      i <- get <* modify (+ 1)
      let shape' = fmap shift shape
      return . MemArray pt shape' u . ReturnsNewBlock DefaultSpace i $
        IxFun.iota $ map convert $ shapeDims shape'
    addMem (Acc acc ispace ts u) = return $ MemAcc acc ispace ts u

    convert (Ext i) = le64 $ Ext i
    convert (Free v) = Free <$> pe64 v

    shift (Ext i) = Ext (i + k)
    shift (Free x) = Free x

bodyReturnMemCtx ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  SubExpRes ->
  AllocM fromrep torep [(SubExpRes, MemInfo ExtSize u MemReturn)]
bodyReturnMemCtx (SubExpRes _ Constant {}) =
  return []
bodyReturnMemCtx (SubExpRes _ (Var v)) = do
  info <- lookupMemInfo v
  case info of
    MemPrim {} -> return []
    MemAcc {} -> return []
    MemMem {} -> return [] -- should not happen
    MemArray _ _ _ (ArrayIn mem _) -> do
      mem_info <- lookupMemInfo mem
      case mem_info of
        MemMem space ->
          pure [(subExpRes $ Var mem, MemMem space)]
        _ -> error $ "bodyReturnMemCtx: not a memory block: " ++ pretty mem

allocInFunBody ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  [Maybe Space] ->
  Body fromrep ->
  AllocM fromrep torep (Body torep, [FunReturns])
allocInFunBody space_oks (Body _ bnds res) =
  buildBody . allocInStms bnds $ do
    res' <- zipWithM ensureDirect space_oks' res
    (mem_ctx_res, mem_ctx_rets) <- unzip . concat <$> mapM bodyReturnMemCtx res'
    pure (mem_ctx_res <> res', mem_ctx_rets)
  where
    num_vals = length space_oks
    space_oks' = replicate (length res - num_vals) Nothing ++ space_oks

ensureDirect ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  Maybe Space ->
  SubExpRes ->
  AllocM fromrep torep SubExpRes
ensureDirect space_ok (SubExpRes cs se) = do
  se_info <- subExpMemInfo se
  SubExpRes cs <$> case (se_info, se) of
    (MemArray {}, Var v) -> do
      (_, v') <- ensureDirectArray space_ok v
      pure v'
    _ ->
      pure se

allocInStms ::
  (Allocable fromrep torep) =>
  Stms fromrep ->
  AllocM fromrep torep a ->
  AllocM fromrep torep a
allocInStms origstms m = allocInStms' $ stmsToList origstms
  where
    allocInStms' [] = m
    allocInStms' (stm : stms) = do
      allocstms <- collectStms_ $ auxing (stmAux stm) $ allocInStm stm
      addStms allocstms
      let stms_substs = foldMap sizeSubst allocstms
          stms_consts = foldMap stmConsts allocstms
          f env =
            env
              { chunkMap = stms_substs <> chunkMap env,
                envConsts = stms_consts <> envConsts env
              }
      local f $ allocInStms' stms

allocInStm ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  Stm fromrep ->
  AllocM fromrep torep ()
allocInStm (Let (Pat pes) _ e) = do
  e' <- allocInExp e
  let idents = map patElemIdent pes
  stm <- allocsForStm idents e'
  addStm stm

allocInLambda ::
  Allocable fromrep torep =>
  [LParam torep] ->
  Body fromrep ->
  AllocM fromrep torep (Lambda torep)
allocInLambda params body =
  mkLambda params . allocInStms (bodyStms body) $
    pure $ bodyResult body

allocInExp ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  Exp fromrep ->
  AllocM fromrep torep (Exp torep)
allocInExp (DoLoop merge form (Body () bodybnds bodyres)) =
  allocInMergeParams merge $ \new_ctx_params params' mk_loop_val -> do
    form' <- allocInLoopForm form
    localScope (scopeOf form') $ do
      (valinit_ctx, args') <- mk_loop_val args
      body' <-
        buildBody_ . allocInStms bodybnds $ do
          (val_ses, valres') <- mk_loop_val $ map resSubExp bodyres
          pure $ subExpsRes val_ses <> zipWith SubExpRes (map resCerts bodyres) valres'
      return $
        DoLoop (zip (new_ctx_params ++ params') (valinit_ctx ++ args')) form' body'
  where
    (_params, args) = unzip merge
allocInExp (Apply fname args rettype loc) = do
  args' <- funcallArgs args
  -- We assume that every array is going to be in its own memory.
  return $ Apply fname args' (mems ++ memoryInDeclExtType 0 rettype) loc
  where
    mems = replicate num_arrays (MemMem DefaultSpace)
    num_arrays = length $ filter ((> 0) . arrayRank . declExtTypeOf) rettype
allocInExp (If cond tbranch0 fbranch0 (IfDec rets ifsort)) = do
  let num_rets = length rets
  -- switch to the explicit-mem rep, but do nothing about results
  (tbranch, tm_ixfs) <- allocInIfBody num_rets tbranch0
  (fbranch, fm_ixfs) <- allocInIfBody num_rets fbranch0
  tspaces <- mkSpaceOks num_rets tbranch
  fspaces <- mkSpaceOks num_rets fbranch
  -- try to generalize (antiunify) the index functions of the then and else bodies
  let sp_substs = zipWith generalize (zip tspaces tm_ixfs) (zip fspaces fm_ixfs)
      (spaces, subs) = unzip sp_substs
      tsubs = map (selectSub fst) subs
      fsubs = map (selectSub snd) subs
  (tbranch', trets) <- addResCtxInIfBody rets tbranch spaces tsubs
  (fbranch', frets) <- addResCtxInIfBody rets fbranch spaces fsubs
  if frets /= trets
    then error "In allocInExp, IF case: antiunification of then/else produce different ExtInFn!"
    else do
      -- above is a sanity check; implementation continues on else branch
      let res_then = bodyResult tbranch'
          res_else = bodyResult fbranch'
          size_ext = length res_then - length trets
          (ind_ses0, r_then_else) =
            partition (\(r_then, r_else, _) -> r_then == r_else) $
              zip3 res_then res_else [0 .. size_ext - 1]
          (r_then_ext, r_else_ext, _) = unzip3 r_then_else
          ind_ses =
            zipWith
              (\(se, _, i) k -> (i - k, se))
              ind_ses0
              [0 .. length ind_ses0 - 1]
          rets'' = foldl (\acc (i, SubExpRes _ se) -> fixExt i se acc) trets ind_ses
          tbranch'' = tbranch' {bodyResult = r_then_ext ++ drop size_ext res_then}
          fbranch'' = fbranch' {bodyResult = r_else_ext ++ drop size_ext res_else}
          res_if_expr = If cond tbranch'' fbranch'' $ IfDec rets'' ifsort
      return res_if_expr
  where
    generalize ::
      (Maybe Space, Maybe IxFun) ->
      (Maybe Space, Maybe IxFun) ->
      (Maybe Space, Maybe (ExtIxFun, [(TPrimExp Int64 VName, TPrimExp Int64 VName)]))
    generalize (Just sp1, Just ixf1) (Just sp2, Just ixf2) =
      if sp1 /= sp2
        then (Just sp1, Nothing)
        else case IxFun.leastGeneralGeneralization (fmap untyped ixf1) (fmap untyped ixf2) of
          Just (ixf, m) ->
            ( Just sp1,
              Just
                ( fmap TPrimExp ixf,
                  zip (map (TPrimExp . fst) m) (map (TPrimExp . snd) m)
                )
            )
          Nothing -> (Just sp1, Nothing)
    generalize (mbsp1, _) _ = (mbsp1, Nothing)

    selectSub ::
      ((a, a) -> a) ->
      Maybe (ExtIxFun, [(a, a)]) ->
      Maybe (ExtIxFun, [a])
    selectSub f (Just (ixfn, m)) = Just (ixfn, map f m)
    selectSub _ Nothing = Nothing
    allocInIfBody ::
      (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
      Int ->
      Body fromrep ->
      AllocM fromrep torep (Body torep, [Maybe IxFun])
    allocInIfBody num_vals (Body _ bnds res) =
      buildBody . allocInStms bnds $ do
        let (_, val_res) = splitFromEnd num_vals res
        mem_ixfs <- mapM (subExpIxFun . resSubExp) val_res
        pure (res, mem_ixfs)
allocInExp (WithAcc inputs bodylam) =
  WithAcc <$> mapM onInput inputs <*> onLambda bodylam
  where
    onLambda lam = do
      params <- forM (lambdaParams lam) $ \(Param pv t) ->
        case t of
          Prim Unit -> pure $ Param pv $ MemPrim Unit
          Acc acc ispace ts u -> pure $ Param pv $ MemAcc acc ispace ts u
          _ -> error $ "Unexpected WithAcc lambda param: " ++ pretty (Param pv t)
      allocInLambda params (lambdaBody lam)

    onInput (shape, arrs, op) =
      (shape,arrs,) <$> traverse (onOp shape arrs) op

    onOp accshape arrs (lam, nes) = do
      let num_vs = length (lambdaReturnType lam)
          num_is = shapeRank accshape
          (i_params, x_params, y_params) =
            splitAt3 num_is num_vs $ lambdaParams lam
          i_params' = map ((`Param` MemPrim int64) . paramName) i_params
          is = map (DimFix . Var . paramName) i_params'
      x_params' <- zipWithM (onXParam is) x_params arrs
      y_params' <- zipWithM (onYParam is) y_params arrs
      lam' <-
        allocInLambda
          (i_params' <> x_params' <> y_params')
          (lambdaBody lam)
      return (lam', nes)

    mkP p pt shape u mem ixfun is =
      Param p . MemArray pt shape u . ArrayIn mem . IxFun.slice ixfun $
        fmap (fmap pe64) $ is ++ map sliceDim (shapeDims shape)

    onXParam _ (Param p (Prim t)) _ =
      return $ Param p (MemPrim t)
    onXParam is (Param p (Array pt shape u)) arr = do
      (mem, ixfun) <- lookupArraySummary arr
      return $ mkP p pt shape u mem ixfun is
    onXParam _ p _ =
      error $ "Cannot handle MkAcc param: " ++ pretty p

    onYParam _ (Param p (Prim t)) _ =
      return $ Param p (MemPrim t)
    onYParam is (Param p (Array pt shape u)) arr = do
      arr_t <- lookupType arr
      mem <- allocForArray arr_t DefaultSpace
      let base_dims = map pe64 $ arrayDims arr_t
          ixfun = IxFun.iota base_dims
      pure $ mkP p pt shape u mem ixfun is
    onYParam _ p _ =
      error $ "Cannot handle MkAcc param: " ++ pretty p
allocInExp e = mapExpM alloc e
  where
    alloc =
      identityMapper
        { mapOnBody = error "Unhandled Body in ExplicitAllocations",
          mapOnRetType = error "Unhandled RetType in ExplicitAllocations",
          mapOnBranchType = error "Unhandled BranchType in ExplicitAllocations",
          mapOnFParam = error "Unhandled FParam in ExplicitAllocations",
          mapOnLParam = error "Unhandled LParam in ExplicitAllocations",
          mapOnOp = \op -> do
            handle <- asks allocInOp
            handle op
        }

subExpIxFun ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  SubExp ->
  AllocM fromrep torep (Maybe IxFun)
subExpIxFun Constant {} = return Nothing
subExpIxFun (Var v) = do
  info <- lookupMemInfo v
  case info of
    MemArray _ptp _shp _u (ArrayIn _ ixf) -> return $ Just ixf
    _ -> return Nothing

shiftShapeExts :: Int -> MemInfo ExtSize u r -> MemInfo ExtSize u r
shiftShapeExts k (MemArray pt shape u returns) =
  MemArray pt (fmap shift shape) u returns
  where
    shift (Ext i) = Ext (i + k)
    shift (Free x) = Free x
shiftShapeExts _ ret = ret

addResCtxInIfBody ::
  (Allocable fromrep torep, Allocator torep (AllocM fromrep torep)) =>
  [ExtType] ->
  Body torep ->
  [Maybe Space] ->
  [Maybe (ExtIxFun, [TPrimExp Int64 VName])] ->
  AllocM fromrep torep (Body torep, [BodyReturns])
addResCtxInIfBody ifrets (Body _ bnds res) spaces substs = buildBody $ do
  mapM_ addStm bnds
  (ctx, ctx_rets, res', res_rets, total_existentials) <-
    foldM helper ([], [], [], [], 0) (zip4 ifrets res substs spaces)
  pure
    ( ctx <> res',
      -- We need to adjust the existentials in shapes corresponding
      -- to the previous type, because we added more existentials in
      -- front.
      ctx_rets ++ map (shiftShapeExts total_existentials) res_rets
    )
  where
    helper (ctx_acc, ctx_rets_acc, res_acc, res_rets_acc, k) (ifr, r, mbixfsub, sp) =
      case mbixfsub of
        Nothing -> do
          -- does NOT generalize/antiunify; ensure direct
          r' <- ensureDirect sp r
          (mem_ctx_ses, mem_ctx_rets) <- unzip <$> bodyReturnMemCtx r'
          let body_ret = inspect k ifr sp
          pure
            ( ctx_acc ++ mem_ctx_ses,
              ctx_rets_acc ++ mem_ctx_rets,
              res_acc ++ [r'],
              res_rets_acc ++ [body_ret],
              k + length mem_ctx_ses
            )
        Just (ixfn, m) -> do
          -- generalizes
          let i = length m
          ext_ses <- mapM (toSubExp "ixfn_exist") m
          (mem_ctx_ses, mem_ctx_rets) <- unzip <$> bodyReturnMemCtx r
          let sp' = fromMaybe DefaultSpace sp
              ixfn' = fmap (adjustExtPE k) ixfn
              exttp = case ifr of
                Array pt shp' u ->
                  MemArray pt shp' u $ ReturnsNewBlock sp' (k + i) ixfn'
                _ -> error "Impossible case reached in addResCtxInIfBody"
          pure
            ( ctx_acc ++ subExpsRes ext_ses ++ mem_ctx_ses,
              ctx_rets_acc ++ map (const (MemPrim int64)) ext_ses ++ mem_ctx_rets,
              res_acc ++ [r],
              res_rets_acc ++ [exttp],
              k + i + 1
            )

    inspect k (Array pt shape u) space =
      let space' = fromMaybe DefaultSpace space
          bodyret =
            MemArray pt shape u $
              ReturnsNewBlock space' k $
                IxFun.iota $ map convert $ shapeDims shape
       in bodyret
    inspect _ (Acc acc ispace ts u) _ = MemAcc acc ispace ts u
    inspect _ (Prim pt) _ = MemPrim pt
    inspect _ (Mem space) _ = MemMem space

    convert (Ext i) = le64 (Ext i)
    convert (Free v) = Free <$> pe64 v

    adjustExtV :: Int -> Ext VName -> Ext VName
    adjustExtV _ (Free v) = Free v
    adjustExtV k (Ext i) = Ext (k + i)

    adjustExtPE :: Int -> TPrimExp t (Ext VName) -> TPrimExp t (Ext VName)
    adjustExtPE k = fmap (adjustExtV k)

mkSpaceOks ::
  (Mem torep, LocalScope torep m) =>
  Int ->
  Body torep ->
  m [Maybe Space]
mkSpaceOks num_vals (Body _ stms res) =
  inScopeOf stms $ mapM (mkSpaceOK . resSubExp) $ takeLast num_vals res
  where
    mkSpaceOK (Var v) = do
      v_info <- lookupMemInfo v
      case v_info of
        MemArray _ _ _ (ArrayIn mem _) -> do
          mem_info <- lookupMemInfo mem
          case mem_info of
            MemMem space -> return $ Just space
            _ -> return Nothing
        _ -> return Nothing
    mkSpaceOK _ = return Nothing

allocInLoopForm ::
  ( Allocable fromrep torep,
    Allocator torep (AllocM fromrep torep)
  ) =>
  LoopForm fromrep ->
  AllocM fromrep torep (LoopForm torep)
allocInLoopForm (WhileLoop v) = return $ WhileLoop v
allocInLoopForm (ForLoop i it n loopvars) =
  ForLoop i it n <$> mapM allocInLoopVar loopvars
  where
    allocInLoopVar (p, a) = do
      (mem, ixfun) <- lookupArraySummary a
      case paramType p of
        Array pt shape u -> do
          dims <- map pe64 . arrayDims <$> lookupType a
          let ixfun' =
                IxFun.slice ixfun $
                  fullSliceNum dims [DimFix $ le64 i]
          return (p {paramDec = MemArray pt shape u $ ArrayIn mem ixfun'}, a)
        Prim bt ->
          return (p {paramDec = MemPrim bt}, a)
        Mem space ->
          return (p {paramDec = MemMem space}, a)
        Acc acc ispace ts u ->
          return (p {paramDec = MemAcc acc ispace ts u}, a)

class SizeSubst op where
  opSizeSubst :: PatT dec -> op -> ChunkMap
  opIsConst :: op -> Bool
  opIsConst = const False

instance SizeSubst () where
  opSizeSubst _ _ = mempty

instance SizeSubst op => SizeSubst (MemOp op) where
  opSizeSubst pat (Inner op) = opSizeSubst pat op
  opSizeSubst _ _ = mempty

  opIsConst (Inner op) = opIsConst op
  opIsConst _ = False

sizeSubst :: SizeSubst (Op rep) => Stm rep -> ChunkMap
sizeSubst (Let pat _ (Op op)) = opSizeSubst pat op
sizeSubst _ = mempty

stmConsts :: SizeSubst (Op rep) => Stm rep -> S.Set VName
stmConsts (Let pat _ (Op op))
  | opIsConst op = S.fromList $ patNames pat
stmConsts _ = mempty

mkLetNamesB' ::
  ( Op (Rep m) ~ MemOp inner,
    MonadBuilder m,
    ExpDec (Rep m) ~ (),
    Allocator (Rep m) (PatAllocM (Rep m))
  ) =>
  ExpDec (Rep m) ->
  [VName] ->
  Exp (Rep m) ->
  m (Stm (Rep m))
mkLetNamesB' dec names e = do
  scope <- askScope
  pat <- bindPatWithAllocations scope names e
  return $ Let pat (defAux dec) e

mkLetNamesB'' ::
  ( Op (Rep m) ~ MemOp inner,
    ExpDec rep ~ (),
    HasScope (Engine.Wise rep) m,
    Allocator rep (PatAllocM rep),
    MonadBuilder m,
    Engine.CanBeWise (Op rep)
  ) =>
  [VName] ->
  Exp (Engine.Wise rep) ->
  m (Stm (Engine.Wise rep))
mkLetNamesB'' names e = do
  scope <- Engine.removeScopeWisdom <$> askScope
  (pat, prestms) <- runPatAllocM (patWithAllocations names $ Engine.removeExpWisdom e) scope
  mapM_ bindAllocStm prestms
  let pat' = Engine.addWisdomToPat pat e
      dec = Engine.mkWiseExpDec pat' () e
  return $ Let pat' (defAux dec) e

simplifiable ::
  ( Engine.SimplifiableRep rep,
    ExpDec rep ~ (),
    BodyDec rep ~ (),
    Op rep ~ MemOp inner,
    Allocator rep (PatAllocM rep)
  ) =>
  (Engine.OpWithWisdom inner -> UT.UsageTable) ->
  (inner -> Engine.SimpleM rep (Engine.OpWithWisdom inner, Stms (Engine.Wise rep))) ->
  SimpleOps rep
simplifiable innerUsage simplifyInnerOp =
  SimpleOps mkExpDecS' mkBodyS' protectOp opUsage simplifyOp
  where
    mkExpDecS' _ pat e =
      return $ Engine.mkWiseExpDec pat () e

    mkBodyS' _ bnds res = return $ mkWiseBody () bnds res

    protectOp taken pat (Alloc size space) = Just $ do
      tbody <- resultBodyM [size]
      fbody <- resultBodyM [intConst Int64 0]
      size' <-
        letSubExp "hoisted_alloc_size" $
          If taken tbody fbody $ IfDec [MemPrim int64] IfFallback
      letBind pat $ Op $ Alloc size' space
    protectOp _ _ _ = Nothing

    opUsage (Alloc (Var size) _) =
      UT.sizeUsage size
    opUsage (Alloc _ _) =
      mempty
    opUsage (Inner inner) =
      innerUsage inner

    simplifyOp (Alloc size space) =
      (,) <$> (Alloc <$> Engine.simplify size <*> pure space) <*> pure mempty
    simplifyOp (Inner k) = do
      (k', hoisted) <- simplifyInnerOp k
      return (Inner k', hoisted)

bindPatWithAllocations ::
  ( MonadBuilder m,
    ExpDec rep ~ (),
    Op (Rep m) ~ MemOp inner,
    Allocator rep (PatAllocM rep)
  ) =>
  Scope rep ->
  [VName] ->
  Exp rep ->
  m (Pat rep)
bindPatWithAllocations types names e = do
  (pat, prebnds) <- runPatAllocM (patWithAllocations names e) types
  mapM_ bindAllocStm prebnds
  return pat

data ExpHint
  = NoHint
  | Hint IxFun Space

defaultExpHints :: (Monad m, ASTRep rep) => Exp rep -> m [ExpHint]
defaultExpHints e = return $ replicate (expExtTypeSize e) NoHint
