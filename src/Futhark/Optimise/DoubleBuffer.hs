{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | The simplification engine is only willing to hoist allocations
-- out of loops if the memory block resulting from the allocation is
-- dead at the end of the loop.  If it is not, we may cause data
-- hazards.
--
-- This module rewrites loops with memory block merge parameters such
-- that each memory block is copied at the end of the iteration, thus
-- ensuring that any allocation inside the loop is dead at the end of
-- the loop.  This is only possible for allocations whose size is
-- loop-invariant, although the initial size may differ from the size
-- produced by the loop result.
--
-- Additionally, inside parallel kernels we also copy the initial
-- value.  This has the effect of making the memory block returned by
-- the array non-existential, which is important for later memory
-- expansion to work.
module Futhark.Optimise.DoubleBuffer
       ( doubleBuffer )
       where

import           Control.Applicative
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Reader
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import           Data.Maybe
import           Data.List

import           Prelude

import           Futhark.MonadFreshNames
import           Futhark.Tools (intraproceduralTransformation)
import           Futhark.Representation.ExplicitMemory
import qualified Futhark.Representation.ExplicitMemory.IndexFunction.Unsafe as IxFun
import           Futhark.Pass

doubleBuffer :: Pass ExplicitMemory ExplicitMemory
doubleBuffer =
  Pass { passName = "Double buffer"
       , passDescription = "Perform double buffering for merge parameters of sequential loops."
       , passFunction = intraproceduralTransformation optimiseFunDef
       }

optimiseFunDef :: MonadFreshNames m => FunDef -> m FunDef
optimiseFunDef fundec = do
  body' <- runReaderT (runDoubleBufferM $ inScopeOf fundec $
                       optimiseBody $ funDefBody fundec) $
           Env emptyScope False
  return fundec { funDefBody = body' }
  where emptyScope :: Scope ExplicitMemory
        emptyScope = mempty

data Env = Env { envScope :: Scope ExplicitMemory
               , envCopyInit :: Bool
                 -- ^ If true, copy initial values of merge
                 -- parameters.  This is necessary to remove
                 -- existential memory inside kernels, but seems to
                 -- break C compiler vectorisation in sequential code.
                 -- We set this to true once we enter kernels.
               }

newtype DoubleBufferM m a = DoubleBufferM { runDoubleBufferM :: ReaderT Env m a }
                          deriving (Functor, Applicative, Monad,
                                    MonadReader Env, MonadFreshNames)

instance (Applicative m, Monad m) =>
         HasScope ExplicitMemory (DoubleBufferM m) where
  askScope = asks envScope

instance (Applicative m, Monad m) =>
         LocalScope ExplicitMemory (DoubleBufferM m) where
  localScope scope = local $ \env -> env { envScope = envScope env <> scope }

optimiseBody :: MonadFreshNames m => Body -> DoubleBufferM m Body
optimiseBody body = do
  bnds' <- optimiseBindings $ bodyBindings body
  return $ body { bodyBindings = bnds' }

optimiseBindings :: MonadFreshNames m => [Binding] -> DoubleBufferM m [Binding]
optimiseBindings [] = return []
optimiseBindings (e:es) = do
  e_es <- optimiseBinding e
  es' <- inScopeOf e_es $ optimiseBindings es
  return $ e_es ++ es'

optimiseBinding :: MonadFreshNames m => Binding -> DoubleBufferM m [Binding]
optimiseBinding (Let pat () (DoLoop ctx val form body)) = do
  body' <- localScope (scopeOfLoopForm form <> scopeOfFParams (map fst $ ctx++val)) $
           optimiseBody body
  (bnds, ctx', val', body'') <- optimiseLoop ctx val body'
  return $ bnds ++ [Let pat () $ DoLoop ctx' val' form body'']
optimiseBinding (Let pat () e) = pure <$> Let pat () <$> mapExpM optimise e
  where optimise = identityMapper { mapOnBody = optimiseBody
                                  , mapOnOp = optimiseOp
                                  }
          where optimiseOp (Inner k) = Inner <$> optimiseKernel k
                optimiseOp op = return op
                optimiseKernel = local (\env -> env { envCopyInit = True }) .
                                 mapKernelM identityKernelMapper
                                 { mapOnKernelBody = optimiseBody
                                 , mapOnKernelLambda = optimiseLambda
                                 }
                optimiseLambda lam = do
                  body <- inScopeOf lam $ optimiseBody $ lambdaBody lam
                  return lam { lambdaBody = body }

optimiseLoop :: MonadFreshNames m =>
                [(FParam, SubExp)] -> [(FParam, SubExp)] -> Body
             -> DoubleBufferM m ([Binding], [(FParam, SubExp)], [(FParam, SubExp)], Body)
optimiseLoop ctx val body = do
  -- We start out by figuring out which of the merge variables should
  -- be double-buffered.
  buffered <- doubleBufferMergeParams
              (zip (map fst ctx) (bodyResult body))
              (map fst merge)
              (boundInBody body)
  -- Then create the allocations of the buffers and copies of the
  -- initial values.
  (merge', allocs) <- allocBindings merge buffered
  -- Modify the loop body to copy buffered result arrays.
  let body' = doubleBufferResult (map fst merge) buffered body
      (ctx', val') = splitAt (length ctx) merge'
  -- Modify the initial merge p
  return (allocs, ctx', val', body')
  where merge = ctx ++ val

-- | The booleans indicate whether we should also play with the
-- initial merge values.
data DoubleBuffer = BufferAlloc VName SubExp Space Bool
                  | BufferCopy VName IxFun.IxFun VName Bool
                    -- ^ First name is the memory block to copy to,
                    -- second is the name of the array copy.
                  | NoBuffer
                    deriving (Show)

doubleBufferMergeParams :: MonadFreshNames m =>
                           [(FParam,SubExp)] -> [FParam] -> Names
                        -> DoubleBufferM m [DoubleBuffer]
doubleBufferMergeParams ctx_and_res val_params bound_in_loop = do
  copy_init <- asks envCopyInit
  evalStateT (mapM (buffer copy_init) val_params) HM.empty
  where loopInvariantSize copy_init (Constant v) =
          Just (Constant v, copy_init)
        loopInvariantSize copy_init (Var v) =
          case find ((==v) . paramName . fst) ctx_and_res of
            Just (_, Constant val) ->
              Just (Constant val, False)
            Just (_, Var v') | not $ v' `HS.member` bound_in_loop ->
              Just (Var v', False)
            Just _ ->
              Nothing
            Nothing ->
              Just (Var v, copy_init)

        buffer copy_init fparam = case paramType fparam of
          Mem size space
            | Just (size', b) <- loopInvariantSize copy_init size -> do
                -- Let us double buffer this!
                bufname <- lift $ newVName "double_buffer_mem"
                modify $ HM.insert (paramName fparam) (bufname, b)
                return $ BufferAlloc bufname size' space b
          Array {}
            | ArrayMem _ _ _ mem ixfun <- paramAttr fparam -> do
                buffered <- gets $ HM.lookup mem
                case buffered of
                  Just (bufname, b) -> do
                    copyname <- lift $ newVName "double_buffer_array"
                    return $ BufferCopy bufname ixfun copyname b
                  Nothing ->
                    return NoBuffer
          _ -> return NoBuffer

allocBindings :: MonadFreshNames m =>
                 [(FParam,SubExp)] -> [DoubleBuffer]
              -> DoubleBufferM m ([(FParam,SubExp)], [Binding])
allocBindings merge = runWriterT . zipWithM allocation merge
  where allocation m@(Param pname _, _) (BufferAlloc name size space b) = do
          tell [Let (Pattern [] [PatElem name BindVar $ MemMem size space]) () $
                Op $ Alloc size space]
          if b
            then return (Param pname $ MemMem size space, Var name)
            else return m
        allocation (f, Var v) (BufferCopy mem _ _ b) | b = do
          v_copy <- lift $ newVName $ baseString v ++ "_double_buffer_copy"
          (_v_mem, v_ixfun) <- lift $ lookupArraySummary v
          let bt = elemType $ paramType f
              shape = arrayShape $ paramType f
              bound = ArrayMem bt shape NoUniqueness mem v_ixfun
          tell [Let (Pattern []
                     [PatElem v_copy BindVar bound]) () $
                PrimOp $ Copy v]
          return (f, Var v_copy)
        allocation (f, se) _ =
          return (f, se)

doubleBufferResult :: [FParam] -> [DoubleBuffer] -> Body -> Body
doubleBufferResult valparams buffered (Body () bnds res) =
  let (ctx_res, val_res) = splitAt (length res - length valparams) res
      (copybnds,val_res') =
        unzip $ zipWith3 buffer valparams buffered val_res
  in Body () (bnds++catMaybes copybnds) $ ctx_res ++ val_res'
  where buffer _ (BufferAlloc bufname _ _ _) _ =
          (Nothing, Var bufname)

        buffer fparam (BufferCopy bufname ixfun copyname _) (Var v) =
          -- To construct the copy we will need to figure out its type
          -- based on the type of the function parameter.
          let t = resultType $ paramType fparam
              summary = ArrayMem (elemType t) (arrayShape t) NoUniqueness bufname ixfun
              copybnd = Let (Pattern [] [PatElem copyname BindVar summary]) () $
                        PrimOp $ Copy v
          in (Just copybnd, Var copyname)

        buffer _ _ se =
          (Nothing, se)

        parammap = HM.fromList $ zip (map paramName valparams) res

        resultType t = t `setArrayDims` map substitute (arrayDims t)

        substitute (Var v)
          | Just replacement <- HM.lookup v parammap = replacement
        substitute se =
          se
