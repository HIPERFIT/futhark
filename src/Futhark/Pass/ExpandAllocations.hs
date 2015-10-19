{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- | Expand allocations inside of maps when possible.
module Futhark.Pass.ExpandAllocations
       ( expandAllocations )
       where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe
import Data.List
import Data.Monoid

import Prelude hiding (div, quot)

import qualified Futhark.Analysis.ScalExp as SE
import Futhark.MonadFreshNames
import Futhark.Representation.ExplicitMemory
import Futhark.Tools
import Futhark.Util
import Futhark.Pass
import qualified Futhark.Representation.ExplicitMemory.IndexFunction.Unsafe as IxFun

expandAllocations :: Pass ExplicitMemory ExplicitMemory
expandAllocations = simplePass
                    "expand allocations"
                    "Expand allocations" $
                    intraproceduralTransformation transformFunDec

transformFunDec :: MonadFreshNames m => FunDec -> m FunDec
transformFunDec fundec = do
  body' <- modifyNameSource $ runState m
  return fundec { funDecBody = body' }
  where m = transformBody $ funDecBody fundec

type ExpandM = State VNameSource

transformBody :: Body -> ExpandM Body
transformBody (Body () bnds res) = do
  bnds' <- concat <$> mapM transformBinding bnds
  return $ Body () bnds' res

transformBinding :: Binding -> ExpandM [Binding]

transformBinding (Let pat () e) = do
  (bnds, e') <- transformExp =<< mapExpM transform e
  return $ bnds ++ [Let pat () e']
  where transform = identityMapper { mapOnBody = transformBody
                                   , mapOnLambda = transformLambda
                                   , mapOnExtLambda = transformExtLambda
                                   }

transformExp :: Exp -> ExpandM ([Binding], Exp)
transformExp (LoopOp (Kernel cs w thread_num ispace inps returns body))
  -- Extract allocations from the body.
  | Right (body', thread_allocs) <- extractKernelAllocations bound_before_body body = do

  (alloc_bnds, alloc_offsets) <- expandedAllocations w thread_num thread_allocs
  let body'' = if null alloc_bnds then body'
               else offsetMemorySummariesInBody alloc_offsets body'

  return (alloc_bnds, LoopOp $ Kernel cs w thread_num ispace inps returns body'')
  where bound_before_body =
          HS.fromList $ map fst ispace ++ map kernelInputName inps

transformExp (LoopOp (ReduceKernel cs w kernel_size red_lam fold_lam nes arrs))
  -- Extract allocations from the lambdas.
  | Right (red_lam_body', red_lam_thread_allocs) <-
      extractKernelAllocations bound_in_red_lam $ lambdaBody red_lam,
    Right (fold_lam_body', fold_lam_thread_allocs) <-
      extractKernelAllocations bound_in_fold_lam $ lambdaBody fold_lam = do

  num_threads <- newVName "num_threads"
  let num_threads_pat = Pattern [] [PatElem (Ident num_threads $ Basic Int) BindVar Scalar]
      num_threads_bnd = Let num_threads_pat () $
                        PrimOp $ BinOp Times num_chunks group_size Int

  (red_alloc_bnds, red_alloc_offsets) <-
    expandedAllocations (Var num_threads) (lambdaIndex red_lam) red_lam_thread_allocs
  (fold_alloc_bnds, fold_alloc_offsets) <-
    expandedAllocations (Var num_threads) (lambdaIndex fold_lam) fold_lam_thread_allocs

  let red_lam_body'' = offsetMemorySummariesInBody red_alloc_offsets red_lam_body'
      fold_lam_body'' = offsetMemorySummariesInBody fold_alloc_offsets fold_lam_body'
      red_lam' = red_lam { lambdaBody = red_lam_body'' }
      fold_lam' = fold_lam { lambdaBody = fold_lam_body'' }
  return (num_threads_bnd : red_alloc_bnds <> fold_alloc_bnds,
          LoopOp $ ReduceKernel cs w kernel_size red_lam' fold_lam' nes arrs)
  where num_chunks = kernelWorkgroups kernel_size
        group_size = kernelWorkgroupSize kernel_size

        bound_in_red_lam = HS.fromList $
                           lambdaIndex red_lam : map paramName (lambdaParams red_lam)
        bound_in_fold_lam = HS.fromList $
                            lambdaIndex fold_lam : map paramName (lambdaParams fold_lam)

transformExp e =
  return ([], e)

transformLambda :: Lambda -> ExpandM Lambda
transformLambda lam = do
  body' <- transformBody $ lambdaBody lam
  return lam { lambdaBody = body' }

transformExtLambda :: ExtLambda -> ExpandM ExtLambda
transformExtLambda lam = do
  body' <- transformBody $ extLambdaBody lam
  return lam { extLambdaBody = body' }

-- | Returns a map from memory block names to their size in bytes,
-- as well as the lambda body where all the allocations have been removed.
-- Only looks at allocations in the immediate body - if there are any
-- further down, we will fail later.  If the size of one of the
-- allocations is not free in the body, we return 'Left' and an
-- error message.
extractKernelAllocations :: Names -> Body
                         -> Either String (Body, HM.HashMap VName (SubExp, Space))
extractKernelAllocations bound_before_body body = do
  (allocs, bnds) <- mapAccumLM isAlloc HM.empty $ bodyBindings body
  return (body { bodyBindings = catMaybes bnds }, allocs)
  where bound_here = bound_before_body `HS.union` boundInBody body

        isAlloc _ (Let (Pattern [] [patElem]) () (PrimOp (Alloc (Var v) _)))
          | v `HS.member` bound_here =
            throwError $ "Size " ++ pretty v ++
            " for block " ++ pretty patElem ++
            " is not lambda-invariant"

        isAlloc allocs (Let (Pattern [] [patElem]) () (PrimOp (Alloc size space))) =
          return (HM.insert (patElemName patElem) (size, space) allocs,
                  Nothing)

        isAlloc allocs bnd =
          return (allocs, Just bnd)

expandedAllocations :: SubExp
                    -> VName
                    -> HM.HashMap VName (SubExp, Space)
                    -> ExpandM ([Binding], RebaseMap)
expandedAllocations num_threads thread_index thread_allocs = do
  -- We expand the allocations by multiplying their size with the
  -- number of kernel threads.
  alloc_bnds <-
    liftM concat $ forM (HM.toList thread_allocs) $ \(mem,(per_thread_size, space)) -> do
      total_size <- newVName "total_size"
      let sizepat = Pattern [] [PatElem (Ident total_size $ Basic Int) BindVar Scalar]
          allocpat = Pattern [] [PatElem
                                 (Ident mem $ Mem (Var total_size) space)
                                 BindVar Scalar]
      return [Let sizepat () $ PrimOp $ BinOp Times num_threads per_thread_size Int,
              Let allocpat () $ PrimOp $ Alloc (Var total_size) space]
  -- Fix every reference to the memory blocks to be offset by the
  -- thread number.
  let alloc_offsets =
        RebaseMap { rebaseMap =
                    HM.map (const newBase) thread_allocs
                  , indexVariable = thread_index
                  , kernelWidth = num_threads
                  }
  return (alloc_bnds, alloc_offsets)
  where newBase old_shape =
          let perm = [length old_shape, 0] ++ [1..length old_shape-1]
              root_ixfun = IxFun.iota (old_shape ++ [SE.intSubExpToScalExp num_threads])
              permuted_ixfun = IxFun.permute root_ixfun perm
              offset_ixfun = IxFun.applyInd permuted_ixfun [SE.Id thread_index Int]
          in offset_ixfun

data RebaseMap = RebaseMap {
    rebaseMap :: HM.HashMap VName (IxFun.Shape -> IxFun.IxFun)
    -- ^ A map from memory block names to new index function bases.
  , indexVariable :: VName
  , kernelWidth :: SubExp
  }

lookupNewBase :: VName -> RebaseMap -> Maybe (IxFun.Shape -> IxFun.IxFun)
lookupNewBase name = HM.lookup name . rebaseMap

offsetMemorySummariesInBody :: RebaseMap -> Body -> Body
offsetMemorySummariesInBody offsets (Body attr bnds res) =
  Body attr (snd $ mapAccumL offsetMemorySummariesInBinding offsets bnds) res

offsetMemorySummariesInBinding :: RebaseMap -> Binding
                               -> (RebaseMap, Binding)
offsetMemorySummariesInBinding offsets (Let pat attr e) =
  (offsets', Let pat' attr $ offsetMemorySummariesInExp offsets e)
  where (offsets', pat') = offsetMemorySummariesInPattern offsets pat

offsetMemorySummariesInPattern :: RebaseMap -> Pattern -> (RebaseMap, Pattern)
offsetMemorySummariesInPattern offsets (Pattern ctx vals) =
  (offsets', Pattern ctx vals')
  where offsets' = foldl inspectCtx offsets ctx
        vals' = map inspectVal vals
        inspectVal patElem =
          patElem { patElemLore =
                       offsetMemorySummariesInMemSummary offsets' $ patElemLore patElem
                  }
        inspectCtx ctx_offsets patElem
          | Mem _ _ <- patElemType patElem =
              error $ unwords ["Cannot deal with existential memory block ",
                               pretty (patElemName patElem),
                               "when expanding inside kernels."]
          | otherwise =
              ctx_offsets

offsetMemorySummariesInFParam :: RebaseMap -> FParam -> FParam
offsetMemorySummariesInFParam offsets fparam =
  fparam { paramLore = offsetMemorySummariesInMemSummary offsets $ paramLore fparam }

offsetMemorySummariesInMemSummary :: RebaseMap -> MemSummary -> MemSummary
offsetMemorySummariesInMemSummary offsets (MemSummary mem ixfun)
  | Just new_base <- lookupNewBase mem offsets =
      MemSummary mem $ IxFun.rebase (new_base $ IxFun.base ixfun) ixfun
offsetMemorySummariesInMemSummary _ summary =
  summary

offsetMemorySummariesInExp :: RebaseMap -> Exp -> Exp
offsetMemorySummariesInExp offsets (LoopOp (DoLoop res merge form body)) =
  LoopOp $ DoLoop res (zip mergeparams' mergeinit) form body'
  where (mergeparams, mergeinit) = unzip merge
        body' = offsetMemorySummariesInBody offsets body
        mergeparams' = map (offsetMemorySummariesInFParam offsets) mergeparams
offsetMemorySummariesInExp offsets e = mapExp recurse e
  where recurse = identityMapper { mapOnBody = return . offsetMemorySummariesInBody offsets
                                 , mapOnLambda = return . offsetMemorySummariesInLambda offsets
                                 }

offsetMemorySummariesInLambda :: RebaseMap -> Lambda -> Lambda
offsetMemorySummariesInLambda offsets lam =
  lam { lambdaParams = params,
        lambdaBody = body
      }
  where params = map (offsetMemorySummariesInFParam offsets) $ lambdaParams lam
        body = offsetMemorySummariesInBody offsets $ lambdaBody lam
