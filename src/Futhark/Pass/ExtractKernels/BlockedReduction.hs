module Futhark.Pass.ExtractKernels.BlockedReduction
       ( blockedReduction )
       where

import Control.Applicative
import Control.Monad
import Data.Monoid

import Prelude

import Futhark.Representation.Basic
import Futhark.MonadFreshNames
import Futhark.Tools
import Futhark.Transform.Rename

blockedReduction :: (MonadFreshNames m, HasTypeEnv m) =>
                    Pattern
                 -> Certificates -> SubExp
                 -> Lambda -> Lambda
                 -> [SubExp]
                 -> [VName]
                 -> m [Binding]
blockedReduction pat cs w reduce_lam fold_lam nes arrs = runBinder_ $ do
  num_chunks <- letSubExp "num_chunks" $
                Apply (nameFromString "num_groups") [] (basicRetType Int)
  group_size <- letSubExp "group_size" $
                Apply (nameFromString "group_size") [] (basicRetType Int)
  chunk_size <- newVName "chunk_size"
  other_index <- newVName "other_index"

  let one = Constant $ IntVal 1

  num_threads <-
    letSubExp "num_threads" $ PrimOp $ BinOp Times num_chunks group_size Int

  per_thread_elements <-
    letSubExp "per_thread_elements" =<<
    eDivRoundingUp (eSubExp w) (eSubExp num_threads)

  let step_one_size = KernelSize num_chunks group_size
                      per_thread_elements w per_thread_elements
      step_two_size = KernelSize one num_chunks one num_chunks one

  loop_iterator <- newVName "i"
  seq_lam_index <- newVName "lam_index"
  step_one_pat <- basicPattern' [] <$>
                      mapM (mkIntermediateIdent num_chunks) (patternIdents pat)
  step_two_pat <- basicPattern' [] <$>
             mapM (mkIntermediateIdent $ Constant $ IntVal 1) (patternIdents pat)
  let (fold_acc_params, fold_arr_params) =
        splitAt (length nes) $ lambdaParams fold_lam
      chunk_size_param = Param (Ident chunk_size $ Basic Int) ()
      other_index_param = Param (Ident other_index $ Basic Int) ()
  arr_chunk_params <- mapM (mkArrChunkParam $ Var chunk_size) fold_arr_params
  res_idents <- mapM (newIdent' (<>"_res") . paramIdent) fold_acc_params

  start_index <- newVName "start_index"

  ((merge_params, unique_nes), seq_copy_merge) <-
    collectBindings $
    unzip <$> zipWithM mkMergeParam fold_acc_params nes

  let res = map paramName merge_params
      form = ForLoop loop_iterator $ Var chunk_size

      compute_start_index =
        mkLet' [] [Ident start_index $ Basic Int] $
        PrimOp $ BinOp Times (Var seq_lam_index) per_thread_elements Int
      compute_index = mkLet' [] [Ident (lambdaIndex fold_lam) $ Basic Int] $
                      PrimOp $ BinOp Plus (Var start_index) (Var loop_iterator) Int
      read_array_elements =
        [ mkLet' [] [paramIdent param] $ PrimOp $ Index [] arr [Var loop_iterator]
          | (param, arr) <- zip fold_arr_params $ map paramName arr_chunk_params ]

  seq_loop_body <-
    runBodyBinder $ bindingParamTypes (lambdaParams fold_lam) $ do
      mapM_ addBinding $ compute_start_index : compute_index : read_array_elements
      let uniqueRes (Var v) = do
            t <- lookupType v
            if unique t || basicType t
              then return $ Var v
              else letSubExp "unique_res" $ PrimOp $ Copy v
          uniqueRes se =
            return se
      resultBodyM =<< mapM uniqueRes =<< bodyBind (lambdaBody fold_lam)

  let seq_loop =
        mkLet' [] res_idents $
        LoopOp $ DoLoop res (zip merge_params unique_nes) form seq_loop_body
      seq_body = mkBody (seq_copy_merge++[seq_loop]) $ map (Var . identName) res_idents

      seqlam = Lambda { lambdaParams = chunk_size_param : arr_chunk_params
                      , lambdaReturnType = lambdaReturnType fold_lam
                      , lambdaBody = seq_body
                      , lambdaIndex = seq_lam_index
                      }

      reduce_lam' = reduce_lam { lambdaParams = other_index_param :
                                                lambdaParams reduce_lam
                               }

  addBinding =<< renameBinding
    (Let step_one_pat () $
     LoopOp $ ReduceKernel cs w step_one_size reduce_lam' seqlam nes arrs)

  identity_lam_params <- mapM (mkArrChunkParam $ Var chunk_size) fold_acc_params

  elements <- zipWithM newIdent
              (map (baseString . paramName) identity_lam_params) $
              lambdaReturnType seqlam
  let read_elements =
        [ mkLet' [] [element] $
          PrimOp $ Index [] arr [Constant $ IntVal 0]
        | (element, arr) <- zip elements $ map paramName identity_lam_params ]
      identity_body = mkBody read_elements $ map (Var . identName) elements
      identity_lam = Lambda { lambdaParams = chunk_size_param : identity_lam_params
                            , lambdaReturnType = lambdaReturnType fold_lam
                            , lambdaBody = identity_body
                            , lambdaIndex = seq_lam_index
                            }

  addBinding $
    Let step_two_pat () $
    LoopOp $ ReduceKernel [] num_chunks step_two_size
    reduce_lam' identity_lam nes $ patternNames step_one_pat

  forM_ (zip (patternNames step_two_pat) (patternIdents pat)) $ \(arr, x) ->
    addBinding $ mkLet' [] [x] $ PrimOp $ Index [] arr [Constant $ IntVal 0]
  where mkArrChunkParam chunk_size arr_param = do
          ident <- newIdent (baseString (paramName arr_param) <> "_chunk") $
                   arrayOfRow (paramType arr_param) chunk_size
          return $ Param ident ()

        mkIntermediateIdent chunk_size ident =
          newIdent (baseString $ identName ident) $
          arrayOfRow (identType ident) chunk_size

        mkMergeParam acc_param (Var v) = do
          v' <- letExp (baseString v ++ "_copy") $ PrimOp $ Copy v
          return (acc_param { paramIdent =
                              paramIdent acc_param `setIdentUniqueness` Unique
                            },
                  Var v')
        mkMergeParam acc_param se =
          return (acc_param, se)
