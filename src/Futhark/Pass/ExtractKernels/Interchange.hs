{-# LANGUAGE FlexibleContexts #-}
module Futhark.Pass.ExtractKernels.Interchange
       (
         SeqLoop (..)
       , interchangeLoops
       ) where

import Control.Applicative
import Control.Monad.RWS.Strict
import qualified Data.HashSet as HS
import Data.Maybe
import Data.List

import Futhark.Pass.ExtractKernels.Distribution
  (LoopNesting(..), KernelNest, kernelNestLoops)
import Futhark.Representation.SOACS
import Futhark.MonadFreshNames
import Futhark.Tools

import Prelude

data SeqLoop = SeqLoop Pattern [(FParam, SubExp)] LoopForm Body

seqLoopBinding :: SeqLoop -> Binding
seqLoopBinding (SeqLoop pat merge form body) =
  Let pat () $ DoLoop [] merge form body

interchangeLoop :: (MonadBinder m, LocalScope SOACS m) =>
                   SeqLoop -> LoopNesting
                -> m SeqLoop
interchangeLoop
  (SeqLoop loop_pat merge form body)
  (MapNesting pat cs w params_and_arrs) = do
    merge_expanded <-
      localScope (scopeOfLParams $ map fst params_and_arrs) $
      mapM expand merge

    let loop_pat_expanded =
          Pattern [] $ map expandPatElem $ patternElements loop_pat
        new_params = [ Param pname $ fromDecl ptype
                     | (Param pname ptype, _) <- merge ]
        new_arrs = map (paramName . fst) merge_expanded
        rettype = map rowType $ patternTypes loop_pat_expanded

    -- If the map consumes something that is bound outside the loop
    -- (i.e. is not a merge parameter), we have to copy() it.  As a
    -- small simplification, we just remove the parameter outright if
    -- it is not used anymore.  This might happen if the parameter was
    -- used just as the inital value of a merge parameter.
    ((params', arrs'), pre_copy_bnds) <-
      runBinder $ localScope (scopeOfLParams new_params) $
      unzip . catMaybes <$> mapM copyOrRemoveParam params_and_arrs

    let lam = Lambda (params'<>new_params) body rettype
        map_bnd = Let loop_pat_expanded () $
                  Op $ Map cs w lam $ arrs' <> new_arrs
        res = map Var $ patternNames loop_pat_expanded

    return $
      SeqLoop pat merge_expanded form $
      mkBody (pre_copy_bnds++[map_bnd]) res
  where free_in_body = freeInBody body

        copyOrRemoveParam (param, arr)
          | not (paramName param `HS.member` free_in_body) =
            return Nothing
          | otherwise =
            return $ Just (param, arr)

        expandedInit _ (Var v)
          | Just (_, arr) <-
              find ((==v).paramName.fst) params_and_arrs =
              return $ Var arr
        expandedInit param_name se =
          letSubExp (param_name <> "_expanded_init") $
            PrimOp $ Replicate w se

        expand (merge_param, merge_init) = do
          expanded_param <-
            newParam (param_name <> "_expanded") $
            arrayOf (paramDeclType merge_param) (Shape [w]) $
            uniqueness $ declTypeOf merge_param
          expanded_init <- expandedInit param_name merge_init
          return (expanded_param, expanded_init)
            where param_name = baseString $ paramName merge_param

        expandPatElem (PatElem name bindage t) =
          PatElem name bindage $ arrayOfRow t w

interchangeLoops :: (MonadFreshNames m, HasScope SOACS m) =>
                    KernelNest -> SeqLoop
                 -> m [Binding]
interchangeLoops nest loop = do
  (loop', bnds) <-
    runBinder $ foldM interchangeLoop loop $ reverse $ kernelNestLoops nest
  return $ bnds ++ [seqLoopBinding loop']
