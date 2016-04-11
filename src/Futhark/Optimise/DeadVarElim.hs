-- | This module implements a compiler pass that removes unused
-- @let@-bindings.
module Futhark.Optimise.DeadVarElim
       ( deadCodeElim
       , deadCodeElimFun
       , deadCodeElimBody
       )
  where

import Control.Applicative
import Control.Monad.Writer

import qualified Data.HashSet as HS

import Prelude

import Futhark.Representation.AST

-----------------------------------------------------------------
-----------------------------------------------------------------
---- This file implements Dead-Variable Elimination          ----
-----------------------------------------------------------------
-----------------------------------------------------------------

data DCElimRes = DCElimRes {
    resSuccess :: Bool
  -- ^ Whether we have changed something.
  , resMap     :: Names
  -- ^ The hashtable recording the uses
  }

instance Monoid DCElimRes where
  DCElimRes s1 m1 `mappend` DCElimRes s2 m2 =
    DCElimRes (s1 || s2) (m1 `HS.union` m2) --(io1 || io2)
  mempty = DCElimRes False HS.empty -- False

type DCElimM = Writer DCElimRes

runDCElimM :: DCElimM a -> (a, DCElimRes)
runDCElimM = runWriter

collectRes :: [VName] -> DCElimM a -> DCElimM (a, Bool)
collectRes mvars m = pass collect
  where wasNotUsed hashtab vnm =
          return $ not (HS.member vnm hashtab)

        collect = do
          (x,res) <- listen m
          tmps    <- mapM (wasNotUsed (resMap res)) mvars
          return ( (x, and tmps), const res )

changed :: DCElimM a -> DCElimM a
changed m = pass collect
    where
     collect = do
        (x, res) <- listen m
        return (x, const $ res { resSuccess = True })

-- | Applies Dead-Code Elimination to an entire program.
deadCodeElim :: Attributes lore => Prog lore -> Prog lore
deadCodeElim = Prog . map deadCodeElimFun . progFunctions

-- | Applies Dead-Code Elimination to just a single function.
deadCodeElimFun :: Attributes lore => FunDef lore -> FunDef lore
deadCodeElimFun (FunDef entry fname rettype args body) =
  let body' = deadCodeElimBody body
  in FunDef entry fname rettype args body'

-- | Applies Dead-Code Elimination to just a single body.
deadCodeElimBody :: Attributes lore => Body lore -> Body lore
deadCodeElimBody = fst . runDCElimM . deadCodeElimBodyM

--------------------------------------------------------------------
--------------------------------------------------------------------
---- Main Function: Dead-Code Elimination for exps              ----
--------------------------------------------------------------------
--------------------------------------------------------------------

deadCodeElimSubExp :: SubExp -> DCElimM SubExp
deadCodeElimSubExp (Var ident)  = Var <$> deadCodeElimVName ident
deadCodeElimSubExp (Constant v) = return $ Constant v

deadCodeElimBodyM :: Attributes lore => Body lore -> DCElimM (Body lore)

deadCodeElimBodyM (Body bodylore (Let pat explore e:bnds) res) = do
  let idds = patternNames pat
  seen $ freeIn explore
  (Body _ bnds' res', noref) <-
    collectRes idds $ do
      deadCodeElimPat pat
      deadCodeElimBodyM $ Body bodylore bnds res
  if noref
  then changed $ return $ Body bodylore bnds' res'
  else do e' <- deadCodeElimExp e
          return $ Body bodylore
                   (Let pat explore e':bnds') res'

deadCodeElimBodyM (Body bodylore [] es) = do
  seen $ freeIn bodylore
  Body bodylore [] <$> mapM deadCodeElimSubExp es

deadCodeElimExp :: Attributes lore => Exp lore -> DCElimM (Exp lore)
deadCodeElimExp (DoLoop ctx val form body) = do
  let (ctxparams, ctxinit) = unzip ctx
      (valparams, valinit) = unzip val
  mapM_ deadCodeElimParam ctxparams
  mapM_ deadCodeElimSubExp ctxinit
  mapM_ deadCodeElimParam valparams
  mapM_ deadCodeElimSubExp valinit
  body' <- deadCodeElimBodyM body
  case form of
    ForLoop _ bound -> void $ deadCodeElimSubExp bound
    WhileLoop cond  -> void $ deadCodeElimVName cond
  return $ DoLoop ctx val form body'
deadCodeElimExp e = mapExpM mapper e
  where mapper = Mapper {
                   mapOnBody = deadCodeElimBodyM
                 , mapOnSubExp = deadCodeElimSubExp
                 , mapOnVName = deadCodeElimVName
                 , mapOnCertificates = mapM deadCodeElimVName
                 , mapOnRetType = \rt -> do
                   seen $ freeIn rt
                   return rt
                 , mapOnFParam = \fparam -> do
                   seen $ freeIn fparam
                   return fparam
                 , mapOnOp = \op -> seen (freeIn op) >> return op
                 }

deadCodeElimVName :: VName -> DCElimM VName
deadCodeElimVName vnm = do
  seen $ HS.singleton vnm
  return vnm

deadCodeElimPat :: FreeIn attr => PatternT attr -> DCElimM ()
deadCodeElimPat = mapM_ deadCodeElimPatElem . patternElements

deadCodeElimPatElem :: FreeIn attr => PatElemT attr -> DCElimM ()
deadCodeElimPatElem patelem =
  seen $ patElemName patelem `HS.delete` freeIn patelem

deadCodeElimParam :: FreeIn attr => ParamT attr -> DCElimM ()
deadCodeElimParam fparam =
  seen $ paramName fparam `HS.delete` freeIn fparam

seen :: Names -> DCElimM ()
seen = tell . DCElimRes False
