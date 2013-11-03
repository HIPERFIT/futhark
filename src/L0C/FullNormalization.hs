{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
--
-- Fully normalize an L0 program to a vaguely three-address-code-like
-- format.  This specifically means that all operands to operators,
-- function calls, SOACs and what have you, must be variables, not
-- expressions.  In essence, we introduce explicit bindings for most
-- every piece of computation.  Some modules (e.g "L0C.Hoisting") will
-- expect a normalized input program.
--
module L0C.FullNormalization
  ( normalizeProg )
  where

import Control.Applicative
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.RWS

import Data.Loc
import qualified Data.Map as M

import L0C.L0
import L0C.FreshNames

data NewBindings = NewBindings (Exp -> Exp)

instance Monoid NewBindings where
  NewBindings f `mappend` NewBindings g =
    NewBindings $ f . g
  mempty = NewBindings id

data Env = Env { envSubsts :: M.Map Ident [Ident]
               }

emptyEnv :: Env
emptyEnv = Env { envSubsts = M.empty }

newtype NormalizeM a = NormalizeM (RWS Env NewBindings (NameSource VName) a)
  deriving (Monad, Functor, Applicative,
            MonadState (NameSource VName),
            MonadReader Env,
            MonadWriter NewBindings)

new :: String -> NormalizeM VName
new k = do (name, src) <- gets $ flip newVName k
           put src
           return name

replaceExp :: String -> Exp -> NormalizeM Ident
replaceExp k e = do
  k' <- new k
  let ident = Ident { identName = k'
                    , identType = typeOf e
                    , identSrcLoc = srclocOf e }
  tell $ NewBindings $ \inner ->
    LetPat (Id ident) e inner $ srclocOf e
  return ident

runNormalizeM :: NormalizeM a -> NameSource VName -> a
runNormalizeM (NormalizeM m) src =
  let (x, _, _) = runRWS m emptyEnv src
  in x

normalizeProg :: Prog -> Prog
normalizeProg prog =
  Prog $ runNormalizeM (mapM normalizeFun $ progFunctions prog) namesrc
  where namesrc = newNameSourceForProg prog

insertBindings :: NormalizeM Exp -> NormalizeM Exp
insertBindings m = pass $ do
  (body, NewBindings binder) <- listen m
  return (binder body, const mempty)

normalizeFun :: FunDec -> NormalizeM FunDec
normalizeFun (fname, rettype, params, body, loc) = do
  body' <- insertBindings $ normalizeExp body
  return (fname, rettype, params, body', loc)

normalizeExp :: Exp -> NormalizeM Exp
normalizeExp (Var k) = return $ Var k
normalizeExp (LetPat pat e body loc) = do
  e' <- normalizeSubExps e
  body' <- insertBindings $ normalizeExp body
  return $ LetPat pat e' body' loc
normalizeExp (DoLoop mergepat mergeexp loopvar
              boundexp loopbody letbody loc) = do
  mergeexp' <- normalizeExp mergeexp
  boundexp' <- normalizeExp boundexp
  loopbody' <- insertBindings $ normalizeExp loopbody
  letbody'  <- insertBindings $ normalizeExp letbody
  return $ DoLoop mergepat mergeexp' loopvar boundexp' loopbody' letbody' loc
normalizeExp (LetWith cs dest src idxes ve body loc) = do
  idxes' <- mapM normalizeExp idxes
  ve'    <- normalizeExp ve
  body'  <- insertBindings $ normalizeExp body
  return $ LetWith cs dest src idxes' ve' body' loc
normalizeExp (If c te fe t loc) = do
  c'  <- normalizeExp c
  te' <- insertBindings $ normalizeExp te
  fe' <- insertBindings $ normalizeExp fe
  return $ If c' te' fe' t loc
normalizeExp e = Var <$> (replaceExp (nameHint e) =<< normalizeSubExps e)

-- | Leave the root of the expression as is, but normalise any
-- subexpressions.
normalizeSubExps :: Exp -> NormalizeM Exp
normalizeSubExps (If c te fe t loc) =
  -- Never normalise anything past a branch.
  normalizeExp $ If c te fe t loc
normalizeSubExps e = mapExpM normalize e
  where normalize = identityMapper {
                      mapOnExp = normalizeExp
                    , mapOnLambda = normalizeLambda
                    , mapOnTupleLambda = normalizeTupleLambda
                    }

normalizeLambda :: Lambda -> NormalizeM Lambda
normalizeLambda (CurryFun fname args rettype loc) = do
  args' <- mapM normalizeExp args
  return $ CurryFun fname args' rettype loc
normalizeLambda (AnonymFun params body rettype loc) = do
  body' <- insertBindings $ normalizeExp body
  return $ AnonymFun params body' rettype loc

normalizeTupleLambda :: TupleLambda -> NormalizeM TupleLambda
normalizeTupleLambda (TupleLambda params body rettype loc) = do
  body' <- insertBindings $ normalizeExp body
  return $ TupleLambda params body' rettype loc

-- | Generate a name appropriate for the variable used to replace the
-- given expression.  Only for readability purposes, so remove, modify
-- and add whichever cases you want.
nameHint :: Exp -> String
nameHint (LetPat {}) = "let"
nameHint (DoLoop {}) = "loop"
nameHint (LetWith {}) = "letwith"
nameHint (BinOp {}) = "bop"
nameHint (Not {}) = "not"
nameHint (Negate {}) = "negate"
nameHint (If {}) = "if"
nameHint (Size {}) = "size"
nameHint (Concat {}) = "concat"
nameHint (Split {}) = "split"
nameHint (Iota {}) = "iota"
nameHint _ = "norm"
