{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Trustworthy #-}

-- | Lambda-lifting of typed, monomorphic Futhark programs without
-- modules.  After this pass, the program will no longer contain any
-- 'LetFun's or 'Lambda's.
module Futhark.Internalise.LiftLambdas (transformProg) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import Data.List (partition)
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Set as S
import Futhark.IR.Pretty ()
import qualified Futhark.Internalise.FreeVars as FV
import Futhark.MonadFreshNames
import Language.Futhark
import Language.Futhark.Traversals

newtype Env = Env {envReplace :: M.Map VName Exp}

initialEnv :: Env
initialEnv = Env mempty

data LiftState = State
  { stateNameSource :: VNameSource,
    stateValBinds :: [ValBind],
    stateGlobal :: S.Set VName
  }

initialState :: VNameSource -> LiftState
initialState src = State src mempty $ S.fromList $ M.keys intrinsics

newtype LiftM a = LiftM (ReaderT Env (State LiftState) a)
  deriving (Functor, Applicative, Monad, MonadReader Env, MonadState LiftState)

instance MonadFreshNames LiftM where
  putNameSource src = modify $ \s -> s {stateNameSource = src}
  getNameSource = gets stateNameSource

runLiftM :: VNameSource -> LiftM () -> ([ValBind], VNameSource)
runLiftM src (LiftM m) =
  let s = execState (runReaderT m initialEnv) (initialState src)
   in (reverse (stateValBinds s), stateNameSource s)

addValBind :: ValBind -> LiftM ()
addValBind vb = modify $ \s ->
  s
    { stateValBinds = vb : stateValBinds s,
      stateGlobal = foldl' (flip S.insert) (stateGlobal s) names
    }
  where
    names = valBindName vb : snd (unInfo (valBindRetType vb))

replacing :: VName -> Exp -> LiftM a -> LiftM a
replacing v e = local $ \env ->
  env {envReplace = M.insert v e $ envReplace env}

existentials :: Exp -> S.Set VName
existentials e =
  let here = case e of
        AppExp (Apply _ _ (Info (_, pdim)) _) (Info res) ->
          S.fromList (maybeToList pdim ++ appResExt res)
        AppExp _ (Info res) ->
          S.fromList (appResExt res)
        _ ->
          mempty

      m = identityMapper {mapOnExp = \e' -> modify (<> existentials e') >> pure e'}
   in execState (astMap m e) here

liftFunction :: VName -> [TypeParam] -> [Pattern] -> StructRetType -> Exp -> LiftM Exp
liftFunction fname tparams params (RetType dims ret) funbody = do
  -- Find free variables
  global <- gets stateGlobal
  let bound =
        global
          <> foldMap patternNames params
          <> S.fromList (map typeParamName tparams)
          <> existentials funbody

      free =
        let immediate_free = FV.freeVars funbody `FV.without` bound
            sizes_in_free =
              foldMap typeDimNames $
                M.elems $ FV.unNameSet immediate_free
            sizes =
              FV.sizes $
                sizes_in_free
                  <> foldMap patternDimNames params
                  <> typeDimNames ret
         in M.toList $ FV.unNameSet $ immediate_free <> (sizes `FV.without` bound)

      -- Those parameters that correspond to sizes must come first.
      sizes_in_types =
        foldMap typeDimNames (ret : map snd free ++ map patternStructType params)
      isSize (v, _) = v `S.member` sizes_in_types
      (free_dims, free_nondims) = partition isSize free

      free_params =
        map (mkParam . second (`setUniqueness` Nonunique)) $
          free_dims ++ free_nondims

  addValBind $
    ValBind
      { valBindName = fname,
        valBindTypeParams = tparams,
        valBindParams = free_params ++ params,
        valBindRetDecl = Nothing,
        valBindRetType = Info (RetType dims ret, mempty),
        valBindBody = funbody,
        valBindDoc = Nothing,
        valBindAttrs = mempty,
        valBindLocation = mempty,
        valBindEntryPoint = Nothing
      }

  return $
    apply
      (Var (qualName fname) (Info (augType $ free_dims ++ free_nondims)) mempty)
      $ free_dims ++ free_nondims
  where
    orig_type = funType params $ RetType dims ret
    mkParam (v, t) = Id v (Info (fromStruct t)) mempty
    freeVar (v, t) = Var (qualName v) (Info (fromStruct t)) mempty
    augType rem_free = fromStruct $ funType (map mkParam rem_free) $ RetType [] orig_type

    apply :: Exp -> [(VName, StructType)] -> Exp
    apply f [] = f
    apply f (p : rem_ps) =
      let inner_ret = AppRes (fromStruct (augType rem_ps)) mempty
          inner = AppExp (Apply f (freeVar p) (Info (Observe, Nothing)) mempty) (Info inner_ret)
       in apply inner rem_ps

transformExp :: Exp -> LiftM Exp
transformExp (AppExp (LetFun fname (tparams, params, _, Info ret, funbody) body _) _) = do
  funbody' <- transformExp funbody
  fname' <- newVName $ "lifted_" ++ baseString fname
  lifted_call <- liftFunction fname' tparams params ret funbody'
  replacing fname lifted_call $ transformExp body
transformExp (Lambda params body _ (Info (_, ret)) _) = do
  body' <- transformExp body
  fname <- newVName "lifted_lambda"
  liftFunction fname [] params ret body'
transformExp e@(Var v _ _) =
  -- Note that function-typed variables can only occur in expressions,
  -- not in other places where VNames/QualNames can occur.
  asks (fromMaybe e . M.lookup (qualLeaf v) . envReplace)
transformExp e =
  astMap m e
  where
    m = identityMapper {mapOnExp = transformExp}

transformValBind :: ValBind -> LiftM ()
transformValBind vb = do
  e <- transformExp $ valBindBody vb
  addValBind $ vb {valBindBody = e}

{-# NOINLINE transformProg #-}

-- | Perform the transformation.
transformProg :: MonadFreshNames m => [ValBind] -> m [ValBind]
transformProg vbinds =
  modifyNameSource $ \namesrc ->
    runLiftM namesrc $ mapM_ transformValBind vbinds
