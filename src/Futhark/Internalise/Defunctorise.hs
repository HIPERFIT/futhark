{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Trustworthy #-}

-- | Partially evaluate all modules away from a source Futhark
-- program.  This is implemented as a source-to-source transformation.
module Futhark.Internalise.Defunctorise (transformProg) where

import Control.Monad.Identity
import Control.Monad.RWS.Strict
import qualified Data.DList as DL
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S
import Futhark.MonadFreshNames
import Language.Futhark
import Language.Futhark.Semantic (FileModule (..), Imports)
import Language.Futhark.Traversals
import Prelude hiding (abs, mod)

-- | A substitution from names in the original program to names in the
-- generated/residual program.
type Substitutions = M.Map VName VName

lookupSubst :: VName -> Substitutions -> VName
lookupSubst v substs = case M.lookup v substs of
  Just v' | v' /= v -> lookupSubst v' substs
  _ -> v

data Mod
  = -- | A pairing of a lexical closure and a module function.
    ModFun TySet Scope ModParam ModExp
  | -- | A non-parametric module.
    ModMod Scope
  deriving (Show)

modScope :: Mod -> Scope
modScope (ModMod scope) = scope
modScope ModFun {} = mempty

data Scope = Scope
  { scopeSubsts :: Substitutions,
    scopeMods :: M.Map VName Mod
  }
  deriving (Show)

lookupSubstInScope :: QualName VName -> Scope -> (QualName VName, Scope)
lookupSubstInScope qn@(QualName quals name) scope@(Scope substs mods) =
  case quals of
    [] -> (qualName $ lookupSubst name substs, scope)
    q : qs ->
      let q' = lookupSubst q substs
       in case M.lookup q' mods of
            Just (ModMod mod_scope) -> lookupSubstInScope (QualName qs name) mod_scope
            _ -> (qn, scope)

instance Semigroup Scope where
  Scope ss1 mt1 <> Scope ss2 mt2 = Scope (ss1 <> ss2) (mt1 <> mt2)

instance Monoid Scope where
  mempty = Scope mempty mempty

type TySet = S.Set VName

data Env = Env
  { envScope :: Scope,
    envGenerating :: Bool,
    envImports :: M.Map String Scope,
    envAbs :: TySet
  }

newtype TransformM a = TransformM (RWS Env (DL.DList Dec) VNameSource a)
  deriving
    ( Applicative,
      Functor,
      Monad,
      MonadFreshNames,
      MonadReader Env,
      MonadWriter (DL.DList Dec)
    )

emit :: Dec -> TransformM ()
emit = tell . DL.singleton

askScope :: TransformM Scope
askScope = asks envScope

localScope :: (Scope -> Scope) -> TransformM a -> TransformM a
localScope f = local $ \env -> env {envScope = f $ envScope env}

extendScope :: Scope -> TransformM a -> TransformM a
extendScope (Scope substs mods) = localScope $ \scope ->
  scope
    { scopeSubsts = M.map (forward (scopeSubsts scope)) substs <> scopeSubsts scope,
      scopeMods = mods <> scopeMods scope
    }
  where
    forward old_substs v = fromMaybe v $ M.lookup v old_substs

substituting :: Substitutions -> TransformM a -> TransformM a
substituting substs = extendScope mempty {scopeSubsts = substs}

boundName :: VName -> TransformM VName
boundName v = do
  g <- asks envGenerating
  if g then newName v else return v

bindingNames :: [VName] -> TransformM Scope -> TransformM Scope
bindingNames names m = do
  names' <- mapM boundName names
  let substs = M.fromList (zip names names')
  substituting substs $ mappend <$> m <*> pure (Scope substs mempty)

generating :: TransformM a -> TransformM a
generating = local $ \env -> env {envGenerating = True}

bindingImport :: String -> Scope -> TransformM a -> TransformM a
bindingImport name scope = local $ \env ->
  env {envImports = M.insert name scope $ envImports env}

bindingAbs :: TySet -> TransformM a -> TransformM a
bindingAbs abs = local $ \env ->
  env {envAbs = abs <> envAbs env}

lookupImport :: String -> TransformM Scope
lookupImport name = maybe bad return =<< asks (M.lookup name . envImports)
  where
    bad = error $ "Unknown import: " ++ name

lookupMod' :: QualName VName -> Scope -> Either String Mod
lookupMod' mname scope =
  let (mname', scope') = lookupSubstInScope mname scope
   in maybe (Left $ bad mname') Right $ M.lookup (qualLeaf mname') $ scopeMods scope'
  where
    bad mname' = "Unknown module: " ++ pretty mname ++ " (" ++ pretty mname' ++ ")"

lookupMod :: QualName VName -> TransformM Mod
lookupMod mname = either error return . lookupMod' mname =<< askScope

runTransformM :: VNameSource -> TransformM a -> (a, VNameSource, DL.DList Dec)
runTransformM src (TransformM m) = runRWS m env src
  where
    env = Env mempty False mempty mempty

maybeAscript ::
  SrcLoc ->
  Maybe (SigExp, Info (M.Map VName VName)) ->
  ModExp ->
  ModExp
maybeAscript loc (Just (mtye, substs)) me = ModAscript me mtye substs loc
maybeAscript _ Nothing me = me

substituteInMod :: Substitutions -> Mod -> Mod
substituteInMod substs (ModMod (Scope mod_substs mod_mods)) =
  -- Forward all substitutions.
  ModMod $ Scope substs' $ M.map (substituteInMod substs) mod_mods
  where
    forward v = lookupSubst v $ mod_substs <> substs
    substs' = M.map forward substs
substituteInMod substs (ModFun abs (Scope mod_substs mod_mods) mparam mbody) =
  ModFun abs (Scope (substs' <> mod_substs) mod_mods) mparam mbody
  where
    forward v = lookupSubst v mod_substs
    substs' = M.map forward substs

extendAbsTypes :: Substitutions -> TransformM a -> TransformM a
extendAbsTypes ascript_substs m = do
  abs <- asks envAbs
  -- Some abstract types may have a different name on the inside, and
  -- we need to make them visible, because substitutions involving
  -- abstract types must be lifted out in transformModBind.
  let subst_abs =
        S.fromList $
          map snd $
            filter ((`S.member` abs) . fst) $
              M.toList ascript_substs
  bindingAbs subst_abs m

evalModExp :: ModExp -> TransformM Mod
evalModExp (ModVar qn _) = lookupMod qn
evalModExp (ModParens e _) = evalModExp e
evalModExp (ModDecs decs _) = ModMod <$> transformDecs decs
evalModExp (ModImport _ (Info fpath) _) = ModMod <$> lookupImport fpath
evalModExp (ModAscript me _ (Info ascript_substs) _) =
  extendAbsTypes ascript_substs $
    substituteInMod ascript_substs <$> evalModExp me
evalModExp (ModApply f arg (Info p_substs) (Info b_substs) loc) = do
  f_mod <- evalModExp f
  arg_mod <- evalModExp arg
  case f_mod of
    ModMod _ ->
      error $ "Cannot apply non-parametric module at " ++ locStr loc
    ModFun f_abs f_closure f_p f_body ->
      bindingAbs (f_abs <> S.fromList (unInfo (modParamAbs f_p)))
        . extendAbsTypes b_substs
        . extendScope f_closure
        . generating
        $ do
          outer_substs <- scopeSubsts <$> askScope
          abs <- asks envAbs
          let forward (k, v) = (lookupSubst k outer_substs, v)
              p_substs' = M.fromList $ map forward $ M.toList p_substs
              keep k _ =
                k `M.member` p_substs'
                  || k `S.member` abs
              abs_substs =
                M.filterWithKey keep $
                  M.map (`lookupSubst` scopeSubsts (modScope arg_mod)) p_substs'
                    <> scopeSubsts f_closure
                    <> scopeSubsts (modScope arg_mod)
          extendScope
            ( Scope
                abs_substs
                ( M.singleton (modParamName f_p) $
                    substituteInMod p_substs' arg_mod
                )
            )
            $ do
              substs <- scopeSubsts <$> askScope
              x <- evalModExp f_body
              return $
                addSubsts abs abs_substs $
                  -- The next one is dubious, but is necessary to
                  -- propagate substitutions from the argument (see
                  -- modules/functor24.fut).
                  addSubstsModMod (scopeSubsts $ modScope arg_mod) $
                    substituteInMod (b_substs <> substs) x
  where
    addSubsts abs substs (ModFun mabs (Scope msubsts mods) mp me) =
      ModFun (abs <> mabs) (Scope (substs <> msubsts) mods) mp me
    addSubsts _ substs (ModMod (Scope msubsts mods)) =
      ModMod $ Scope (substs <> msubsts) mods
    addSubstsModMod substs (ModMod (Scope msubsts mods)) =
      ModMod $ Scope (substs <> msubsts) mods
    addSubstsModMod _ m = m
evalModExp (ModLambda p ascript e loc) = do
  scope <- askScope
  abs <- asks envAbs
  return $ ModFun abs scope p $ maybeAscript loc ascript e

transformName :: VName -> TransformM VName
transformName v = lookupSubst v . scopeSubsts <$> askScope

-- | A general-purpose substitution of names.
transformNames :: ASTMappable x => x -> TransformM x
transformNames x = do
  scope <- askScope
  return $ runIdentity $ astMap (substituter scope) x
  where
    substituter scope =
      ASTMapper
        { mapOnExp = onExp scope,
          mapOnName = \v ->
            return $ qualLeaf $ fst $ lookupSubstInScope (qualName v) scope,
          mapOnQualName = \v ->
            return $ fst $ lookupSubstInScope v scope,
          mapOnStructType = astMap (substituter scope),
          mapOnPatternType = astMap (substituter scope),
          mapOnStructRetType = astMap (substituter scope),
          mapOnPatternRetType = astMap (substituter scope)
        }
    onExp scope e =
      -- One expression is tricky, because it interacts with scoping rules.
      case e of
        QualParens (mn, _) e' _ ->
          case lookupMod' mn scope of
            Left err -> error err
            Right mod ->
              astMap (substituter $ modScope mod <> scope) e'
        _ -> astMap (substituter scope) e

transformTypeExp :: TypeExp VName -> TransformM (TypeExp VName)
transformTypeExp = transformNames

transformStructType :: StructType -> TransformM StructType
transformStructType = transformNames

transformExp :: Exp -> TransformM Exp
transformExp = transformNames

transformValBind :: ValBind -> TransformM ()
transformValBind (ValBind entry name tdecl (Info (RetType dims t, retext)) tparams params e doc attrs loc) = do
  name' <- transformName name
  tdecl' <- traverse transformTypeExp tdecl
  t' <- transformStructType t
  e' <- transformExp e
  tparams' <- traverse transformNames tparams
  params' <- traverse transformNames params
  emit $ ValDec $ ValBind entry name' tdecl' (Info (RetType dims t', retext)) tparams' params' e' doc attrs loc

transformTypeDecl :: TypeDecl -> TransformM TypeDecl
transformTypeDecl (TypeDecl dt (Info et)) =
  TypeDecl <$> transformTypeExp dt <*> (Info <$> transformStructType et)

transformTypeBind :: TypeBind -> TransformM ()
transformTypeBind (TypeBind name l tparams te (Info (RetType dims t)) doc loc) = do
  name' <- transformName name
  emit . TypeDec
    =<< ( TypeBind name' l <$> traverse transformNames tparams
            <*> transformTypeExp te
            <*> (Info . RetType dims <$> transformStructType t)
            <*> pure doc
            <*> pure loc
        )

transformModBind :: ModBind -> TransformM Scope
transformModBind mb = do
  let addParam p me = ModLambda p Nothing me $ srclocOf me
  mod <-
    evalModExp $
      foldr
        addParam
        (maybeAscript (srclocOf mb) (modSignature mb) $ modExp mb)
        $ modParams mb
  mname <- transformName $ modName mb
  abs <- asks envAbs
  -- Copy substitutions involving abstract types out, because they are
  -- always resolved at the outermost level.
  let abs_substs =
        M.filterWithKey (const . flip S.member abs) $
          scopeSubsts $ modScope mod
  return $ Scope abs_substs $ M.singleton mname mod

transformDecs :: [Dec] -> TransformM Scope
transformDecs ds =
  case ds of
    [] ->
      return mempty
    LocalDec d _ : ds' ->
      transformDecs $ d : ds'
    ValDec fdec : ds' ->
      bindingNames [valBindName fdec] $ do
        transformValBind fdec
        transformDecs ds'
    TypeDec tb : ds' ->
      bindingNames [typeAlias tb] $ do
        transformTypeBind tb
        transformDecs ds'
    SigDec {} : ds' ->
      transformDecs ds'
    ModDec mb : ds' ->
      bindingNames [modName mb] $ do
        mod_scope <- transformModBind mb
        extendScope mod_scope $ mappend <$> transformDecs ds' <*> pure mod_scope
    OpenDec e _ : ds' -> do
      scope <- modScope <$> evalModExp e
      extendScope scope $ mappend <$> transformDecs ds' <*> pure scope
    ImportDec name name' loc : ds' ->
      let d = LocalDec (OpenDec (ModImport name name' loc) loc) loc
       in transformDecs $ d : ds'

transformImports :: Imports -> TransformM ()
transformImports [] = return ()
transformImports ((name, imp) : imps) = do
  let abs = S.fromList $ map qualLeaf $ M.keys $ fileAbs imp
  scope <-
    censor (fmap maybeHideEntryPoint) $
      bindingAbs abs $ transformDecs $ progDecs $ fileProg imp
  bindingAbs abs $ bindingImport name scope $ transformImports imps
  where
    -- Only the "main" file (last import) is allowed to have entry points.
    permit_entry_points = null imps

    maybeHideEntryPoint (ValDec vdec) =
      ValDec
        vdec
          { valBindEntryPoint =
              if permit_entry_points
                then valBindEntryPoint vdec
                else Nothing
          }
    maybeHideEntryPoint d = d

-- | Perform defunctorisation.
transformProg :: MonadFreshNames m => Imports -> m [Dec]
transformProg prog = modifyNameSource $ \namesrc ->
  let ((), namesrc', prog') = runTransformM namesrc $ transformImports prog
   in (DL.toList prog', namesrc')
