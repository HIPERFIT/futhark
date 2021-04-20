{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Implementation of the Futhark module system (at least most of it;
-- some is scattered elsewhere in the type checker).
module Language.Futhark.TypeChecker.Modules
  ( matchMTys,
    newNamesForMTy,
    refineEnv,
    applyFunctor,
  )
where

import Control.Monad.Except
import Control.Monad.Writer hiding (Sum)
import Data.Either
import Data.List (intersect)
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Ord
import qualified Data.Set as S
import Futhark.Util.Pretty
import Language.Futhark
import Language.Futhark.Semantic
import Language.Futhark.TypeChecker.Monad
import Language.Futhark.TypeChecker.Types
import Language.Futhark.TypeChecker.Unify (doUnification)
import Prelude hiding (abs, mod)

substituteTypesInMod :: TypeSubs -> Mod -> Mod
substituteTypesInMod substs (ModEnv e) =
  ModEnv $ substituteTypesInEnv substs e
substituteTypesInMod substs (ModFun (FunSig abs mod mty)) =
  ModFun $ FunSig abs (substituteTypesInMod substs mod) (substituteTypesInMTy substs mty)

substituteTypesInMTy :: TypeSubs -> MTy -> MTy
substituteTypesInMTy substs (MTy abs mod) = MTy abs $ substituteTypesInMod substs mod

substituteTypesInEnv :: TypeSubs -> Env -> Env
substituteTypesInEnv substs env =
  env
    { envVtable = M.map (substituteTypesInBoundV substs) $ envVtable env,
      envTypeTable = M.mapWithKey subT $ envTypeTable env,
      envModTable = M.map (substituteTypesInMod substs) $ envModTable env
    }
  where
    subT name (TypeAbbr l _ _)
      | Just (Subst ps rt) <- substs name = TypeAbbr l ps rt
    subT _ (TypeAbbr l ps (RetType dims t)) =
      TypeAbbr l ps $ RetType dims $ applySubst substs t

substituteTypesInBoundV :: TypeSubs -> BoundV -> BoundV
substituteTypesInBoundV substs (BoundV tps t) =
  BoundV tps (applySubst substs t)

-- | All names defined anywhere in the 'Env'.
allNamesInEnv :: Env -> S.Set VName
allNamesInEnv (Env vtable ttable stable modtable _names) =
  S.fromList
    ( M.keys vtable ++ M.keys ttable
        ++ M.keys stable
        ++ M.keys modtable
    )
    <> mconcat
      ( map allNamesInMTy (M.elems stable)
          ++ map allNamesInMod (M.elems modtable)
          ++ map allNamesInType (M.elems ttable)
      )
  where
    allNamesInType (TypeAbbr _ ps _) = S.fromList $ map typeParamName ps

allNamesInMod :: Mod -> S.Set VName
allNamesInMod (ModEnv env) = allNamesInEnv env
allNamesInMod ModFun {} = mempty

allNamesInMTy :: MTy -> S.Set VName
allNamesInMTy (MTy abs mod) =
  S.fromList (map qualLeaf $ M.keys abs) <> allNamesInMod mod

-- | Create unique renames for the module type.  This is used for
-- e.g. generative functor application.
newNamesForMTy :: MTy -> TypeM (MTy, M.Map VName VName)
newNamesForMTy orig_mty = do
  pairs <- forM (S.toList $ allNamesInMTy orig_mty) $ \v -> do
    v' <- newName v
    return (v, v')
  let substs = M.fromList pairs
      rev_substs = M.fromList $ map (uncurry $ flip (,)) pairs

  return (substituteInMTy substs orig_mty, rev_substs)
  where
    substituteInMTy :: M.Map VName VName -> MTy -> MTy
    substituteInMTy substs (MTy mty_abs mty_mod) =
      MTy (M.mapKeys (fmap substitute) mty_abs) (substituteInMod mty_mod)
      where
        substituteInEnv (Env vtable ttable _stable modtable names) =
          let vtable' = substituteInMap substituteInBinding vtable
              ttable' = substituteInMap substituteInTypeBinding ttable
              mtable' = substituteInMap substituteInMod modtable
           in Env
                { envVtable = vtable',
                  envTypeTable = ttable',
                  envSigTable = mempty,
                  envModTable = mtable',
                  envNameMap = M.map (fmap substitute) names
                }

        substitute v =
          fromMaybe v $ M.lookup v substs

        substituteInMap f m =
          let (ks, vs) = unzip $ M.toList m
           in M.fromList $
                zip
                  (map (\k -> fromMaybe k $ M.lookup k substs) ks)
                  (map f vs)

        substituteInBinding (BoundV ps t) =
          BoundV (map substituteInTypeParam ps) (substituteInType t)

        substituteInMod (ModEnv env) =
          ModEnv $ substituteInEnv env
        substituteInMod (ModFun funsig) =
          ModFun $ substituteInFunSig funsig

        substituteInFunSig (FunSig abs mod mty) =
          FunSig
            (M.mapKeys (fmap substitute) abs)
            (substituteInMod mod)
            (substituteInMTy substs mty)

        substituteInTypeBinding (TypeAbbr l ps (RetType dims t)) =
          TypeAbbr l (map substituteInTypeParam ps) $ RetType dims $ substituteInType t

        substituteInTypeParam (TypeParamDim p loc) =
          TypeParamDim (substitute p) loc
        substituteInTypeParam (TypeParamType l p loc) =
          TypeParamType l (substitute p) loc

        substituteInType :: StructType -> StructType
        substituteInType (Scalar (TypeVar () u (TypeName qs v) targs)) =
          Scalar $
            TypeVar () u (TypeName (map substitute qs) $ substitute v) $
              map substituteInTypeArg targs
        substituteInType (Scalar (Prim t)) =
          Scalar $ Prim t
        substituteInType (Scalar (Record ts)) =
          Scalar $ Record $ fmap substituteInType ts
        substituteInType (Scalar (Sum ts)) =
          Scalar $ Sum $ (fmap . fmap) substituteInType ts
        substituteInType (Array () u t shape) =
          arrayOf (substituteInType $ Scalar t) (substituteInShape shape) u
        substituteInType (Scalar (Arrow als v t1 (RetType dims t2))) =
          Scalar $ Arrow als v (substituteInType t1) $ RetType dims $ substituteInType t2

        substituteInShape (ShapeDecl ds) =
          ShapeDecl $ map substituteInDim ds
        substituteInDim (NamedDim (QualName qs v)) =
          NamedDim $ QualName (map substitute qs) $ substitute v
        substituteInDim d = d

        substituteInTypeArg (TypeArgDim (NamedDim (QualName qs v)) loc) =
          TypeArgDim (NamedDim $ QualName (map substitute qs) $ substitute v) loc
        substituteInTypeArg (TypeArgDim (ConstDim x) loc) =
          TypeArgDim (ConstDim x) loc
        substituteInTypeArg (TypeArgType t loc) =
          TypeArgType (substituteInType t) loc

mtyTypeAbbrs :: MTy -> M.Map VName TypeBinding
mtyTypeAbbrs (MTy _ mod) = modTypeAbbrs mod

modTypeAbbrs :: Mod -> M.Map VName TypeBinding
modTypeAbbrs (ModEnv env) =
  envTypeAbbrs env
modTypeAbbrs (ModFun (FunSig _ mod mty)) =
  modTypeAbbrs mod <> mtyTypeAbbrs mty

envTypeAbbrs :: Env -> M.Map VName TypeBinding
envTypeAbbrs env =
  envTypeTable env
    <> (mconcat . map modTypeAbbrs . M.elems . envModTable) env

-- | Refine the given type name in the given env.
refineEnv ::
  SrcLoc ->
  TySet ->
  Env ->
  QualName Name ->
  [TypeParam] ->
  StructType ->
  TypeM (QualName VName, TySet, Env)
refineEnv loc tset env tname ps t
  | Just (tname', TypeAbbr _ cur_ps (RetType _ (Scalar (TypeVar () _ (TypeName qs v) _)))) <-
      findTypeDef tname (ModEnv env),
    QualName (qualQuals tname') v `M.member` tset =
    if paramsMatch cur_ps ps
      then
        return
          ( tname',
            QualName qs v `M.delete` tset,
            substituteTypesInEnv
              ( flip M.lookup $
                  M.fromList
                    [ (qualLeaf tname', Subst cur_ps $ RetType [] t),
                      (v, Subst ps $ RetType [] t)
                    ]
              )
              env
          )
      else
        typeError loc mempty $
          "Cannot refine a type having"
            <+> tpMsg ps <> " with a type having " <> tpMsg cur_ps <> "."
  | otherwise =
    typeError loc mempty $ ppr tname <+> "is not an abstract type in the module type."
  where
    tpMsg [] = "no type parameters"
    tpMsg xs = "type parameters" <+> spread (map ppr xs)

paramsMatch :: [TypeParam] -> [TypeParam] -> Bool
paramsMatch ps1 ps2 = length ps1 == length ps2 && all match (zip ps1 ps2)
  where
    match (TypeParamType l1 _ _, TypeParamType l2 _ _) = l1 <= l2
    match (TypeParamDim _ _, TypeParamDim _ _) = True
    match _ = False

findBinding ::
  (Env -> M.Map VName v) ->
  Namespace ->
  Name ->
  Env ->
  Maybe (VName, v)
findBinding table namespace name the_env = do
  QualName _ name' <- M.lookup (namespace, name) $ envNameMap the_env
  (name',) <$> M.lookup name' (table the_env)

findTypeDef :: QualName Name -> Mod -> Maybe (QualName VName, TypeBinding)
findTypeDef _ ModFun {} = Nothing
findTypeDef (QualName [] name) (ModEnv the_env) = do
  (name', tb) <- findBinding envTypeTable Type name the_env
  return (qualName name', tb)
findTypeDef (QualName (q : qs) name) (ModEnv the_env) = do
  (q', q_mod) <- findBinding envModTable Term q the_env
  (QualName qs' name', tb) <- findTypeDef (QualName qs name) q_mod
  return (QualName (q' : qs') name', tb)

resolveAbsTypes ::
  TySet ->
  Mod ->
  TySet ->
  SrcLoc ->
  Either TypeError (M.Map VName (QualName VName, TypeBinding))
resolveAbsTypes mod_abs mod sig_abs loc = do
  let abs_mapping =
        M.fromList $
          zip
            (map (fmap baseName . fst) $ M.toList mod_abs)
            (M.toList mod_abs)
  fmap M.fromList $
    forM (M.toList sig_abs) $ \(name, name_l) ->
      case findTypeDef (fmap baseName name) mod of
        Just (name', TypeAbbr mod_l ps t)
          | mod_l > name_l ->
            mismatchedLiftedness
              name_l
              (map qualLeaf $ M.keys mod_abs)
              (qualLeaf name)
              (mod_l, ps, t)
          | name_l < SizeLifted,
            not $ null $ retDims t ->
            anonymousSizes
              (map qualLeaf $ M.keys mod_abs)
              (qualLeaf name)
              (mod_l, ps, t)
          | Just (abs_name, _) <- M.lookup (fmap baseName name) abs_mapping ->
            return (qualLeaf name, (abs_name, TypeAbbr name_l ps t))
          | otherwise ->
            return (qualLeaf name, (name', TypeAbbr name_l ps t))
        _ ->
          missingType loc $ fmap baseName name
  where
    mismatchedLiftedness name_l abs name mod_t =
      Left $
        TypeError loc mempty $
          "Module defines"
            </> indent 2 (ppTypeAbbr abs name mod_t)
            </> "but module type requires" <+> text what <> "."
      where
        what = case name_l of
          Unlifted -> "a non-lifted type"
          SizeLifted -> "a size-lifted type"
          Lifted -> "a lifted type"

    anonymousSizes abs name mod_t =
      Left $
        TypeError loc mempty $
          "Module defines"
            </> indent 2 (ppTypeAbbr abs name mod_t)
            </> "which contains anonymous sizes, but module type requires non-lifted type."

resolveMTyNames ::
  MTy ->
  MTy ->
  M.Map VName (QualName VName)
resolveMTyNames = resolveMTyNames'
  where
    resolveMTyNames' (MTy _mod_abs mod) (MTy _sig_abs sig) =
      resolveModNames mod sig

    resolveModNames (ModEnv mod_env) (ModEnv sig_env) =
      resolveEnvNames mod_env sig_env
    resolveModNames (ModFun mod_fun) (ModFun sig_fun) =
      resolveModNames (funSigMod mod_fun) (funSigMod sig_fun)
        <> resolveMTyNames' (funSigMty mod_fun) (funSigMty sig_fun)
    resolveModNames _ _ =
      mempty

    resolveEnvNames mod_env sig_env =
      let mod_substs = resolve Term mod_env $ envModTable sig_env
          onMod (modname, mod_env_mod) =
            case M.lookup modname mod_substs of
              Just (QualName _ modname')
                | Just sig_env_mod <-
                    M.lookup modname' $ envModTable mod_env ->
                  resolveModNames sig_env_mod mod_env_mod
              _ -> mempty
       in mconcat
            [ resolve Term mod_env $ envVtable sig_env,
              resolve Type mod_env $ envVtable sig_env,
              resolve Signature mod_env $ envVtable sig_env,
              mod_substs,
              mconcat $ map onMod $ M.toList $ envModTable sig_env
            ]

    resolve namespace mod_env = M.mapMaybeWithKey resolve'
      where
        resolve' name _ =
          M.lookup (namespace, baseName name) $ envNameMap mod_env

missingType :: Pretty a => SrcLoc -> a -> Either TypeError b
missingType loc name =
  Left $
    TypeError loc mempty $
      "Module does not define a type named" <+> ppr name <> "."

missingVal :: Pretty a => SrcLoc -> a -> Either TypeError b
missingVal loc name =
  Left $
    TypeError loc mempty $
      "Module does not define a value named" <+> ppr name <> "."

missingMod :: Pretty a => SrcLoc -> a -> Either TypeError b
missingMod loc name =
  Left $
    TypeError loc mempty $
      "Module does not define a module named" <+> ppr name <> "."

mismatchedType ::
  SrcLoc ->
  [VName] ->
  VName ->
  (Liftedness, [TypeParam], StructRetType) ->
  (Liftedness, [TypeParam], StructRetType) ->
  Either TypeError b
mismatchedType loc abs name spec_t env_t =
  Left $
    TypeError loc mempty $
      "Module defines"
        </> indent 2 (ppTypeAbbr abs name env_t)
        </> "but module type requires"
        </> indent 2 (ppTypeAbbr abs name spec_t)

ppTypeAbbr :: [VName] -> VName -> (Liftedness, [TypeParam], StructRetType) -> Doc
ppTypeAbbr abs name (l, ps, (RetType [] (Scalar (TypeVar () _ tn args))))
  | typeLeaf tn `elem` abs,
    map typeParamToArg ps == args =
    "type" <> ppr l <+> pprName name
      <+> spread (map ppr ps)
ppTypeAbbr _ name (l, ps, t) =
  "type" <> ppr l <+> pprName name
    <+> spread (map ppr ps)
    <+> equals
    <+/> nest 2 (align (ppr t))

-- | Return new renamed/abstracted env, as well as a mapping from
-- names in the signature to names in the new env.  This is used for
-- functor application.  The first env is the module env, and the
-- second the env it must match.
matchMTys ::
  MTy ->
  MTy ->
  SrcLoc ->
  Either TypeError (M.Map VName VName)
matchMTys orig_mty orig_mty_sig =
  matchMTys'
    (M.map (SizeSubst . NamedDim) $ resolveMTyNames orig_mty orig_mty_sig)
    orig_mty
    orig_mty_sig
  where
    matchMTys' ::
      M.Map VName (Subst StructRetType) ->
      MTy ->
      MTy ->
      SrcLoc ->
      Either TypeError (M.Map VName VName)

    matchMTys' _ (MTy _ ModFun {}) (MTy _ ModEnv {}) loc =
      Left $
        TypeError
          loc
          mempty
          "Cannot match parametric module with non-parametric module type."
    matchMTys' _ (MTy _ ModEnv {}) (MTy _ ModFun {}) loc =
      Left $
        TypeError
          loc
          mempty
          "Cannot match non-parametric module with paramatric module type."
    matchMTys' old_abs_subst_to_type (MTy mod_abs mod) (MTy sig_abs sig) loc = do
      -- Check that abstract types in 'sig' have an implementation in
      -- 'mod'.  This also gives us a substitution that we use to check
      -- the types of values.
      abs_substs <- resolveAbsTypes mod_abs mod sig_abs loc

      let abs_subst_to_type =
            old_abs_subst_to_type <> M.map (substFromAbbr . snd) abs_substs
          abs_name_substs = M.map (qualLeaf . fst) abs_substs
      substs <- matchMods abs_subst_to_type mod sig loc
      return (substs <> abs_name_substs)

    matchMods ::
      M.Map VName (Subst StructRetType) ->
      Mod ->
      Mod ->
      SrcLoc ->
      Either TypeError (M.Map VName VName)
    matchMods _ ModEnv {} ModFun {} loc =
      Left $
        TypeError
          loc
          mempty
          "Cannot match non-parametric module with parametric module type."
    matchMods _ ModFun {} ModEnv {} loc =
      Left $
        TypeError
          loc
          mempty
          "Cannot match parametric module with non-parametric module type."
    matchMods abs_subst_to_type (ModEnv mod) (ModEnv sig) loc =
      matchEnvs abs_subst_to_type mod sig loc
    matchMods
      old_abs_subst_to_type
      (ModFun (FunSig mod_abs mod_pmod mod_mod))
      (ModFun (FunSig sig_abs sig_pmod sig_mod))
      loc = do
        abs_substs <- resolveAbsTypes mod_abs mod_pmod sig_abs loc
        let abs_subst_to_type =
              old_abs_subst_to_type <> M.map (substFromAbbr . snd) abs_substs
            abs_name_substs = M.map (qualLeaf . fst) abs_substs
        pmod_substs <- matchMods abs_subst_to_type mod_pmod sig_pmod loc
        mod_substs <- matchMTys' abs_subst_to_type mod_mod sig_mod loc
        return (pmod_substs <> mod_substs <> abs_name_substs)

    matchEnvs ::
      M.Map VName (Subst StructRetType) ->
      Env ->
      Env ->
      SrcLoc ->
      Either TypeError (M.Map VName VName)
    matchEnvs abs_subst_to_type env sig loc = do
      -- XXX: we only want to create substitutions for visible names.
      -- This must be wrong in some cases.  Probably we need to
      -- rethink how we do shadowing for module types.
      let visible = S.fromList $ map qualLeaf $ M.elems $ envNameMap sig
          isVisible name = name `S.member` visible

      -- Check that all type abbreviations are correctly defined.
      abbr_name_substs <- fmap M.fromList $
        forM
          ( filter (isVisible . fst) $
              M.toList $
                envTypeTable sig
          )
          $ \(name, TypeAbbr spec_l spec_ps spec_t) ->
            case findBinding envTypeTable Type (baseName name) env of
              Just (name', TypeAbbr l ps t) ->
                matchTypeAbbr loc abs_subst_to_type name spec_l spec_ps spec_t name' l ps t
              Nothing -> missingType loc $ baseName name

      -- Check that all values are defined correctly, substituting the
      -- abstract types first.
      val_substs <- fmap M.fromList $
        forM (M.toList $ envVtable sig) $ \(name, spec_bv) -> do
          let spec_bv' = substituteTypesInBoundV (`M.lookup` abs_subst_to_type) spec_bv
          case findBinding envVtable Term (baseName name) env of
            Just (name', bv) -> matchVal loc name spec_bv' name' bv
            _ -> missingVal loc (baseName name)

      -- Check for correct modules.
      mod_substs <- fmap M.unions $
        forM (M.toList $ envModTable sig) $ \(name, modspec) ->
          case findBinding envModTable Term (baseName name) env of
            Just (name', mod) ->
              M.insert name name' <$> matchMods abs_subst_to_type mod modspec loc
            Nothing ->
              missingMod loc $ baseName name

      return $ val_substs <> mod_substs <> abbr_name_substs

    matchTypeAbbr ::
      SrcLoc ->
      M.Map VName (Subst StructRetType) ->
      VName ->
      Liftedness ->
      [TypeParam] ->
      StructRetType ->
      VName ->
      Liftedness ->
      [TypeParam] ->
      StructRetType ->
      Either TypeError (VName, VName)
    matchTypeAbbr loc abs_subst_to_type spec_name spec_l spec_ps (RetType spec_t_dims spec_t) name l ps (RetType t_dims t) = do
      -- We have to create substitutions for the type parameters, too.
      unless (length spec_ps == length ps) $ nomatch $ RetType spec_t_dims spec_t
      param_substs <-
        mconcat <$> zipWithM (matchTypeParam (nomatch (RetType spec_t_dims spec_t))) spec_ps ps

      -- Abstract types have a particular restriction to ensure that
      -- if we have a value of an abstract type 't [n]', then there is
      -- an array of size 'n' somewhere inside.
      when (M.member spec_name abs_subst_to_type) $
        case S.toList (mustBeExplicitInType t) `intersect` map typeParamName ps of
          [] -> return ()
          d : _ ->
            Left . TypeError loc mempty $
              "Type"
                </> indent 2 (ppTypeAbbr [] name (l, ps, RetType t_dims t))
                </> textwrap "cannot be made abstract because size parameter"
                <+/> pquote (pprName d)
                <+/> textwrap "is not used as an array size in the definition."

      let spec_t' = applySubst (`M.lookup` (param_substs <> abs_subst_to_type)) spec_t
      if spec_t' == t
        then return (spec_name, name)
        else nomatch $ RetType spec_t_dims spec_t'
      where
        nomatch spec_t' =
          mismatchedType
            loc
            (M.keys abs_subst_to_type)
            spec_name
            (spec_l, spec_ps, spec_t')
            (l, ps, RetType spec_t_dims spec_t)

    matchTypeParam _ (TypeParamDim x _) (TypeParamDim y _) =
      pure $ M.singleton x $ SizeSubst $ NamedDim $ qualName y
    matchTypeParam _ (TypeParamType spec_l x _) (TypeParamType l y _)
      | spec_l <= l =
        pure . M.singleton x . Subst [] . RetType [] $
          Scalar $ TypeVar () Nonunique (typeName y) []
    matchTypeParam nomatch _ _ =
      nomatch

    matchVal ::
      SrcLoc ->
      VName ->
      BoundV ->
      VName ->
      BoundV ->
      Either TypeError (VName, VName)
    matchVal loc spec_name spec_v name v =
      case matchValBinding loc spec_v v of
        Nothing -> return (spec_name, name)
        Just problem ->
          Left $
            TypeError loc mempty $
              "Module type specifies"
                </> indent 2 (ppValBind spec_name spec_v)
                </> "but module provides"
                </> indent 2 (ppValBind spec_name v)
                </> fromMaybe mempty problem

    matchValBinding :: SrcLoc -> BoundV -> BoundV -> Maybe (Maybe Doc)
    matchValBinding loc (BoundV _ orig_spec_t) (BoundV tps orig_t) =
      case doUnification loc tps (toStruct orig_spec_t) (toStruct orig_t) of
        Left (TypeError _ notes msg) ->
          Just $ Just $ msg <> ppr notes
        -- Even if they unify, we still have to verify the uniqueness
        -- properties.
        Right t
          | noSizes t
              `subtypeOf` noSizes orig_spec_t ->
            Nothing
          | otherwise -> Just Nothing

    ppValBind v (BoundV tps t) =
      "val" <+> pprName v <+> spread (map ppr tps) <+> colon
        </> indent 2 (align (ppr t))

-- | Apply a parametric module to an argument.
applyFunctor ::
  SrcLoc ->
  FunSig ->
  MTy ->
  TypeM
    ( MTy,
      M.Map VName VName,
      M.Map VName VName
    )
applyFunctor applyloc (FunSig p_abs p_mod body_mty) a_mty = do
  p_subst <- badOnLeft $ matchMTys a_mty (MTy p_abs p_mod) applyloc

  -- Apply type abbreviations from a_mty to body_mty.
  let a_abbrs = mtyTypeAbbrs a_mty
      isSub v = case M.lookup v a_abbrs of
        Just abbr -> Just $ substFromAbbr abbr
        _ -> Just $ SizeSubst $ NamedDim $ qualName v
      type_subst = M.mapMaybe isSub p_subst
      body_mty' = substituteTypesInMTy (`M.lookup` type_subst) body_mty
  (body_mty'', body_subst) <- newNamesForMTy body_mty'
  return (body_mty'', p_subst, body_subst)
