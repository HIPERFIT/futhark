{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The type checker checks whether the program is type-consistent
-- and adds type annotations and various other elaborations.  The
-- program does not need to have any particular properties for the
-- type checker to function; in particular it does not need unique
-- names.
module Language.Futhark.TypeChecker
  ( checkProg,
    checkExp,
    checkDec,
    checkModExp,
    TypeError,
    Warnings,
    initialEnv,
  )
where

import Control.Monad.Except
import Control.Monad.Writer hiding (Sum)
import Data.Bifunctor (second)
import Data.Char (isAlpha, isAlphaNum)
import Data.Either
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Ord
import qualified Data.Set as S
import Futhark.FreshNames hiding (newName)
import Futhark.Util.Pretty hiding (space)
import Language.Futhark
import Language.Futhark.Semantic
import Language.Futhark.TypeChecker.Modules
import Language.Futhark.TypeChecker.Monad
import Language.Futhark.TypeChecker.Terms
import Language.Futhark.TypeChecker.Types
import Prelude hiding (abs, mod)

--- The main checker

-- | Type check a program containing no type information, yielding
-- either a type error or a program with complete type information.
-- Accepts a mapping from file names (excluding extension) to
-- previously type checked results.  The 'ImportName' is used to resolve
-- relative @import@s.
checkProg ::
  Imports ->
  VNameSource ->
  ImportName ->
  UncheckedProg ->
  (Warnings, Either TypeError (FileModule, VNameSource))
checkProg files src name prog =
  runTypeM initialEnv files' name src $ checkProgM prog
  where
    files' = M.map fileEnv $ M.fromList files

-- | Type check a single expression containing no type information,
-- yielding either a type error or the same expression annotated with
-- type information.  Also returns a list of type parameters, which
-- will be nonempty if the expression is polymorphic.  See also
-- 'checkProg'.
checkExp ::
  Imports ->
  VNameSource ->
  Env ->
  UncheckedExp ->
  (Warnings, Either TypeError ([TypeParam], Exp))
checkExp files src env e =
  second (fmap fst) $ runTypeM env files' (mkInitialImport "") src $ checkOneExp e
  where
    files' = M.map fileEnv $ M.fromList files

-- | Type check a single declaration containing no type information,
-- yielding either a type error or the same declaration annotated with
-- type information along the Env produced by that declaration.  See
-- also 'checkProg'.
checkDec ::
  Imports ->
  VNameSource ->
  Env ->
  ImportName ->
  UncheckedDec ->
  (Warnings, Either TypeError (Env, Dec, VNameSource))
checkDec files src env name d =
  second (fmap massage) $
    runTypeM env files' name src $ do
      (_, env', d') <- checkOneDec d
      return (env' <> env, d')
  where
    massage ((env', d'), src') =
      (env', d', src')
    files' = M.map fileEnv $ M.fromList files

-- | Type check a single module expression containing no type information,
-- yielding either a type error or the same expression annotated with
-- type information along the Env produced by that declaration.  See
-- also 'checkProg'.
checkModExp ::
  Imports ->
  VNameSource ->
  Env ->
  ModExpBase NoInfo Name ->
  (Warnings, Either TypeError (MTy, ModExpBase Info VName))
checkModExp files src env me =
  second (fmap fst) $ runTypeM env files' (mkInitialImport "") src $ checkOneModExp me
  where
    files' = M.map fileEnv $ M.fromList files

-- | An initial environment for the type checker, containing
-- intrinsics and such.
initialEnv :: Env
initialEnv =
  intrinsicsModule
    { envModTable = initialModTable,
      envNameMap =
        M.insert
          (Term, nameFromString "intrinsics")
          (qualName intrinsics_v)
          topLevelNameMap
    }
  where
    initialTypeTable = M.fromList $ mapMaybe addIntrinsicT $ M.toList intrinsics
    initialModTable = M.singleton intrinsics_v (ModEnv intrinsicsModule)

    intrinsics_v = VName (nameFromString "intrinsics") 0

    intrinsicsModule = Env mempty initialTypeTable mempty mempty intrinsicsNameMap

    addIntrinsicT (name, IntrinsicType l ps t) =
      Just (name, TypeAbbr l ps $ RetType [] t)
    addIntrinsicT _ =
      Nothing

checkProgM :: UncheckedProg -> TypeM FileModule
checkProgM (Prog doc decs) = do
  checkForDuplicateDecs decs
  (abs, env, decs') <- checkDecs decs
  return (FileModule abs env $ Prog doc decs')

dupDefinitionError ::
  MonadTypeChecker m =>
  Namespace ->
  Name ->
  SrcLoc ->
  SrcLoc ->
  m a
dupDefinitionError space name loc1 loc2 =
  typeError loc1 mempty $
    "Duplicate definition of" <+> ppr space
      <+> pprName name <> ".  Previously defined at"
      <+> text (locStr loc2) <> "."

checkForDuplicateDecs :: [DecBase NoInfo Name] -> TypeM ()
checkForDuplicateDecs =
  foldM_ (flip f) mempty
  where
    check namespace name loc known =
      case M.lookup (namespace, name) known of
        Just loc' ->
          dupDefinitionError namespace name loc loc'
        _ -> return $ M.insert (namespace, name) loc known

    f (ValDec vb) =
      check Term (valBindName vb) (srclocOf vb)
    f (TypeDec (TypeBind name _ _ _ _ _ loc)) =
      check Type name loc
    f (SigDec (SigBind name _ _ loc)) =
      check Signature name loc
    f (ModDec (ModBind name _ _ _ _ loc)) =
      check Term name loc
    f OpenDec {} = return
    f LocalDec {} = return
    f ImportDec {} = return

bindingTypeParams :: [TypeParam] -> TypeM a -> TypeM a
bindingTypeParams tparams = localEnv env
  where
    env = mconcat $ map typeParamEnv tparams

    typeParamEnv (TypeParamDim v _) =
      mempty
        { envVtable =
            M.singleton v $ BoundV [] (Scalar $ Prim $ Signed Int64)
        }
    typeParamEnv (TypeParamType l v _) =
      mempty
        { envTypeTable =
            M.singleton v $
              TypeAbbr l [] . RetType [] . Scalar $
                TypeVar () Nonunique (typeName v) []
        }

checkTypeDecl ::
  TypeDeclBase NoInfo Name ->
  TypeM ([VName], TypeDeclBase Info VName, Liftedness)
checkTypeDecl (TypeDecl te NoInfo) = do
  (te', svars, RetType dims st, l) <- checkTypeExp te
  pure (svars ++ dims, TypeDecl te' $ Info st, l)

-- In this function, after the recursion, we add the Env of the
-- current Spec *after* the one that is returned from the recursive
-- call.  This implements the behaviour that specs later in a module
-- type can override those earlier (it rarely matters, but it affects
-- the specific structure of substitutions in case some module type is
-- redundantly imported multiple times).
checkSpecs :: [SpecBase NoInfo Name] -> TypeM (TySet, Env, [SpecBase Info VName])
checkSpecs [] = return (mempty, mempty, [])
checkSpecs (ValSpec name tparams vtype doc loc : specs) =
  bindSpaced [(Term, name)] $ do
    name' <- checkName Term name loc
    (tparams', vtype') <-
      checkTypeParams tparams $ \tparams' -> bindingTypeParams tparams' $ do
        (ext, vtype', _) <- checkTypeDecl vtype

        unless (null ext) $
          typeError loc mempty $
            "All function parameters must have non-anonymous sizes."
              </> "Hint: add size parameters to" <+> pquote (pprName name') <> "."

        return (tparams', vtype')

    let (params, _) = unfoldFunType $ unInfo $ expandedType vtype'
    when (null params && any isSizeParam tparams) $
      typeError
        loc
        mempty
        "Size parameters are only allowed on bindings that also have value parameters."

    let binding = BoundV tparams' $ unInfo $ expandedType vtype'
        valenv =
          mempty
            { envVtable = M.singleton name' binding,
              envNameMap = M.singleton (Term, name) $ qualName name'
            }
    (abstypes, env, specs') <- localEnv valenv $ checkSpecs specs
    return
      ( abstypes,
        env <> valenv,
        ValSpec name' tparams' vtype' doc loc : specs'
      )
checkSpecs (TypeAbbrSpec tdec : specs) =
  bindSpaced [(Type, typeAlias tdec)] $ do
    (tenv, tdec') <- checkTypeBind tdec
    (abstypes, env, specs') <- localEnv tenv $ checkSpecs specs
    return
      ( abstypes,
        env <> tenv,
        TypeAbbrSpec tdec' : specs'
      )
checkSpecs (TypeSpec l name ps doc loc : specs) =
  checkTypeParams ps $ \ps' ->
    bindSpaced [(Type, name)] $ do
      name' <- checkName Type name loc
      let tenv =
            mempty
              { envNameMap =
                  M.singleton (Type, name) $ qualName name',
                envTypeTable =
                  M.singleton name' $
                    TypeAbbr l ps' . RetType [] . Scalar $
                      TypeVar () Nonunique (typeName name') $
                        map typeParamToArg ps'
              }
      (abstypes, env, specs') <- localEnv tenv $ checkSpecs specs
      return
        ( M.insert (qualName name') l abstypes,
          env <> tenv,
          TypeSpec l name' ps' doc loc : specs'
        )
checkSpecs (ModSpec name sig doc loc : specs) =
  bindSpaced [(Term, name)] $ do
    name' <- checkName Term name loc
    (mty, sig') <- checkSigExp sig
    let senv =
          mempty
            { envNameMap = M.singleton (Term, name) $ qualName name',
              envModTable = M.singleton name' $ mtyMod mty
            }
    (abstypes, env, specs') <- localEnv senv $ checkSpecs specs
    return
      ( M.mapKeys (qualify name') (mtyAbs mty) <> abstypes,
        env <> senv,
        ModSpec name' sig' doc loc : specs'
      )
checkSpecs (IncludeSpec e loc : specs) = do
  (e_abs, e_env, e') <- checkSigExpToEnv e

  mapM_ (warnIfShadowing . fmap baseName) $ M.keys e_abs

  (abstypes, env, specs') <- localEnv e_env $ checkSpecs specs
  return
    ( abstypes <> e_abs,
      env <> e_env,
      IncludeSpec e' loc : specs'
    )
  where
    warnIfShadowing qn =
      (lookupType loc qn >> warnAbout qn)
        `catchError` \_ -> return ()
    warnAbout qn =
      warn loc $ "Inclusion shadows type" <+> pquote (ppr qn) <+> "."

checkSigExp :: SigExpBase NoInfo Name -> TypeM (MTy, SigExpBase Info VName)
checkSigExp (SigParens e loc) = do
  (mty, e') <- checkSigExp e
  return (mty, SigParens e' loc)
checkSigExp (SigVar name NoInfo loc) = do
  (name', mty) <- lookupMTy loc name
  (mty', substs) <- newNamesForMTy mty
  return (mty', SigVar name' (Info substs) loc)
checkSigExp (SigSpecs specs loc) = do
  checkForDuplicateSpecs specs
  (abstypes, env, specs') <- checkSpecs specs
  return (MTy abstypes $ ModEnv env, SigSpecs specs' loc)
checkSigExp (SigWith s (TypeRef tname ps td trloc) loc) = do
  (s_abs, s_env, s') <- checkSigExpToEnv s
  checkTypeParams ps $ \ps' -> do
    (ext, td', _) <- bindingTypeParams ps' $ checkTypeDecl td
    unless (null ext) $
      typeError td' mempty "Anonymous dimensions are not allowed here."
    (tname', s_abs', s_env') <- refineEnv loc s_abs s_env tname ps' $ unInfo $ expandedType td'
    return (MTy s_abs' $ ModEnv s_env', SigWith s' (TypeRef tname' ps' td' trloc) loc)
checkSigExp (SigArrow maybe_pname e1 e2 loc) = do
  (MTy s_abs e1_mod, e1') <- checkSigExp e1
  (env_for_e2, maybe_pname') <-
    case maybe_pname of
      Just pname -> bindSpaced [(Term, pname)] $ do
        pname' <- checkName Term pname loc
        return
          ( mempty
              { envNameMap = M.singleton (Term, pname) $ qualName pname',
                envModTable = M.singleton pname' e1_mod
              },
            Just pname'
          )
      Nothing ->
        return (mempty, Nothing)
  (e2_mod, e2') <- localEnv env_for_e2 $ checkSigExp e2
  return
    ( MTy mempty $ ModFun $ FunSig s_abs e1_mod e2_mod,
      SigArrow maybe_pname' e1' e2' loc
    )

checkSigExpToEnv :: SigExpBase NoInfo Name -> TypeM (TySet, Env, SigExpBase Info VName)
checkSigExpToEnv e = do
  (MTy abs mod, e') <- checkSigExp e
  case mod of
    ModEnv env -> return (abs, env, e')
    ModFun {} -> unappliedFunctor $ srclocOf e

checkSigBind :: SigBindBase NoInfo Name -> TypeM (Env, SigBindBase Info VName)
checkSigBind (SigBind name e doc loc) = do
  (env, e') <- checkSigExp e
  bindSpaced [(Signature, name)] $ do
    name' <- checkName Signature name loc
    return
      ( mempty
          { envSigTable = M.singleton name' env,
            envNameMap = M.singleton (Signature, name) (qualName name')
          },
        SigBind name' e' doc loc
      )

checkOneModExp :: ModExpBase NoInfo Name -> TypeM (MTy, ModExpBase Info VName)
checkOneModExp (ModParens e loc) = do
  (mty, e') <- checkOneModExp e
  return (mty, ModParens e' loc)
checkOneModExp (ModDecs decs loc) = do
  checkForDuplicateDecs decs
  (abstypes, env, decs') <- checkDecs decs
  return
    ( MTy abstypes $ ModEnv env,
      ModDecs decs' loc
    )
checkOneModExp (ModVar v loc) = do
  (v', env) <- lookupMod loc v
  when
    ( baseName (qualLeaf v') == nameFromString "intrinsics"
        && baseTag (qualLeaf v') <= maxIntrinsicTag
    )
    $ typeError loc mempty "The 'intrinsics' module may not be used in module expressions."
  return (MTy mempty env, ModVar v' loc)
checkOneModExp (ModImport name NoInfo loc) = do
  (name', env) <- lookupImport loc name
  return
    ( MTy mempty $ ModEnv env,
      ModImport name (Info name') loc
    )
checkOneModExp (ModApply f e NoInfo NoInfo loc) = do
  (f_mty, f') <- checkOneModExp f
  case mtyMod f_mty of
    ModFun functor -> do
      (e_mty, e') <- checkOneModExp e
      (mty, psubsts, rsubsts) <- applyFunctor loc functor e_mty
      return (mty, ModApply f' e' (Info psubsts) (Info rsubsts) loc)
    _ ->
      typeError loc mempty "Cannot apply non-parametric module."
checkOneModExp (ModAscript me se NoInfo loc) = do
  (me_mod, me') <- checkOneModExp me
  (se_mty, se') <- checkSigExp se
  match_subst <- badOnLeft $ matchMTys me_mod se_mty loc
  return (se_mty, ModAscript me' se' (Info match_subst) loc)
checkOneModExp (ModLambda param maybe_fsig_e body_e loc) =
  withModParam param $ \param' param_abs param_mod -> do
    (maybe_fsig_e', body_e', mty) <- checkModBody (fst <$> maybe_fsig_e) body_e loc
    return
      ( MTy mempty $ ModFun $ FunSig param_abs param_mod mty,
        ModLambda param' maybe_fsig_e' body_e' loc
      )

checkOneModExpToEnv :: ModExpBase NoInfo Name -> TypeM (TySet, Env, ModExpBase Info VName)
checkOneModExpToEnv e = do
  (MTy abs mod, e') <- checkOneModExp e
  case mod of
    ModEnv env -> return (abs, env, e')
    ModFun {} -> unappliedFunctor $ srclocOf e

withModParam ::
  ModParamBase NoInfo Name ->
  (ModParamBase Info VName -> TySet -> Mod -> TypeM a) ->
  TypeM a
withModParam (ModParam pname psig_e NoInfo loc) m = do
  (MTy p_abs p_mod, psig_e') <- checkSigExp psig_e
  bindSpaced [(Term, pname)] $ do
    pname' <- checkName Term pname loc
    let in_body_env = mempty {envModTable = M.singleton pname' p_mod}
    localEnv in_body_env $
      m (ModParam pname' psig_e' (Info $ map qualLeaf $ M.keys p_abs) loc) p_abs p_mod

withModParams ::
  [ModParamBase NoInfo Name] ->
  ([(ModParamBase Info VName, TySet, Mod)] -> TypeM a) ->
  TypeM a
withModParams [] m = m []
withModParams (p : ps) m =
  withModParam p $ \p' pabs pmod ->
    withModParams ps $ \ps' -> m $ (p', pabs, pmod) : ps'

checkModBody ::
  Maybe (SigExpBase NoInfo Name) ->
  ModExpBase NoInfo Name ->
  SrcLoc ->
  TypeM
    ( Maybe (SigExp, Info (M.Map VName VName)),
      ModExp,
      MTy
    )
checkModBody maybe_fsig_e body_e loc = do
  (body_mty, body_e') <- checkOneModExp body_e
  case maybe_fsig_e of
    Nothing ->
      return (Nothing, body_e', body_mty)
    Just fsig_e -> do
      (fsig_mty, fsig_e') <- checkSigExp fsig_e
      fsig_subst <- badOnLeft $ matchMTys body_mty fsig_mty loc
      return (Just (fsig_e', Info fsig_subst), body_e', fsig_mty)

checkModBind :: ModBindBase NoInfo Name -> TypeM (TySet, Env, ModBindBase Info VName)
checkModBind (ModBind name [] maybe_fsig_e e doc loc) = do
  (maybe_fsig_e', e', mty) <- checkModBody (fst <$> maybe_fsig_e) e loc
  bindSpaced [(Term, name)] $ do
    name' <- checkName Term name loc
    return
      ( mtyAbs mty,
        mempty
          { envModTable = M.singleton name' $ mtyMod mty,
            envNameMap = M.singleton (Term, name) $ qualName name'
          },
        ModBind name' [] maybe_fsig_e' e' doc loc
      )
checkModBind (ModBind name (p : ps) maybe_fsig_e body_e doc loc) = do
  (params', maybe_fsig_e', body_e', funsig) <-
    withModParam p $ \p' p_abs p_mod ->
      withModParams ps $ \params_stuff -> do
        let (ps', ps_abs, ps_mod) = unzip3 params_stuff
        (maybe_fsig_e', body_e', mty) <- checkModBody (fst <$> maybe_fsig_e) body_e loc
        let addParam (x, y) mty' = MTy mempty $ ModFun $ FunSig x y mty'
        return
          ( p' : ps',
            maybe_fsig_e',
            body_e',
            FunSig p_abs p_mod $ foldr addParam mty $ zip ps_abs ps_mod
          )
  bindSpaced [(Term, name)] $ do
    name' <- checkName Term name loc
    return
      ( mempty,
        mempty
          { envModTable =
              M.singleton name' $ ModFun funsig,
            envNameMap =
              M.singleton (Term, name) $ qualName name'
          },
        ModBind name' params' maybe_fsig_e' body_e' doc loc
      )

checkForDuplicateSpecs :: [SpecBase NoInfo Name] -> TypeM ()
checkForDuplicateSpecs =
  foldM_ (flip f) mempty
  where
    check namespace name loc known =
      case M.lookup (namespace, name) known of
        Just loc' ->
          dupDefinitionError namespace name loc loc'
        _ -> return $ M.insert (namespace, name) loc known

    f (ValSpec name _ _ _ loc) =
      check Term name loc
    f (TypeAbbrSpec (TypeBind name _ _ _ _ _ loc)) =
      check Type name loc
    f (TypeSpec _ name _ _ loc) =
      check Type name loc
    f (ModSpec name _ _ loc) =
      check Term name loc
    f IncludeSpec {} =
      return

checkTypeBind ::
  TypeBindBase NoInfo Name ->
  TypeM (Env, TypeBindBase Info VName)
checkTypeBind (TypeBind name l tps te NoInfo doc loc) =
  checkTypeParams tps $ \tps' -> do
    (te', svars, RetType dims t, l') <- bindingTypeParams tps' $ checkTypeExp te
    let elab_t = RetType (svars ++ dims) t

    let used_dims = typeDimNames t
    case filter ((`S.notMember` used_dims) . typeParamName) $
      filter isSizeParam tps' of
      [] -> return ()
      tp : _ ->
        typeError loc mempty $
          "Size parameter" <+> pquote (ppr tp) <+> "unused."

    case (l, l') of
      (_, Lifted)
        | l < Lifted ->
          typeError loc mempty $
            "Non-lifted type abbreviations may not contain functions."
              </> "Hint: consider using 'type^'."
      (_, SizeLifted)
        | l < SizeLifted ->
          typeError loc mempty $
            "Non-size-lifted type abbreviations may not contain size-lifted types."
              </> "Hint: consider using 'type~'."
      (Unlifted, _)
        | not $ null $ svars ++ dims ->
          typeError loc mempty $
            "Non-lifted type abbreviations may not use existential sizes in their definition."
              </> "Hint: use 'type~' or add size parameters to"
              <+> pquote (pprName name) <> "."
      _ -> return ()

    bindSpaced [(Type, name)] $ do
      name' <- checkName Type name loc
      return
        ( mempty
            { envTypeTable =
                M.singleton name' $ TypeAbbr l tps' elab_t,
              envNameMap =
                M.singleton (Type, name) $ qualName name'
            },
          TypeBind name' l tps' te' (Info elab_t) doc loc
        )

entryPoint :: [Pattern] -> Maybe (TypeExp VName) -> StructRetType -> EntryPoint
entryPoint params orig_ret_te (RetType _ orig_ret) =
  EntryPoint (map patternEntry params ++ more_params) rettype'
  where
    (more_params, rettype') =
      onRetType orig_ret_te orig_ret

    patternEntry (PatternParens p _) =
      patternEntry p
    patternEntry (PatternAscription _ tdecl _) =
      EntryType (unInfo (expandedType tdecl)) (Just (declaredType tdecl))
    patternEntry p =
      EntryType (patternStructType p) Nothing

    onRetType (Just (TEArrow _ t1_te t2_te _)) (Scalar (Arrow _ _ t1 (RetType _ t2))) =
      let (xs, y) = onRetType (Just t2_te) t2
       in (EntryType t1 (Just t1_te) : xs, y)
    onRetType _ (Scalar (Arrow _ _ t1 (RetType _ t2))) =
      let (xs, y) = onRetType Nothing t2
       in (EntryType t1 Nothing : xs, y)
    onRetType te t =
      ([], EntryType t te)

entryPointNameIsAcceptable :: Name -> Bool
entryPointNameIsAcceptable = check . nameToString
  where
    check [] = True -- academic
    check (c : cs) = isAlpha c && all constituent cs
    constituent c = isAlphaNum c || c == '_'

checkValBind :: ValBindBase NoInfo Name -> TypeM (Env, ValBind)
checkValBind (ValBind entry fname maybe_tdecl NoInfo tparams params body doc attrs loc) = do
  (fname', tparams', params', maybe_tdecl', rettype@(RetType _ rettype_t), retext, body') <-
    checkFunDef (fname, maybe_tdecl, tparams, params, body, loc)

  let (rettype_params, rettype') = unfoldFunType rettype_t
      entry' = Info (entryPoint params' maybe_tdecl' rettype) <$ entry

  case entry' of
    Just _
      | not $ entryPointNameIsAcceptable fname ->
        typeError loc mempty "Entry point names must start with a letter and contain only letters, digits, and underscores."
      | any isTypeParam tparams' ->
        typeError loc mempty "Entry point functions may not be polymorphic."
      | not (all patternOrderZero params')
          || not (all orderZero rettype_params)
          || not (orderZero rettype') ->
        typeError loc mempty "Entry point functions may not be higher-order."
      | sizes_only_in_ret <-
          S.fromList (map typeParamName tparams')
            `S.intersection` typeDimNames rettype'
            `S.difference` foldMap typeDimNames (map patternStructType params' ++ rettype_params),
        not $ S.null sizes_only_in_ret ->
        typeError loc mempty "Entry point functions must not be size-polymorphic in their return type."
      | p : _ <- filter nastyParameter params' ->
        warn loc $
          "Entry point parameter\n"
            </> indent 2 (ppr p)
            </> "\nwill have an opaque type, so the entry point will likely not be callable."
      | nastyReturnType maybe_tdecl' rettype_t ->
        warn loc $
          "Entry point return type\n"
            </> indent 2 (ppr rettype)
            </> "\nwill have an opaque type, so the result will likely not be usable."
    _ -> return ()

  let vb = ValBind entry' fname' maybe_tdecl' (Info (rettype, retext)) tparams' params' body' doc attrs loc
  return
    ( mempty
        { envVtable =
            M.singleton fname' $ uncurry BoundV $ valBindTypeScheme vb,
          envNameMap =
            M.singleton (Term, fname) $ qualName fname'
        },
      vb
    )

nastyType :: Monoid als => TypeBase dim als -> Bool
nastyType (Scalar Prim {}) = False
nastyType t@Array {} = nastyType $ stripArray 1 t
nastyType _ = True

nastyReturnType :: Monoid als => Maybe (TypeExp VName) -> TypeBase dim als -> Bool
nastyReturnType Nothing (Scalar (Arrow _ _ t1 (RetType _ t2))) =
  nastyType t1 || nastyReturnType Nothing t2
nastyReturnType (Just (TEArrow _ te1 te2 _)) (Scalar (Arrow _ _ t1 (RetType _ t2))) =
  (not (niceTypeExp te1) && nastyType t1)
    || nastyReturnType (Just te2) t2
nastyReturnType (Just te) _
  | niceTypeExp te = False
nastyReturnType te t
  | Just ts <- isTupleRecord t =
    case te of
      Just (TETuple tes _) -> or $ zipWith nastyType' (map Just tes) ts
      _ -> any nastyType ts
  | otherwise = nastyType' te t
  where
    nastyType' (Just te') _ | niceTypeExp te' = False
    nastyType' _ t' = nastyType t'

nastyParameter :: Pattern -> Bool
nastyParameter p = nastyType (patternType p) && not (ascripted p)
  where
    ascripted (PatternAscription _ (TypeDecl te _) _) = niceTypeExp te
    ascripted (PatternParens p' _) = ascripted p'
    ascripted _ = False

niceTypeExp :: TypeExp VName -> Bool
niceTypeExp (TEVar (QualName [] _) _) = True
niceTypeExp (TEApply te TypeArgExpDim {} _) = niceTypeExp te
niceTypeExp (TEArray te _ _) = niceTypeExp te
niceTypeExp _ = False

checkOneDec :: DecBase NoInfo Name -> TypeM (TySet, Env, DecBase Info VName)
checkOneDec (ModDec struct) = do
  (abs, modenv, struct') <- checkModBind struct
  return (abs, modenv, ModDec struct')
checkOneDec (SigDec sig) = do
  (sigenv, sig') <- checkSigBind sig
  return (mempty, sigenv, SigDec sig')
checkOneDec (TypeDec tdec) = do
  (tenv, tdec') <- checkTypeBind tdec
  return (mempty, tenv, TypeDec tdec')
checkOneDec (OpenDec x loc) = do
  (x_abs, x_env, x') <- checkOneModExpToEnv x
  return (x_abs, x_env, OpenDec x' loc)
checkOneDec (LocalDec d loc) = do
  (abstypes, env, d') <- checkOneDec d
  return (abstypes, env, LocalDec d' loc)
checkOneDec (ImportDec name NoInfo loc) = do
  (name', env) <- lookupImport loc name
  when ("/prelude" `isPrefixOf` name) $
    typeError loc mempty $ ppr name <+> "may not be explicitly imported."
  return (mempty, env, ImportDec name (Info name') loc)
checkOneDec (ValDec vb) = do
  (env, vb') <- checkValBind vb
  return (mempty, env, ValDec vb')

checkDecs :: [DecBase NoInfo Name] -> TypeM (TySet, Env, [DecBase Info VName])
checkDecs (d : ds) = do
  (d_abstypes, d_env, d') <- checkOneDec d
  (ds_abstypes, ds_env, ds') <- localEnv d_env $ checkDecs ds
  return
    ( d_abstypes <> ds_abstypes,
      case d' of
        LocalDec {} -> ds_env
        ImportDec {} -> ds_env
        _ -> ds_env <> d_env,
      d' : ds'
    )
checkDecs [] =
  return (mempty, mempty, [])
