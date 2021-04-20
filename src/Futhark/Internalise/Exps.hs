{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Futhark.Internalise.Exps (transformProg) where

import Control.Monad.Reader
import Data.List (find, intercalate, intersperse, transpose)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Futhark.IR.SOACS as I hiding (stmPattern)
import Futhark.Internalise.AccurateSizes
import Futhark.Internalise.Bindings
import Futhark.Internalise.Lambdas
import Futhark.Internalise.Monad as I
import Futhark.Internalise.TypesValues
import Futhark.Transform.Rename as I
import Futhark.Util (splitAt3)
import Futhark.Util.Pretty (prettyOneLine)
import Language.Futhark as E hiding (TypeArg)

-- | Convert a program in source Futhark to a program in the Futhark
-- core language.
transformProg :: MonadFreshNames m => Bool -> [E.ValBind] -> m (I.Prog SOACS)
transformProg always_safe vbinds = do
  (consts, funs) <-
    runInternaliseM always_safe (internaliseValBinds vbinds)
  I.renameProg $ I.Prog consts funs

internaliseAttr :: E.AttrInfo -> Attr
internaliseAttr (E.AttrAtom v) = I.AttrAtom v
internaliseAttr (E.AttrComp f attrs) = I.AttrComp f $ map internaliseAttr attrs

internaliseAttrs :: [E.AttrInfo] -> Attrs
internaliseAttrs = mconcat . map (oneAttr . internaliseAttr)

internaliseValBinds :: [E.ValBind] -> InternaliseM ()
internaliseValBinds = mapM_ internaliseValBind

internaliseFunName :: VName -> Name
internaliseFunName = nameFromString . pretty

internaliseValBind :: E.ValBind -> InternaliseM ()
internaliseValBind fb@(E.ValBind entry fname retdecl (Info (rettype, _)) tparams params body _ attrs loc) = do
  localConstsScope $
    bindingFParams tparams params $ \shapeparams params' -> do
      let shapenames = map I.paramName shapeparams

      msg <- case retdecl of
        Just dt ->
          errorMsg
            . ("Function return value does not match shape of type " :)
            <$> typeExpForError dt
        Nothing -> return $ errorMsg ["Function return value does not match shape of declared return type."]

      (body', rettype') <- buildBody $ do
        body_res <- internaliseExp (baseString fname <> "_res") body
        rettype_bad <-
          internaliseReturnType rettype =<< mapM subExpType body_res
        let rettype' = zeroExts rettype_bad
        body_res' <-
          ensureResultExtShape msg loc (map I.fromDecl rettype') body_res
        pure (body_res', rettype')

      let all_params = shapeparams ++ concat params'

      let fd =
            I.FunDef
              Nothing
              (internaliseAttrs attrs)
              (internaliseFunName fname)
              rettype'
              all_params
              body'

      if null params'
        then bindConstant fname fd
        else
          bindFunction
            fname
            fd
            ( shapenames,
              map declTypeOf $ concat params',
              all_params,
              applyRetType rettype' all_params
            )

  case entry of
    Just (Info entry') -> generateEntryPoint entry' fb
    Nothing -> return ()
  where
    zeroExts ts = generaliseExtTypes ts ts

generateEntryPoint :: E.EntryPoint -> E.ValBind -> InternaliseM ()
generateEntryPoint (E.EntryPoint e_paramts e_rettype) vb = localConstsScope $ do
  let (E.ValBind _ ofname _ (Info (rettype, _)) tparams params _ _ attrs loc) = vb
  bindingFParams tparams params $ \shapeparams params' -> do
    entry_rettype <- internaliseEntryReturnType rettype
    let entry' = entryPoint (baseName ofname) (zip e_paramts params') (e_rettype, entry_rettype)
        args = map (I.Var . I.paramName) $ concat params'

    entry_body <- buildBody_ $ do
      -- Special case the (rare) situation where the entry point is
      -- not a function.
      maybe_const <- lookupConst ofname
      vals <- case maybe_const of
        Just ses ->
          return ses
        Nothing ->
          fst <$> funcall "entry_result" (E.qualName ofname) args loc
      ctx <-
        extractShapeContext (concat entry_rettype)
          <$> mapM (fmap I.arrayDims . subExpType) vals
      pure $ ctx ++ vals

    addFunDef $
      I.FunDef
        (Just entry')
        (internaliseAttrs attrs)
        ("entry_" <> baseName ofname)
        (concat entry_rettype)
        (shapeparams ++ concat params')
        entry_body

entryPoint ::
  Name ->
  [(E.EntryType, [I.FParam])] ->
  ( E.EntryType,
    [[I.TypeBase ExtShape Uniqueness]]
  ) ->
  I.EntryPoint
entryPoint name params (eret, crets) =
  ( name,
    concatMap (entryPointType . preParam) params,
    case ( isTupleRecord $ entryType eret,
           entryAscribed eret
         ) of
      (Just ts, Just (E.TETuple e_ts _)) ->
        concatMap entryPointType $
          zip (zipWith E.EntryType ts (map Just e_ts)) crets
      (Just ts, Nothing) ->
        concatMap entryPointType $
          zip (map (`E.EntryType` Nothing) ts) crets
      _ ->
        entryPointType (eret, concat crets)
  )
  where
    preParam (e_t, ps) = (e_t, staticShapes $ map I.paramDeclType ps)

    entryPointType (t, ts)
      | E.Scalar (E.Prim E.Unsigned {}) <- E.entryType t =
        [I.TypeUnsigned]
      | E.Array _ _ (E.Prim E.Unsigned {}) _ <- E.entryType t =
        [I.TypeUnsigned]
      | E.Scalar E.Prim {} <- E.entryType t =
        [I.TypeDirect]
      | E.Array _ _ E.Prim {} _ <- E.entryType t =
        [I.TypeDirect]
      | otherwise =
        [I.TypeOpaque desc $ length ts]
      where
        desc = maybe (prettyOneLine t') typeExpOpaqueName $ E.entryAscribed t
        t' = noSizes (E.entryType t) `E.setUniqueness` Nonunique
    typeExpOpaqueName (TEApply te TypeArgExpDim {} _) =
      typeExpOpaqueName te
    typeExpOpaqueName (TEArray te _ _) =
      let (d, te') = withoutDims te
       in "arr_" ++ typeExpOpaqueName te'
            ++ "_"
            ++ show (1 + d)
            ++ "d"
    typeExpOpaqueName te = prettyOneLine te

    withoutDims (TEArray te _ _) =
      let (d, te') = withoutDims te
       in (d + 1, te')
    withoutDims te = (0 :: Int, te)

internaliseBody :: String -> E.Exp -> InternaliseM Body
internaliseBody desc e =
  buildBody_ $ internaliseExp (desc <> "_res") e

bodyFromStms ::
  InternaliseM (Result, a) ->
  InternaliseM (Body, a)
bodyFromStms m = do
  ((res, a), stms) <- collectStms m
  (,a) <$> mkBodyM stms res

internaliseAppExp :: String -> E.AppExp -> InternaliseM [I.SubExp]
internaliseAppExp desc (E.Index e idxs loc) = do
  vs <- internaliseExpToVars "indexed" e
  dims <- case vs of
    [] -> return [] -- Will this happen?
    v : _ -> I.arrayDims <$> lookupType v
  (idxs', cs) <- internaliseSlice loc dims idxs
  let index v = do
        v_t <- lookupType v
        return $ I.BasicOp $ I.Index v $ fullSlice v_t idxs'
  certifying cs $ letSubExps desc =<< mapM index vs
internaliseAppExp desc (E.Range start maybe_second end loc) = do
  start' <- internaliseExp1 "range_start" start
  end' <- internaliseExp1 "range_end" $ case end of
    DownToExclusive e -> e
    ToInclusive e -> e
    UpToExclusive e -> e
  maybe_second' <-
    traverse (internaliseExp1 "range_second") maybe_second

  -- Construct an error message in case the range is invalid.
  let conv = case E.typeOf start of
        E.Scalar (E.Prim (E.Unsigned _)) -> asIntZ Int64
        _ -> asIntS Int64
  start'_i64 <- conv start'
  end'_i64 <- conv end'
  maybe_second'_i64 <- traverse conv maybe_second'
  let errmsg =
        errorMsg $
          ["Range "]
            ++ [ErrorInt64 start'_i64]
            ++ ( case maybe_second'_i64 of
                   Nothing -> []
                   Just second_i64 -> ["..", ErrorInt64 second_i64]
               )
            ++ ( case end of
                   DownToExclusive {} -> ["..>"]
                   ToInclusive {} -> ["..."]
                   UpToExclusive {} -> ["..<"]
               )
            ++ [ErrorInt64 end'_i64, " is invalid."]

  (it, le_op, lt_op) <-
    case E.typeOf start of
      E.Scalar (E.Prim (E.Signed it)) -> return (it, CmpSle it, CmpSlt it)
      E.Scalar (E.Prim (E.Unsigned it)) -> return (it, CmpUle it, CmpUlt it)
      start_t -> error $ "Start value in range has type " ++ pretty start_t

  let one = intConst it 1
      negone = intConst it (-1)
      default_step = case end of
        DownToExclusive {} -> negone
        ToInclusive {} -> one
        UpToExclusive {} -> one

  (step, step_zero) <- case maybe_second' of
    Just second' -> do
      subtracted_step <-
        letSubExp "subtracted_step" $
          I.BasicOp $ I.BinOp (I.Sub it I.OverflowWrap) second' start'
      step_zero <- letSubExp "step_zero" $ I.BasicOp $ I.CmpOp (I.CmpEq $ IntType it) start' second'
      return (subtracted_step, step_zero)
    Nothing ->
      return (default_step, constant False)

  step_sign <- letSubExp "s_sign" $ BasicOp $ I.UnOp (I.SSignum it) step
  step_sign_i64 <- asIntS Int64 step_sign

  bounds_invalid_downwards <-
    letSubExp "bounds_invalid_downwards" $
      I.BasicOp $ I.CmpOp le_op start' end'
  bounds_invalid_upwards <-
    letSubExp "bounds_invalid_upwards" $
      I.BasicOp $ I.CmpOp lt_op end' start'

  (distance, step_wrong_dir, bounds_invalid) <- case end of
    DownToExclusive {} -> do
      step_wrong_dir <-
        letSubExp "step_wrong_dir" $
          I.BasicOp $ I.CmpOp (I.CmpEq $ IntType it) step_sign one
      distance <-
        letSubExp "distance" $
          I.BasicOp $ I.BinOp (Sub it I.OverflowWrap) start' end'
      distance_i64 <- asIntS Int64 distance
      return (distance_i64, step_wrong_dir, bounds_invalid_downwards)
    UpToExclusive {} -> do
      step_wrong_dir <-
        letSubExp "step_wrong_dir" $
          I.BasicOp $ I.CmpOp (I.CmpEq $ IntType it) step_sign negone
      distance <- letSubExp "distance" $ I.BasicOp $ I.BinOp (Sub it I.OverflowWrap) end' start'
      distance_i64 <- asIntS Int64 distance
      return (distance_i64, step_wrong_dir, bounds_invalid_upwards)
    ToInclusive {} -> do
      downwards <-
        letSubExp "downwards" $
          I.BasicOp $ I.CmpOp (I.CmpEq $ IntType it) step_sign negone
      distance_downwards_exclusive <-
        letSubExp "distance_downwards_exclusive" $
          I.BasicOp $ I.BinOp (Sub it I.OverflowWrap) start' end'
      distance_upwards_exclusive <-
        letSubExp "distance_upwards_exclusive" $
          I.BasicOp $ I.BinOp (Sub it I.OverflowWrap) end' start'

      bounds_invalid <-
        letSubExp "bounds_invalid" $
          I.If
            downwards
            (resultBody [bounds_invalid_downwards])
            (resultBody [bounds_invalid_upwards])
            $ ifCommon [I.Prim I.Bool]
      distance_exclusive <-
        letSubExp "distance_exclusive" $
          I.If
            downwards
            (resultBody [distance_downwards_exclusive])
            (resultBody [distance_upwards_exclusive])
            $ ifCommon [I.Prim $ IntType it]
      distance_exclusive_i64 <- asIntS Int64 distance_exclusive
      distance <-
        letSubExp "distance" $
          I.BasicOp $
            I.BinOp
              (Add Int64 I.OverflowWrap)
              distance_exclusive_i64
              (intConst Int64 1)
      return (distance, constant False, bounds_invalid)

  step_invalid <-
    letSubExp "step_invalid" $
      I.BasicOp $ I.BinOp I.LogOr step_wrong_dir step_zero

  invalid <-
    letSubExp "range_invalid" $
      I.BasicOp $ I.BinOp I.LogOr step_invalid bounds_invalid
  valid <- letSubExp "valid" $ I.BasicOp $ I.UnOp I.Not invalid
  cs <- assert "range_valid_c" valid errmsg loc

  step_i64 <- asIntS Int64 step
  pos_step <-
    letSubExp "pos_step" $
      I.BasicOp $ I.BinOp (Mul Int64 I.OverflowWrap) step_i64 step_sign_i64

  num_elems <-
    certifying cs $
      letSubExp "num_elems" $
        I.BasicOp $ I.BinOp (SDivUp Int64 I.Unsafe) distance pos_step

  se <- letSubExp desc (I.BasicOp $ I.Iota num_elems start' step it)
  return [se]
internaliseAppExp desc (E.Coerce e (TypeDecl dt (Info et)) loc) = do
  ses <- internaliseExp desc e
  ts <- internaliseReturnType (E.RetType [] et) =<< mapM subExpType ses
  dt' <- typeExpForError dt
  forM (zip ses ts) $ \(e', t') -> do
    dims <- arrayDims <$> subExpType e'
    let parts =
          ["Value of (core language) shape ("]
            ++ intersperse ", " (map ErrorInt64 dims)
            ++ [") cannot match shape of type `"]
            ++ dt'
            ++ ["`."]
    ensureExtShape (errorMsg parts) loc (I.fromDecl t') desc e'
internaliseAppExp desc e@E.Apply {} = do
  (qfname, args) <- findFuncall e

  -- Argument evaluation is outermost-in so that any existential sizes
  -- created by function applications can be brought into scope.
  let fname = nameFromString $ pretty $ baseName $ qualLeaf qfname
      loc = srclocOf e
      arg_desc = nameToString fname ++ "_arg"

  -- Some functions are magical (overloaded) and we handle that here.
  case () of
    -- Overloaded functions never take array arguments (except
    -- equality, but those cannot be existential), so we can safely
    -- ignore the existential dimensions.
    ()
      | Just internalise <- isOverloadedFunction qfname (map fst args) loc ->
        internalise desc
      | baseTag (qualLeaf qfname) <= maxIntrinsicTag,
        Just (rettype, _) <- M.lookup fname I.builtInFunctions -> do
        let tag ses = [(se, I.Observe) | se <- ses]
        args' <- reverse <$> mapM (internaliseArg arg_desc) (reverse args)
        let args'' = concatMap tag args'
        letTupExp' desc $
          I.Apply
            fname
            args''
            [I.Prim rettype]
            (Safe, loc, [])
      | otherwise -> do
        args' <- concat . reverse <$> mapM (internaliseArg arg_desc) (reverse args)
        fst <$> funcall desc qfname args' loc
internaliseAppExp desc (E.LetPat sizes pat e body _) =
  internalisePat desc sizes pat e body (internaliseExp desc)
internaliseAppExp _ (E.LetFun ofname _ _ _) =
  error $ "Unexpected LetFun " ++ pretty ofname
internaliseAppExp desc (E.DoLoop sparams mergepat mergeexp form loopbody loc) = do
  ses <- internaliseExp "loop_init" mergeexp
  ((loopbody', (form', shapepat, mergepat', mergeinit')), initstms) <-
    collectStms $ handleForm ses form

  addStms initstms
  mergeinit_ts' <- mapM subExpType mergeinit'

  ctxinit <- argShapes (map I.paramName shapepat) mergepat' mergeinit_ts'

  let ctxmerge = zip shapepat ctxinit
      valmerge = zip mergepat' mergeinit'
      dropCond = case form of
        E.While {} -> drop 1
        _ -> id

  -- Ensure that the result of the loop matches the shapes of the
  -- merge parameters.  XXX: Ideally they should already match (by
  -- the source language type rules), but some of our
  -- transformations (esp. defunctionalisation) strips out some size
  -- information.  For a type-correct source program, these reshapes
  -- should simplify away.
  let merge = ctxmerge ++ valmerge
      merge_ts = map (I.paramType . fst) merge
  loopbody'' <-
    localScope (scopeOfFParams $ map fst merge) . inScopeOf form' . buildBody_ $
      ensureArgShapes
        "shape of loop result does not match shapes in loop parameter"
        loc
        (map (I.paramName . fst) ctxmerge)
        merge_ts
        =<< bodyBind loopbody'

  attrs <- asks envAttrs
  map I.Var . dropCond
    <$> attributing
      attrs
      (letTupExp desc (I.DoLoop ctxmerge valmerge form' loopbody''))
  where
    sparams' = map (`TypeParamDim` mempty) sparams

    forLoop mergepat' shapepat mergeinit form' =
      bodyFromStms $
        inScopeOf form' $ do
          ses <- internaliseExp "loopres" loopbody
          sets <- mapM subExpType ses
          shapeargs <- argShapes (map I.paramName shapepat) mergepat' sets
          return
            ( shapeargs ++ ses,
              ( form',
                shapepat,
                mergepat',
                mergeinit
              )
            )

    handleForm mergeinit (E.ForIn x arr) = do
      arr' <- internaliseExpToVars "for_in_arr" arr
      arr_ts <- mapM lookupType arr'
      let w = arraysSize 0 arr_ts

      i <- newVName "i"

      ts <- mapM subExpType mergeinit
      bindingLoopParams sparams' mergepat ts $
        \shapepat mergepat' ->
          bindingLambdaParams [x] (map rowType arr_ts) $ \x_params -> do
            let loopvars = zip x_params arr'
            forLoop mergepat' shapepat mergeinit $
              I.ForLoop i Int64 w loopvars
    handleForm mergeinit (E.For i num_iterations) = do
      num_iterations' <- internaliseExp1 "upper_bound" num_iterations
      num_iterations_t <- I.subExpType num_iterations'
      it <- case num_iterations_t of
        I.Prim (IntType it) -> return it
        _ -> error "internaliseExp DoLoop: invalid type"

      ts <- mapM subExpType mergeinit
      bindingLoopParams sparams' mergepat ts $
        \shapepat mergepat' ->
          forLoop mergepat' shapepat mergeinit $
            I.ForLoop (E.identName i) it num_iterations' []
    handleForm mergeinit (E.While cond) = do
      ts <- mapM subExpType mergeinit
      bindingLoopParams sparams' mergepat ts $ \shapepat mergepat' -> do
        mergeinit_ts <- mapM subExpType mergeinit
        -- We need to insert 'cond' twice - once for the initial
        -- condition (do we enter the loop at all?), and once with the
        -- result values of the loop (do we continue into the next
        -- iteration?).  This is safe, as the type rules for the
        -- external language guarantees that 'cond' does not consume
        -- anything.
        shapeinit <- argShapes (map I.paramName shapepat) mergepat' mergeinit_ts

        (loop_initial_cond, init_loop_cond_bnds) <- collectStms $ do
          forM_ (zip shapepat shapeinit) $ \(p, se) ->
            letBindNames [paramName p] $ BasicOp $ SubExp se
          forM_ (zip mergepat' mergeinit) $ \(p, se) ->
            unless (se == I.Var (paramName p)) $
              letBindNames [paramName p] $
                BasicOp $
                  case se of
                    I.Var v
                      | not $ primType $ paramType p ->
                        Reshape (map DimCoercion $ arrayDims $ paramType p) v
                    _ -> SubExp se
          internaliseExp1 "loop_cond" cond

        addStms init_loop_cond_bnds

        bodyFromStms $ do
          ses <- internaliseExp "loopres" loopbody
          sets <- mapM subExpType ses
          loop_while <- newParam "loop_while" $ I.Prim I.Bool
          shapeargs <- argShapes (map I.paramName shapepat) mergepat' sets

          -- Careful not to clobber anything.
          loop_end_cond_body <- renameBody <=< buildBody_ $ do
            forM_ (zip shapepat shapeargs) $ \(p, se) ->
              unless (se == I.Var (paramName p)) $
                letBindNames [paramName p] $ BasicOp $ SubExp se
            forM_ (zip mergepat' ses) $ \(p, se) ->
              unless (se == I.Var (paramName p)) $
                letBindNames [paramName p] $
                  BasicOp $
                    case se of
                      I.Var v
                        | not $ primType $ paramType p ->
                          Reshape (map DimCoercion $ arrayDims $ paramType p) v
                      _ -> SubExp se
            internaliseExp "loop_cond" cond
          loop_end_cond <- bodyBind loop_end_cond_body

          return
            ( shapeargs ++ loop_end_cond ++ ses,
              ( I.WhileLoop $ I.paramName loop_while,
                shapepat,
                loop_while : mergepat',
                loop_initial_cond : mergeinit
              )
            )
internaliseAppExp desc (E.LetWith name src idxs ve body loc) = do
  let pat = E.Id (E.identName name) (E.identType name) loc
      src_t = E.fromStruct <$> E.identType src
      e = E.Update (E.Var (E.qualName $ E.identName src) src_t loc) idxs ve loc
  internaliseExp desc $
    E.AppExp
      (E.LetPat [] pat e body loc)
      (Info (AppRes (E.typeOf body) mempty))
internaliseAppExp desc (E.Match e cs _) = do
  ses <- internaliseExp (desc ++ "_scrutinee") e
  case NE.uncons cs of
    (CasePat pCase eCase _, Nothing) -> do
      (_, pertinent) <- generateCond pCase ses
      internalisePat' [] pCase pertinent eCase (internaliseExp desc)
    (c, Just cs') -> do
      let CasePat pLast eLast _ = NE.last cs'
      bFalse <- do
        (_, pertinent) <- generateCond pLast ses
        eLast' <- internalisePat' [] pLast pertinent eLast (internaliseBody desc)
        foldM (\bf c' -> eBody $ return $ generateCaseIf ses c' bf) eLast' $
          reverse $ NE.init cs'
      letTupExp' desc =<< generateCaseIf ses c bFalse
internaliseAppExp desc (E.If ce te fe _) =
  letTupExp' desc
    =<< eIf
      (BasicOp . SubExp <$> internaliseExp1 "cond" ce)
      (internaliseBody (desc <> "_t") te)
      (internaliseBody (desc <> "_f") fe)
internaliseAppExp _ e@E.BinOp {} =
  error $ "internaliseAppExp: Unexpected BinOp " ++ pretty e

internaliseExp :: String -> E.Exp -> InternaliseM [I.SubExp]
internaliseExp desc (E.Parens e _) =
  internaliseExp desc e
internaliseExp desc (E.QualParens _ e _) =
  internaliseExp desc e
internaliseExp desc (E.StringLit vs _) =
  fmap pure $
    letSubExp desc $
      I.BasicOp $ I.ArrayLit (map constant vs) $ I.Prim int8
internaliseExp _ (E.Var (E.QualName _ name) _ _) = do
  subst <- lookupSubst name
  case subst of
    Just substs -> return substs
    Nothing -> pure [I.Var name]
internaliseExp desc (E.AppExp e (Info appres)) = do
  ses <- internaliseAppExp desc e
  bindExtSizes appres ses
  pure ses

-- XXX: we map empty records and tuples to units, because otherwise
-- arrays of unit will lose their sizes.
internaliseExp _ (E.TupLit [] _) =
  return [constant UnitValue]
internaliseExp _ (E.RecordLit [] _) =
  return [constant UnitValue]
internaliseExp desc (E.TupLit es _) = concat <$> mapM (internaliseExp desc) es
internaliseExp desc (E.RecordLit orig_fields _) =
  concatMap snd . sortFields . M.unions <$> mapM internaliseField orig_fields
  where
    internaliseField (E.RecordFieldExplicit name e _) =
      M.singleton name <$> internaliseExp desc e
    internaliseField (E.RecordFieldImplicit name t loc) =
      internaliseField $
        E.RecordFieldExplicit
          (baseName name)
          (E.Var (E.qualName name) t loc)
          loc
internaliseExp desc (E.ArrayLit es (Info arr_t) loc)
  -- If this is a multidimensional array literal of primitives, we
  -- treat it specially by flattening it out followed by a reshape.
  -- This cuts down on the amount of statements that are produced, and
  -- thus allows us to efficiently handle huge array literals - a
  -- corner case, but an important one.
  | Just ((eshape, e') : es') <- mapM isArrayLiteral es,
    not $ null eshape,
    all ((eshape ==) . fst) es',
    Just basetype <- E.peelArray (length eshape) arr_t = do
    let flat_lit = E.ArrayLit (e' ++ concatMap snd es') (Info basetype) loc
        new_shape = length es : eshape
    flat_arrs <- internaliseExpToVars "flat_literal" flat_lit
    forM flat_arrs $ \flat_arr -> do
      flat_arr_t <- lookupType flat_arr
      let new_shape' =
            reshapeOuter
              (map (DimNew . intConst Int64 . toInteger) new_shape)
              1
              $ I.arrayShape flat_arr_t
      letSubExp desc $ I.BasicOp $ I.Reshape new_shape' flat_arr
  | otherwise = do
    es' <- mapM (internaliseExp "arr_elem") es
    arr_t_ext <- internaliseType $ E.toStruct arr_t

    rowtypes <-
      case mapM (fmap rowType . hasStaticShape . I.fromDecl) arr_t_ext of
        Just ts -> pure ts
        Nothing ->
          -- XXX: the monomorphiser may create single-element array
          -- literals with an unknown row type.  In those cases we
          -- need to look at the types of the actual elements.
          -- Fixing this in the monomorphiser is a lot more tricky
          -- than just working around it here.
          case es' of
            [] -> error $ "internaliseExp ArrayLit: existential type: " ++ pretty arr_t
            e' : _ -> mapM subExpType e'

    let arraylit ks rt = do
          ks' <-
            mapM
              ( ensureShape
                  "shape of element differs from shape of first element"
                  loc
                  rt
                  "elem_reshaped"
              )
              ks
          return $ I.BasicOp $ I.ArrayLit ks' rt

    letSubExps desc
      =<< if null es'
        then mapM (arraylit []) rowtypes
        else zipWithM arraylit (transpose es') rowtypes
  where
    isArrayLiteral :: E.Exp -> Maybe ([Int], [E.Exp])
    isArrayLiteral (E.ArrayLit inner_es _ _) = do
      (eshape, e) : inner_es' <- mapM isArrayLiteral inner_es
      guard $ all ((eshape ==) . fst) inner_es'
      return (length inner_es : eshape, e ++ concatMap snd inner_es')
    isArrayLiteral e =
      Just ([], [e])
internaliseExp desc (E.Ascript e _ _) =
  internaliseExp desc e
internaliseExp desc (E.Negate e _) = do
  e' <- internaliseExp1 "negate_arg" e
  et <- subExpType e'
  case et of
    I.Prim (I.IntType t) ->
      letTupExp' desc $ I.BasicOp $ I.BinOp (I.Sub t I.OverflowWrap) (I.intConst t 0) e'
    I.Prim (I.FloatType t) ->
      letTupExp' desc $ I.BasicOp $ I.BinOp (I.FSub t) (I.floatConst t 0) e'
    _ -> error "Futhark.Internalise.internaliseExp: non-numeric type in Negate"
internaliseExp desc (E.Update src slice ve loc) = do
  ves <- internaliseExp "lw_val" ve
  srcs <- internaliseExpToVars "src" src
  dims <- case srcs of
    [] -> return [] -- Will this happen?
    v : _ -> I.arrayDims <$> lookupType v
  (idxs', cs) <- internaliseSlice loc dims slice

  let comb sname ve' = do
        sname_t <- lookupType sname
        let full_slice = fullSlice sname_t idxs'
            rowtype = sname_t `setArrayDims` sliceDims full_slice
        ve'' <-
          ensureShape
            "shape of value does not match shape of source array"
            loc
            rowtype
            "lw_val_correct_shape"
            ve'
        letInPlace desc sname full_slice $ BasicOp $ SubExp ve''
  certifying cs $ map I.Var <$> zipWithM comb srcs ves
internaliseExp desc (E.RecordUpdate src fields ve _ _) = do
  src' <- internaliseExp desc src
  ve' <- internaliseExp desc ve
  replace (E.typeOf src `setAliases` ()) fields ve' src'
  where
    replace (E.Scalar (E.Record m)) (f : fs) ve' src'
      | Just t <- M.lookup f m = do
        i <-
          fmap sum $
            mapM (internalisedTypeSize . snd) $
              takeWhile ((/= f) . fst) $ sortFields m
        k <- internalisedTypeSize t
        let (bef, to_update, aft) = splitAt3 i k src'
        src'' <- replace t fs ve' to_update
        return $ bef ++ src'' ++ aft
    replace _ _ ve' _ = return ve'
internaliseExp desc (E.Attr attr e _) =
  local f $ internaliseExp desc e
  where
    attrs = oneAttr $ internaliseAttr attr
    f env
      | "unsafe" `inAttrs` attrs,
        not $ envSafe env =
        env {envDoBoundsChecks = False}
      | otherwise =
        env {envAttrs = envAttrs env <> attrs}
internaliseExp desc (E.Assert e1 e2 (Info check) loc) = do
  e1' <- internaliseExp1 "assert_cond" e1
  c <- assert "assert_c" e1' (errorMsg [ErrorString $ "Assertion is false: " <> check]) loc
  -- Make sure there are some bindings to certify.
  certifying c $ mapM rebind =<< internaliseExp desc e2
  where
    rebind v = do
      v' <- newVName "assert_res"
      letBindNames [v'] $ I.BasicOp $ I.SubExp v
      return $ I.Var v'
internaliseExp _ (E.Constr c es (Info (E.Scalar (E.Sum fs))) _) = do
  (ts, constr_map) <- internaliseSumType $ M.map (map E.toStruct) fs
  es' <- concat <$> mapM (internaliseExp "payload") es

  let noExt _ = return $ intConst Int64 0
  ts' <- instantiateShapes noExt $ map fromDecl ts

  case M.lookup c constr_map of
    Just (i, js) ->
      (intConst Int8 (toInteger i) :) <$> clauses 0 ts' (zip js es')
    Nothing ->
      error "internaliseExp Constr: missing constructor"
  where
    clauses j (t : ts) js_to_es
      | Just e <- j `lookup` js_to_es =
        (e :) <$> clauses (j + 1) ts js_to_es
      | otherwise = do
        blank <- letSubExp "zero" =<< eBlank t
        (blank :) <$> clauses (j + 1) ts js_to_es
    clauses _ [] _ =
      return []
internaliseExp _ (E.Constr _ _ (Info t) loc) =
  error $ "internaliseExp: constructor with type " ++ pretty t ++ " at " ++ locStr loc
-- The "interesting" cases are over, now it's mostly boilerplate.

internaliseExp _ (E.Literal v _) =
  return [I.Constant $ internalisePrimValue v]
internaliseExp _ (E.IntLit v (Info t) _) =
  case t of
    E.Scalar (E.Prim (E.Signed it)) ->
      return [I.Constant $ I.IntValue $ intValue it v]
    E.Scalar (E.Prim (E.Unsigned it)) ->
      return [I.Constant $ I.IntValue $ intValue it v]
    E.Scalar (E.Prim (E.FloatType ft)) ->
      return [I.Constant $ I.FloatValue $ floatValue ft v]
    _ -> error $ "internaliseExp: nonsensical type for integer literal: " ++ pretty t
internaliseExp _ (E.FloatLit v (Info t) _) =
  case t of
    E.Scalar (E.Prim (E.FloatType ft)) ->
      return [I.Constant $ I.FloatValue $ floatValue ft v]
    _ -> error $ "internaliseExp: nonsensical type for float literal: " ++ pretty t
-- Builtin operators are handled specially because they are
-- overloaded.
internaliseExp desc (E.Project k e (Info rt) _) = do
  n <- internalisedTypeSize $ rt `setAliases` ()
  i' <- fmap sum $
    mapM internalisedTypeSize $
      case E.typeOf e `setAliases` () of
        E.Scalar (Record fs) ->
          map snd $ takeWhile ((/= k) . fst) $ sortFields fs
        t -> [t]
  take n . drop i' <$> internaliseExp desc e
internaliseExp _ e@E.Lambda {} =
  error $ "internaliseExp: Unexpected lambda at " ++ locStr (srclocOf e)
internaliseExp _ e@E.OpSection {} =
  error $ "internaliseExp: Unexpected operator section at " ++ locStr (srclocOf e)
internaliseExp _ e@E.OpSectionLeft {} =
  error $ "internaliseExp: Unexpected left operator section at " ++ locStr (srclocOf e)
internaliseExp _ e@E.OpSectionRight {} =
  error $ "internaliseExp: Unexpected right operator section at " ++ locStr (srclocOf e)
internaliseExp _ e@E.ProjectSection {} =
  error $ "internaliseExp: Unexpected projection section at " ++ locStr (srclocOf e)
internaliseExp _ e@E.IndexSection {} =
  error $ "internaliseExp: Unexpected index section at " ++ locStr (srclocOf e)

internaliseArg :: String -> (E.Exp, Maybe VName) -> InternaliseM [SubExp]
internaliseArg desc (arg, argdim) = do
  arg' <- internaliseExp desc arg
  case (arg', argdim) of
    ([se], Just d) -> letBindNames [d] $ BasicOp $ SubExp se
    _ -> return ()
  return arg'

subExpPrimType :: I.SubExp -> InternaliseM I.PrimType
subExpPrimType = fmap I.elemType . subExpType

generateCond :: E.Pattern -> [I.SubExp] -> InternaliseM (I.SubExp, [I.SubExp])
generateCond orig_p orig_ses = do
  (cmps, pertinent, _) <- compares orig_p orig_ses
  cmp <- letSubExp "matches" =<< eAll cmps
  return (cmp, pertinent)
  where
    -- Literals are always primitive values.
    compares (E.PatternLit l t _) (se : ses) = do
      e' <- case l of
        PatLitPrim v -> pure $ constant $ internalisePrimValue v
        PatLitInt x -> internaliseExp1 "constant" $ E.IntLit x t mempty
        PatLitFloat x -> internaliseExp1 "constant" $ E.FloatLit x t mempty
      t' <- subExpPrimType se
      cmp <- letSubExp "match_lit" $ I.BasicOp $ I.CmpOp (I.CmpEq t') e' se
      return ([cmp], [se], ses)
    compares (E.PatternConstr c (Info (E.Scalar (E.Sum fs))) pats _) (se : ses) = do
      (payload_ts, m) <- internaliseSumType $ M.map (map toStruct) fs
      case M.lookup c m of
        Just (i, payload_is) -> do
          let i' = intConst Int8 $ toInteger i
          let (payload_ses, ses') = splitAt (length payload_ts) ses
          cmp <- letSubExp "match_constr" $ I.BasicOp $ I.CmpOp (I.CmpEq int8) i' se
          (cmps, pertinent, _) <- comparesMany pats $ map (payload_ses !!) payload_is
          return (cmp : cmps, pertinent, ses')
        Nothing ->
          error "generateCond: missing constructor"
    compares (E.PatternConstr _ (Info t) _ _) _ =
      error $ "generateCond: PatternConstr has nonsensical type: " ++ pretty t
    compares (E.Id _ t loc) ses =
      compares (E.Wildcard t loc) ses
    compares (E.Wildcard (Info t) _) ses = do
      n <- internalisedTypeSize $ E.toStruct t
      let (id_ses, rest_ses) = splitAt n ses
      return ([], id_ses, rest_ses)
    compares (E.PatternParens pat _) ses =
      compares pat ses
    -- XXX: treat empty tuples and records as bool.
    compares (E.TuplePattern [] loc) ses =
      compares (E.Wildcard (Info $ E.Scalar $ E.Prim E.Bool) loc) ses
    compares (E.RecordPattern [] loc) ses =
      compares (E.Wildcard (Info $ E.Scalar $ E.Prim E.Bool) loc) ses
    compares (E.TuplePattern pats _) ses =
      comparesMany pats ses
    compares (E.RecordPattern fs _) ses =
      comparesMany (map snd $ E.sortFields $ M.fromList fs) ses
    compares (E.PatternAscription pat _ _) ses =
      compares pat ses
    compares pat [] =
      error $ "generateCond: No values left for pattern " ++ pretty pat

    comparesMany [] ses = return ([], [], ses)
    comparesMany (pat : pats) ses = do
      (cmps1, pertinent1, ses') <- compares pat ses
      (cmps2, pertinent2, ses'') <- comparesMany pats ses'
      return
        ( cmps1 <> cmps2,
          pertinent1 <> pertinent2,
          ses''
        )

generateCaseIf :: [I.SubExp] -> Case -> I.Body -> InternaliseM I.Exp
generateCaseIf ses (CasePat p eCase _) bFail = do
  (cond, pertinent) <- generateCond p ses
  eCase' <- internalisePat' [] p pertinent eCase (internaliseBody "case")
  eIf (eSubExp cond) (return eCase') (return bFail)

internalisePat ::
  String ->
  [E.SizeBinder VName] ->
  E.Pattern ->
  E.Exp ->
  E.Exp ->
  (E.Exp -> InternaliseM a) ->
  InternaliseM a
internalisePat desc sizes p e body m = do
  ses <- internaliseExp desc' e
  internalisePat' sizes p ses body m
  where
    desc' = case S.toList $ E.patternIdents p of
      [v] -> baseString $ E.identName v
      _ -> desc

internalisePat' ::
  [E.SizeBinder VName] ->
  E.Pattern ->
  [I.SubExp] ->
  E.Exp ->
  (E.Exp -> InternaliseM a) ->
  InternaliseM a
internalisePat' sizes p ses body m = do
  ses_ts <- mapM subExpType ses
  stmPattern p ses_ts $ \pat_names -> do
    bindExtSizes (AppRes (E.patternType p) (map E.sizeName sizes)) ses
    forM_ (zip pat_names ses) $ \(v, se) ->
      letBindNames [v] $ I.BasicOp $ I.SubExp se
    m body

internaliseSlice ::
  SrcLoc ->
  [SubExp] ->
  [E.DimIndex] ->
  InternaliseM ([I.DimIndex SubExp], Certificates)
internaliseSlice loc dims idxs = do
  (idxs', oks, parts) <- unzip3 <$> zipWithM internaliseDimIndex dims idxs
  ok <- letSubExp "index_ok" =<< eAll oks
  let msg =
        errorMsg $
          ["Index ["] ++ intercalate [", "] parts
            ++ ["] out of bounds for array of shape ["]
            ++ intersperse "][" (map ErrorInt64 $ take (length idxs) dims)
            ++ ["]."]
  c <- assert "index_certs" ok msg loc
  return (idxs', c)

internaliseDimIndex ::
  SubExp ->
  E.DimIndex ->
  InternaliseM (I.DimIndex SubExp, SubExp, [ErrorMsgPart SubExp])
internaliseDimIndex w (E.DimFix i) = do
  (i', _) <- internaliseDimExp "i" i
  let lowerBound =
        I.BasicOp $
          I.CmpOp (I.CmpSle I.Int64) (I.constant (0 :: I.Int64)) i'
      upperBound =
        I.BasicOp $
          I.CmpOp (I.CmpSlt I.Int64) i' w
  ok <- letSubExp "bounds_check" =<< eBinOp I.LogAnd (pure lowerBound) (pure upperBound)
  return (I.DimFix i', ok, [ErrorInt64 i'])

-- Special-case an important common case that otherwise leads to horrible code.
internaliseDimIndex
  w
  ( E.DimSlice
      Nothing
      Nothing
      (Just (E.Negate (E.IntLit 1 _ _) _))
    ) = do
    w_minus_1 <-
      letSubExp "w_minus_1" $
        BasicOp $ I.BinOp (Sub Int64 I.OverflowWrap) w one
    return
      ( I.DimSlice w_minus_1 w $ intConst Int64 (-1),
        constant True,
        mempty
      )
    where
      one = constant (1 :: Int64)
internaliseDimIndex w (E.DimSlice i j s) = do
  s' <- maybe (return one) (fmap fst . internaliseDimExp "s") s
  s_sign <- letSubExp "s_sign" $ BasicOp $ I.UnOp (I.SSignum Int64) s'
  backwards <- letSubExp "backwards" $ I.BasicOp $ I.CmpOp (I.CmpEq int64) s_sign negone
  w_minus_1 <- letSubExp "w_minus_1" $ BasicOp $ I.BinOp (Sub Int64 I.OverflowWrap) w one
  let i_def =
        letSubExp "i_def" $
          I.If
            backwards
            (resultBody [w_minus_1])
            (resultBody [zero])
            $ ifCommon [I.Prim int64]
      j_def =
        letSubExp "j_def" $
          I.If
            backwards
            (resultBody [negone])
            (resultBody [w])
            $ ifCommon [I.Prim int64]
  i' <- maybe i_def (fmap fst . internaliseDimExp "i") i
  j' <- maybe j_def (fmap fst . internaliseDimExp "j") j
  j_m_i <- letSubExp "j_m_i" $ BasicOp $ I.BinOp (Sub Int64 I.OverflowWrap) j' i'
  -- Something like a division-rounding-up, but accomodating negative
  -- operands.
  let divRounding x y =
        eBinOp
          (SQuot Int64 Safe)
          ( eBinOp
              (Add Int64 I.OverflowWrap)
              x
              (eBinOp (Sub Int64 I.OverflowWrap) y (eSignum $ toExp s'))
          )
          y
  n <- letSubExp "n" =<< divRounding (toExp j_m_i) (toExp s')

  zero_stride <- letSubExp "zero_stride" $ I.BasicOp $ I.CmpOp (CmpEq int64) s_sign zero
  nonzero_stride <- letSubExp "nonzero_stride" $ I.BasicOp $ I.UnOp Not zero_stride

  -- Bounds checks depend on whether we are slicing forwards or
  -- backwards.  If forwards, we must check '0 <= i && i <= j'.  If
  -- backwards, '-1 <= j && j <= i'.  In both cases, we check '0 <=
  -- i+n*s && i+(n-1)*s < w'.  We only check if the slice is nonempty.
  empty_slice <- letSubExp "empty_slice" $ I.BasicOp $ I.CmpOp (CmpEq int64) n zero

  m <- letSubExp "m" $ I.BasicOp $ I.BinOp (Sub Int64 I.OverflowWrap) n one
  m_t_s <- letSubExp "m_t_s" $ I.BasicOp $ I.BinOp (Mul Int64 I.OverflowWrap) m s'
  i_p_m_t_s <- letSubExp "i_p_m_t_s" $ I.BasicOp $ I.BinOp (Add Int64 I.OverflowWrap) i' m_t_s
  zero_leq_i_p_m_t_s <-
    letSubExp "zero_leq_i_p_m_t_s" $
      I.BasicOp $ I.CmpOp (I.CmpSle Int64) zero i_p_m_t_s
  i_p_m_t_s_leq_w <-
    letSubExp "i_p_m_t_s_leq_w" $
      I.BasicOp $ I.CmpOp (I.CmpSle Int64) i_p_m_t_s w
  i_p_m_t_s_lth_w <-
    letSubExp "i_p_m_t_s_leq_w" $
      I.BasicOp $ I.CmpOp (I.CmpSlt Int64) i_p_m_t_s w

  zero_lte_i <- letSubExp "zero_lte_i" $ I.BasicOp $ I.CmpOp (I.CmpSle Int64) zero i'
  i_lte_j <- letSubExp "i_lte_j" $ I.BasicOp $ I.CmpOp (I.CmpSle Int64) i' j'
  forwards_ok <-
    letSubExp "forwards_ok"
      =<< eAll [zero_lte_i, zero_lte_i, i_lte_j, zero_leq_i_p_m_t_s, i_p_m_t_s_lth_w]

  negone_lte_j <- letSubExp "negone_lte_j" $ I.BasicOp $ I.CmpOp (I.CmpSle Int64) negone j'
  j_lte_i <- letSubExp "j_lte_i" $ I.BasicOp $ I.CmpOp (I.CmpSle Int64) j' i'
  backwards_ok <-
    letSubExp "backwards_ok"
      =<< eAll
        [negone_lte_j, negone_lte_j, j_lte_i, zero_leq_i_p_m_t_s, i_p_m_t_s_leq_w]

  slice_ok <-
    letSubExp "slice_ok" $
      I.If
        backwards
        (resultBody [backwards_ok])
        (resultBody [forwards_ok])
        $ ifCommon [I.Prim I.Bool]

  ok_or_empty <-
    letSubExp "ok_or_empty" $
      I.BasicOp $ I.BinOp I.LogOr empty_slice slice_ok

  acceptable <-
    letSubExp "slice_acceptable" $
      I.BasicOp $ I.BinOp I.LogAnd nonzero_stride ok_or_empty

  let parts = case (i, j, s) of
        (_, _, Just {}) ->
          [ maybe "" (const $ ErrorInt64 i') i,
            ":",
            maybe "" (const $ ErrorInt64 j') j,
            ":",
            ErrorInt64 s'
          ]
        (_, Just {}, _) ->
          [ maybe "" (const $ ErrorInt64 i') i,
            ":",
            ErrorInt64 j'
          ]
            ++ maybe mempty (const [":", ErrorInt64 s']) s
        (_, Nothing, Nothing) ->
          [ErrorInt64 i', ":"]
  return (I.DimSlice i' n s', acceptable, parts)
  where
    zero = constant (0 :: Int64)
    negone = constant (-1 :: Int64)
    one = constant (1 :: Int64)

internaliseScanOrReduce ::
  String ->
  String ->
  (SubExp -> I.Lambda -> [SubExp] -> [VName] -> InternaliseM (SOAC SOACS)) ->
  (E.Exp, E.Exp, E.Exp, SrcLoc) ->
  InternaliseM [SubExp]
internaliseScanOrReduce desc what f (lam, ne, arr, loc) = do
  arrs <- internaliseExpToVars (what ++ "_arr") arr
  nes <- internaliseExp (what ++ "_ne") ne
  nes' <- forM (zip nes arrs) $ \(ne', arr') -> do
    rowtype <- I.stripArray 1 <$> lookupType arr'
    ensureShape
      "Row shape of input array does not match shape of neutral element"
      loc
      rowtype
      (what ++ "_ne_right_shape")
      ne'
  nests <- mapM I.subExpType nes'
  arrts <- mapM lookupType arrs
  lam' <- internaliseFoldLambda internaliseLambda lam nests arrts
  w <- arraysSize 0 <$> mapM lookupType arrs
  letTupExp' desc . I.Op =<< f w lam' nes' arrs

internaliseHist ::
  String ->
  E.Exp ->
  E.Exp ->
  E.Exp ->
  E.Exp ->
  E.Exp ->
  E.Exp ->
  SrcLoc ->
  InternaliseM [SubExp]
internaliseHist desc rf hist op ne buckets img loc = do
  rf' <- internaliseExp1 "hist_rf" rf
  ne' <- internaliseExp "hist_ne" ne
  hist' <- internaliseExpToVars "hist_hist" hist
  buckets' <-
    letExp "hist_buckets" . BasicOp . SubExp
      =<< internaliseExp1 "hist_buckets" buckets
  img' <- internaliseExpToVars "hist_img" img

  -- reshape neutral element to have same size as the destination array
  ne_shp <- forM (zip ne' hist') $ \(n, h) -> do
    rowtype <- I.stripArray 1 <$> lookupType h
    ensureShape
      "Row shape of destination array does not match shape of neutral element"
      loc
      rowtype
      "hist_ne_right_shape"
      n
  ne_ts <- mapM I.subExpType ne_shp
  his_ts <- mapM lookupType hist'
  op' <- internaliseFoldLambda internaliseLambda op ne_ts his_ts

  -- reshape return type of bucket function to have same size as neutral element
  -- (modulo the index)
  bucket_param <- newParam "bucket_p" $ I.Prim int64
  img_params <- mapM (newParam "img_p" . rowType) =<< mapM lookupType img'
  let params = bucket_param : img_params
      rettype = I.Prim int64 : ne_ts
      body = mkBody mempty $ map (I.Var . paramName) params
  lam' <-
    mkLambda params $
      ensureResultShape
        "Row shape of value array does not match row shape of hist target"
        (srclocOf img)
        rettype
        =<< bodyBind body

  -- get sizes of histogram and image arrays
  w_hist <- arraysSize 0 <$> mapM lookupType hist'
  w_img <- arraysSize 0 <$> mapM lookupType img'

  -- Generate an assertion and reshapes to ensure that buckets' and
  -- img' are the same size.
  b_shape <- I.arrayShape <$> lookupType buckets'
  let b_w = shapeSize 0 b_shape
  cmp <- letSubExp "bucket_cmp" $ I.BasicOp $ I.CmpOp (I.CmpEq I.int64) b_w w_img
  c <-
    assert
      "bucket_cert"
      cmp
      "length of index and value array does not match"
      loc
  buckets'' <-
    certifying c $
      letExp (baseString buckets') $
        I.BasicOp $ I.Reshape (reshapeOuter [DimCoercion w_img] 1 b_shape) buckets'

  letTupExp' desc . I.Op $
    I.Hist w_img [HistOp w_hist rf' hist' ne_shp op'] lam' $ buckets'' : img'

internaliseStreamMap ::
  String ->
  StreamOrd ->
  E.Exp ->
  E.Exp ->
  InternaliseM [SubExp]
internaliseStreamMap desc o lam arr = do
  arrs <- internaliseExpToVars "stream_input" arr
  lam' <- internaliseStreamMapLambda internaliseLambda lam $ map I.Var arrs
  w <- arraysSize 0 <$> mapM lookupType arrs
  let form = I.Parallel o Commutative (I.Lambda [] (mkBody mempty []) [])
  letTupExp' desc $ I.Op $ I.Stream w arrs form [] lam'

internaliseStreamRed ::
  String ->
  StreamOrd ->
  Commutativity ->
  E.Exp ->
  E.Exp ->
  E.Exp ->
  InternaliseM [SubExp]
internaliseStreamRed desc o comm lam0 lam arr = do
  arrs <- internaliseExpToVars "stream_input" arr
  rowts <- mapM (fmap I.rowType . lookupType) arrs
  (lam_params, lam_body) <-
    internaliseStreamLambda internaliseLambda lam rowts
  let (chunk_param, _, lam_val_params) =
        partitionChunkedFoldParameters 0 lam_params

  -- Synthesize neutral elements by applying the fold function
  -- to an empty chunk.
  letBindNames [I.paramName chunk_param] $
    I.BasicOp $ I.SubExp $ constant (0 :: Int64)
  forM_ lam_val_params $ \p ->
    letBindNames [I.paramName p] $
      I.BasicOp $
        I.Scratch (I.elemType $ I.paramType p) $
          I.arrayDims $ I.paramType p
  nes <- bodyBind =<< renameBody lam_body

  nes_ts <- mapM I.subExpType nes
  outsz <- arraysSize 0 <$> mapM lookupType arrs
  let acc_arr_tps = [I.arrayOf t (I.Shape [outsz]) NoUniqueness | t <- nes_ts]
  lam0' <- internaliseFoldLambda internaliseLambda lam0 nes_ts acc_arr_tps

  let lam0_acc_params = take (length nes) $ I.lambdaParams lam0'
  lam_acc_params <- forM lam0_acc_params $ \p -> do
    name <- newVName $ baseString $ I.paramName p
    return p {I.paramName = name}

  -- Make sure the chunk size parameter comes first.
  let lam_params' = chunk_param : lam_acc_params ++ lam_val_params

  lam' <- mkLambda lam_params' $ do
    lam_res <- bodyBind lam_body
    lam_res' <-
      ensureArgShapes
        "shape of chunk function result does not match shape of initial value"
        (srclocOf lam)
        []
        (map I.typeOf $ I.lambdaParams lam0')
        lam_res
    ensureResultShape
      "shape of result does not match shape of initial value"
      (srclocOf lam0)
      nes_ts
      =<< ( eLambda lam0' . map eSubExp $
              map (I.Var . paramName) lam_acc_params ++ lam_res'
          )

  let form = I.Parallel o comm lam0'
  w <- arraysSize 0 <$> mapM lookupType arrs
  letTupExp' desc $ I.Op $ I.Stream w arrs form nes lam'

internaliseStreamAcc ::
  String ->
  E.Exp ->
  Maybe (E.Exp, E.Exp) ->
  E.Exp ->
  E.Exp ->
  InternaliseM [SubExp]
internaliseStreamAcc desc dest op lam bs = do
  dest' <- internaliseExpToVars "scatter_dest" dest
  bs' <- internaliseExpToVars "scatter_input" bs

  acc_cert_v <- newVName "acc_cert"
  dest_ts <- mapM lookupType dest'
  let dest_w = arraysSize 0 dest_ts
      acc_t = Acc acc_cert_v (Shape [dest_w]) (map rowType dest_ts) NoUniqueness
  acc_p <- newParam "acc_p" acc_t
  withacc_lam <- mkLambda [Param acc_cert_v (I.Prim I.Unit), acc_p] $ do
    lam' <-
      internaliseMapLambda internaliseLambda lam $
        map I.Var $ paramName acc_p : bs'
    w <- arraysSize 0 <$> mapM lookupType bs'
    letTupExp' "acc_res" $ I.Op $ I.Screma w (paramName acc_p : bs') (I.mapSOAC lam')

  op' <-
    case op of
      Just (op_lam, ne) -> do
        ne' <- internaliseExp "hist_ne" ne
        ne_ts <- mapM I.subExpType ne'
        (lam_params, lam_body, lam_rettype) <-
          internaliseLambda op_lam $ ne_ts ++ ne_ts
        idxp <- newParam "idx" $ I.Prim int64
        let op_lam' = I.Lambda (idxp : lam_params) lam_body lam_rettype
        return $ Just (op_lam', ne')
      Nothing ->
        return Nothing

  destw <- arraysSize 0 <$> mapM lookupType dest'
  fmap (map I.Var) $
    letTupExp desc $ WithAcc [(Shape [destw], dest', op')] withacc_lam

internaliseExp1 :: String -> E.Exp -> InternaliseM I.SubExp
internaliseExp1 desc e = do
  vs <- internaliseExp desc e
  case vs of
    [se] -> return se
    _ -> error "Internalise.internaliseExp1: was passed not just a single subexpression"

-- | Promote to dimension type as appropriate for the original type.
-- Also return original type.
internaliseDimExp :: String -> E.Exp -> InternaliseM (I.SubExp, IntType)
internaliseDimExp s e = do
  e' <- internaliseExp1 s e
  case E.typeOf e of
    E.Scalar (E.Prim (Signed it)) -> (,it) <$> asIntS Int64 e'
    _ -> error "internaliseDimExp: bad type"

internaliseExpToVars :: String -> E.Exp -> InternaliseM [I.VName]
internaliseExpToVars desc e =
  mapM asIdent =<< internaliseExp desc e
  where
    asIdent (I.Var v) = return v
    asIdent se = letExp desc $ I.BasicOp $ I.SubExp se

internaliseOperation ::
  String ->
  E.Exp ->
  (I.VName -> InternaliseM I.BasicOp) ->
  InternaliseM [I.SubExp]
internaliseOperation s e op = do
  vs <- internaliseExpToVars s e
  letSubExps s =<< mapM (fmap I.BasicOp . op) vs

certifyingNonzero ::
  SrcLoc ->
  IntType ->
  SubExp ->
  InternaliseM a ->
  InternaliseM a
certifyingNonzero loc t x m = do
  zero <-
    letSubExp "zero" $
      I.BasicOp $
        CmpOp (CmpEq (IntType t)) x (intConst t 0)
  nonzero <- letSubExp "nonzero" $ I.BasicOp $ UnOp Not zero
  c <- assert "nonzero_cert" nonzero "division by zero" loc
  certifying c m

certifyingNonnegative ::
  SrcLoc ->
  IntType ->
  SubExp ->
  InternaliseM a ->
  InternaliseM a
certifyingNonnegative loc t x m = do
  nonnegative <-
    letSubExp "nonnegative" $
      I.BasicOp $
        CmpOp (CmpSle t) (intConst t 0) x
  c <- assert "nonzero_cert" nonnegative "negative exponent" loc
  certifying c m

internaliseBinOp ::
  SrcLoc ->
  String ->
  E.BinOp ->
  I.SubExp ->
  I.SubExp ->
  E.PrimType ->
  E.PrimType ->
  InternaliseM [I.SubExp]
internaliseBinOp _ desc E.Plus x y (E.Signed t) _ =
  simpleBinOp desc (I.Add t I.OverflowWrap) x y
internaliseBinOp _ desc E.Plus x y (E.Unsigned t) _ =
  simpleBinOp desc (I.Add t I.OverflowWrap) x y
internaliseBinOp _ desc E.Plus x y (E.FloatType t) _ =
  simpleBinOp desc (I.FAdd t) x y
internaliseBinOp _ desc E.Minus x y (E.Signed t) _ =
  simpleBinOp desc (I.Sub t I.OverflowWrap) x y
internaliseBinOp _ desc E.Minus x y (E.Unsigned t) _ =
  simpleBinOp desc (I.Sub t I.OverflowWrap) x y
internaliseBinOp _ desc E.Minus x y (E.FloatType t) _ =
  simpleBinOp desc (I.FSub t) x y
internaliseBinOp _ desc E.Times x y (E.Signed t) _ =
  simpleBinOp desc (I.Mul t I.OverflowWrap) x y
internaliseBinOp _ desc E.Times x y (E.Unsigned t) _ =
  simpleBinOp desc (I.Mul t I.OverflowWrap) x y
internaliseBinOp _ desc E.Times x y (E.FloatType t) _ =
  simpleBinOp desc (I.FMul t) x y
internaliseBinOp loc desc E.Divide x y (E.Signed t) _ =
  certifyingNonzero loc t y $
    simpleBinOp desc (I.SDiv t I.Unsafe) x y
internaliseBinOp loc desc E.Divide x y (E.Unsigned t) _ =
  certifyingNonzero loc t y $
    simpleBinOp desc (I.UDiv t I.Unsafe) x y
internaliseBinOp _ desc E.Divide x y (E.FloatType t) _ =
  simpleBinOp desc (I.FDiv t) x y
internaliseBinOp _ desc E.Pow x y (E.FloatType t) _ =
  simpleBinOp desc (I.FPow t) x y
internaliseBinOp loc desc E.Pow x y (E.Signed t) _ =
  certifyingNonnegative loc t y $
    simpleBinOp desc (I.Pow t) x y
internaliseBinOp _ desc E.Pow x y (E.Unsigned t) _ =
  simpleBinOp desc (I.Pow t) x y
internaliseBinOp loc desc E.Mod x y (E.Signed t) _ =
  certifyingNonzero loc t y $
    simpleBinOp desc (I.SMod t I.Unsafe) x y
internaliseBinOp loc desc E.Mod x y (E.Unsigned t) _ =
  certifyingNonzero loc t y $
    simpleBinOp desc (I.UMod t I.Unsafe) x y
internaliseBinOp _ desc E.Mod x y (E.FloatType t) _ =
  simpleBinOp desc (I.FMod t) x y
internaliseBinOp loc desc E.Quot x y (E.Signed t) _ =
  certifyingNonzero loc t y $
    simpleBinOp desc (I.SQuot t I.Unsafe) x y
internaliseBinOp loc desc E.Quot x y (E.Unsigned t) _ =
  certifyingNonzero loc t y $
    simpleBinOp desc (I.UDiv t I.Unsafe) x y
internaliseBinOp loc desc E.Rem x y (E.Signed t) _ =
  certifyingNonzero loc t y $
    simpleBinOp desc (I.SRem t I.Unsafe) x y
internaliseBinOp loc desc E.Rem x y (E.Unsigned t) _ =
  certifyingNonzero loc t y $
    simpleBinOp desc (I.UMod t I.Unsafe) x y
internaliseBinOp _ desc E.ShiftR x y (E.Signed t) _ =
  simpleBinOp desc (I.AShr t) x y
internaliseBinOp _ desc E.ShiftR x y (E.Unsigned t) _ =
  simpleBinOp desc (I.LShr t) x y
internaliseBinOp _ desc E.ShiftL x y (E.Signed t) _ =
  simpleBinOp desc (I.Shl t) x y
internaliseBinOp _ desc E.ShiftL x y (E.Unsigned t) _ =
  simpleBinOp desc (I.Shl t) x y
internaliseBinOp _ desc E.Band x y (E.Signed t) _ =
  simpleBinOp desc (I.And t) x y
internaliseBinOp _ desc E.Band x y (E.Unsigned t) _ =
  simpleBinOp desc (I.And t) x y
internaliseBinOp _ desc E.Xor x y (E.Signed t) _ =
  simpleBinOp desc (I.Xor t) x y
internaliseBinOp _ desc E.Xor x y (E.Unsigned t) _ =
  simpleBinOp desc (I.Xor t) x y
internaliseBinOp _ desc E.Bor x y (E.Signed t) _ =
  simpleBinOp desc (I.Or t) x y
internaliseBinOp _ desc E.Bor x y (E.Unsigned t) _ =
  simpleBinOp desc (I.Or t) x y
internaliseBinOp _ desc E.Equal x y t _ =
  simpleCmpOp desc (I.CmpEq $ internalisePrimType t) x y
internaliseBinOp _ desc E.NotEqual x y t _ = do
  eq <- letSubExp (desc ++ "true") $ I.BasicOp $ I.CmpOp (I.CmpEq $ internalisePrimType t) x y
  fmap pure $ letSubExp desc $ I.BasicOp $ I.UnOp I.Not eq
internaliseBinOp _ desc E.Less x y (E.Signed t) _ =
  simpleCmpOp desc (I.CmpSlt t) x y
internaliseBinOp _ desc E.Less x y (E.Unsigned t) _ =
  simpleCmpOp desc (I.CmpUlt t) x y
internaliseBinOp _ desc E.Leq x y (E.Signed t) _ =
  simpleCmpOp desc (I.CmpSle t) x y
internaliseBinOp _ desc E.Leq x y (E.Unsigned t) _ =
  simpleCmpOp desc (I.CmpUle t) x y
internaliseBinOp _ desc E.Greater x y (E.Signed t) _ =
  simpleCmpOp desc (I.CmpSlt t) y x -- Note the swapped x and y
internaliseBinOp _ desc E.Greater x y (E.Unsigned t) _ =
  simpleCmpOp desc (I.CmpUlt t) y x -- Note the swapped x and y
internaliseBinOp _ desc E.Geq x y (E.Signed t) _ =
  simpleCmpOp desc (I.CmpSle t) y x -- Note the swapped x and y
internaliseBinOp _ desc E.Geq x y (E.Unsigned t) _ =
  simpleCmpOp desc (I.CmpUle t) y x -- Note the swapped x and y
internaliseBinOp _ desc E.Less x y (E.FloatType t) _ =
  simpleCmpOp desc (I.FCmpLt t) x y
internaliseBinOp _ desc E.Leq x y (E.FloatType t) _ =
  simpleCmpOp desc (I.FCmpLe t) x y
internaliseBinOp _ desc E.Greater x y (E.FloatType t) _ =
  simpleCmpOp desc (I.FCmpLt t) y x -- Note the swapped x and y
internaliseBinOp _ desc E.Geq x y (E.FloatType t) _ =
  simpleCmpOp desc (I.FCmpLe t) y x -- Note the swapped x and y

-- Relational operators for booleans.
internaliseBinOp _ desc E.Less x y E.Bool _ =
  simpleCmpOp desc I.CmpLlt x y
internaliseBinOp _ desc E.Leq x y E.Bool _ =
  simpleCmpOp desc I.CmpLle x y
internaliseBinOp _ desc E.Greater x y E.Bool _ =
  simpleCmpOp desc I.CmpLlt y x -- Note the swapped x and y
internaliseBinOp _ desc E.Geq x y E.Bool _ =
  simpleCmpOp desc I.CmpLle y x -- Note the swapped x and y
internaliseBinOp _ _ op _ _ t1 t2 =
  error $
    "Invalid binary operator " ++ pretty op
      ++ " with operand types "
      ++ pretty t1
      ++ ", "
      ++ pretty t2

simpleBinOp ::
  String ->
  I.BinOp ->
  I.SubExp ->
  I.SubExp ->
  InternaliseM [I.SubExp]
simpleBinOp desc bop x y =
  letTupExp' desc $ I.BasicOp $ I.BinOp bop x y

simpleCmpOp ::
  String ->
  I.CmpOp ->
  I.SubExp ->
  I.SubExp ->
  InternaliseM [I.SubExp]
simpleCmpOp desc op x y =
  letTupExp' desc $ I.BasicOp $ I.CmpOp op x y

findFuncall ::
  E.AppExp ->
  InternaliseM
    ( E.QualName VName,
      [(E.Exp, Maybe VName)]
    )
findFuncall (E.Apply f arg (Info (_, argext)) _)
  | E.AppExp f_e _ <- f = do
    (fname, args) <- findFuncall f_e
    return (fname, args ++ [(arg, argext)])
  | E.Var fname _ _ <- f =
    return (fname, [(arg, argext)])
findFuncall e =
  error $ "Invalid function expression in application: " ++ pretty e

-- The type of a body.  Watch out: this only works for the degenerate
-- case where the body does not already return its context.
bodyExtType :: Body -> InternaliseM [ExtType]
bodyExtType (Body _ stms res) =
  existentialiseExtTypes (M.keys stmsscope) . staticShapes
    <$> extendedScope (traverse subExpType res) stmsscope
  where
    stmsscope = scopeOf stms

internaliseLambda :: InternaliseLambda
internaliseLambda (E.Parens e _) rowtypes =
  internaliseLambda e rowtypes
internaliseLambda (E.Lambda params body _ (Info (_, RetType _ rettype)) _) rowtypes =
  bindingLambdaParams params rowtypes $ \params' -> do
    body' <- internaliseBody "lam" body
    rettype' <- internaliseLambdaReturnType rettype =<< bodyExtType body'
    return (params', body', rettype')
internaliseLambda e _ = error $ "internaliseLambda: unexpected expression:\n" ++ pretty e

-- | Some operators and functions are overloaded or otherwise special
-- - we detect and treat them here.
isOverloadedFunction ::
  E.QualName VName ->
  [E.Exp] ->
  SrcLoc ->
  Maybe (String -> InternaliseM [SubExp])
isOverloadedFunction qname args loc = do
  guard $ baseTag (qualLeaf qname) <= maxIntrinsicTag
  let handlers =
        [ handleSign,
          handleIntrinsicOps,
          handleOps,
          handleSOACs,
          handleAccs,
          handleRest
        ]
  msum [h args $ baseString $ qualLeaf qname | h <- handlers]
  where
    handleSign [x] "sign_i8" = Just $ toSigned I.Int8 x
    handleSign [x] "sign_i16" = Just $ toSigned I.Int16 x
    handleSign [x] "sign_i32" = Just $ toSigned I.Int32 x
    handleSign [x] "sign_i64" = Just $ toSigned I.Int64 x
    handleSign [x] "unsign_i8" = Just $ toUnsigned I.Int8 x
    handleSign [x] "unsign_i16" = Just $ toUnsigned I.Int16 x
    handleSign [x] "unsign_i32" = Just $ toUnsigned I.Int32 x
    handleSign [x] "unsign_i64" = Just $ toUnsigned I.Int64 x
    handleSign _ _ = Nothing

    handleIntrinsicOps [x] s
      | Just unop <- find ((== s) . pretty) allUnOps = Just $ \desc -> do
        x' <- internaliseExp1 "x" x
        fmap pure $ letSubExp desc $ I.BasicOp $ I.UnOp unop x'
    handleIntrinsicOps [TupLit [x, y] _] s
      | Just bop <- find ((== s) . pretty) allBinOps = Just $ \desc -> do
        x' <- internaliseExp1 "x" x
        y' <- internaliseExp1 "y" y
        fmap pure $ letSubExp desc $ I.BasicOp $ I.BinOp bop x' y'
      | Just cmp <- find ((== s) . pretty) allCmpOps = Just $ \desc -> do
        x' <- internaliseExp1 "x" x
        y' <- internaliseExp1 "y" y
        fmap pure $ letSubExp desc $ I.BasicOp $ I.CmpOp cmp x' y'
    handleIntrinsicOps [x] s
      | Just conv <- find ((== s) . pretty) allConvOps = Just $ \desc -> do
        x' <- internaliseExp1 "x" x
        fmap pure $ letSubExp desc $ I.BasicOp $ I.ConvOp conv x'
    handleIntrinsicOps _ _ = Nothing

    -- Short-circuiting operators are magical.
    handleOps [x, y] "&&" = Just $ \desc ->
      internaliseExp desc $
        E.AppExp
          (E.If x y (E.Literal (E.BoolValue False) mempty) mempty)
          (Info $ AppRes (E.Scalar $ E.Prim E.Bool) [])
    handleOps [x, y] "||" = Just $ \desc ->
      internaliseExp desc $
        E.AppExp
          (E.If x (E.Literal (E.BoolValue True) mempty) y mempty)
          (Info $ AppRes (E.Scalar $ E.Prim E.Bool) [])
    -- Handle equality and inequality specially, to treat the case of
    -- arrays.
    handleOps [xe, ye] op
      | Just cmp_f <- isEqlOp op = Just $ \desc -> do
        xe' <- internaliseExp "x" xe
        ye' <- internaliseExp "y" ye
        rs <- zipWithM (doComparison desc) xe' ye'
        cmp_f desc =<< letSubExp "eq" =<< eAll rs
      where
        isEqlOp "!=" = Just $ \desc eq ->
          letTupExp' desc $ I.BasicOp $ I.UnOp I.Not eq
        isEqlOp "==" = Just $ \_ eq ->
          return [eq]
        isEqlOp _ = Nothing

        doComparison desc x y = do
          x_t <- I.subExpType x
          y_t <- I.subExpType y
          case x_t of
            I.Prim t -> letSubExp desc $ I.BasicOp $ I.CmpOp (I.CmpEq t) x y
            _ -> do
              let x_dims = I.arrayDims x_t
                  y_dims = I.arrayDims y_t
              dims_match <- forM (zip x_dims y_dims) $ \(x_dim, y_dim) ->
                letSubExp "dim_eq" $ I.BasicOp $ I.CmpOp (I.CmpEq int64) x_dim y_dim
              shapes_match <- letSubExp "shapes_match" =<< eAll dims_match
              compare_elems_body <- runBodyBinder $ do
                -- Flatten both x and y.
                x_num_elems <-
                  letSubExp "x_num_elems"
                    =<< foldBinOp (I.Mul Int64 I.OverflowUndef) (constant (1 :: Int64)) x_dims
                x' <- letExp "x" $ I.BasicOp $ I.SubExp x
                y' <- letExp "x" $ I.BasicOp $ I.SubExp y
                x_flat <- letExp "x_flat" $ I.BasicOp $ I.Reshape [I.DimNew x_num_elems] x'
                y_flat <- letExp "y_flat" $ I.BasicOp $ I.Reshape [I.DimNew x_num_elems] y'

                -- Compare the elements.
                cmp_lam <- cmpOpLambda $ I.CmpEq (elemType x_t)
                cmps <-
                  letExp "cmps" $
                    I.Op $
                      I.Screma x_num_elems [x_flat, y_flat] (I.mapSOAC cmp_lam)

                -- Check that all were equal.
                and_lam <- binOpLambda I.LogAnd I.Bool
                reduce <- I.reduceSOAC [Reduce Commutative and_lam [constant True]]
                all_equal <- letSubExp "all_equal" $ I.Op $ I.Screma x_num_elems [cmps] reduce
                return $ resultBody [all_equal]

              letSubExp "arrays_equal" $
                I.If shapes_match compare_elems_body (resultBody [constant False]) $
                  ifCommon [I.Prim I.Bool]
    handleOps [x, y] name
      | Just bop <- find ((name ==) . pretty) [minBound .. maxBound :: E.BinOp] =
        Just $ \desc -> do
          x' <- internaliseExp1 "x" x
          y' <- internaliseExp1 "y" y
          case (E.typeOf x, E.typeOf y) of
            (E.Scalar (E.Prim t1), E.Scalar (E.Prim t2)) ->
              internaliseBinOp loc desc bop x' y' t1 t2
            _ -> error "Futhark.Internalise.internaliseExp: non-primitive type in BinOp."
    handleOps _ _ = Nothing

    handleSOACs [TupLit [lam, arr] _] "map" = Just $ \desc -> do
      arr' <- internaliseExpToVars "map_arr" arr
      lam' <- internaliseMapLambda internaliseLambda lam $ map I.Var arr'
      w <- arraysSize 0 <$> mapM lookupType arr'
      letTupExp' desc $
        I.Op $
          I.Screma w arr' (I.mapSOAC lam')
    handleSOACs [TupLit [k, lam, arr] _] "partition" = do
      k' <- fromIntegral <$> fromInt32 k
      Just $ \_desc -> do
        arrs <- internaliseExpToVars "partition_input" arr
        lam' <- internalisePartitionLambda internaliseLambda k' lam $ map I.Var arrs
        uncurry (++) <$> partitionWithSOACS (fromIntegral k') lam' arrs
      where
        fromInt32 (Literal (SignedValue (Int32Value k')) _) = Just k'
        fromInt32 (IntLit k' (Info (E.Scalar (E.Prim (Signed Int32)))) _) = Just $ fromInteger k'
        fromInt32 _ = Nothing
    handleSOACs [TupLit [lam, ne, arr] _] "reduce" = Just $ \desc ->
      internaliseScanOrReduce desc "reduce" reduce (lam, ne, arr, loc)
      where
        reduce w red_lam nes arrs =
          I.Screma w arrs
            <$> I.reduceSOAC [Reduce Noncommutative red_lam nes]
    handleSOACs [TupLit [lam, ne, arr] _] "reduce_comm" = Just $ \desc ->
      internaliseScanOrReduce desc "reduce" reduce (lam, ne, arr, loc)
      where
        reduce w red_lam nes arrs =
          I.Screma w arrs
            <$> I.reduceSOAC [Reduce Commutative red_lam nes]
    handleSOACs [TupLit [lam, ne, arr] _] "scan" = Just $ \desc ->
      internaliseScanOrReduce desc "scan" reduce (lam, ne, arr, loc)
      where
        reduce w scan_lam nes arrs =
          I.Screma w arrs <$> I.scanSOAC [Scan scan_lam nes]
    handleSOACs [TupLit [op, f, arr] _] "reduce_stream" = Just $ \desc ->
      internaliseStreamRed desc InOrder Noncommutative op f arr
    handleSOACs [TupLit [op, f, arr] _] "reduce_stream_per" = Just $ \desc ->
      internaliseStreamRed desc Disorder Commutative op f arr
    handleSOACs [TupLit [f, arr] _] "map_stream" = Just $ \desc ->
      internaliseStreamMap desc InOrder f arr
    handleSOACs [TupLit [f, arr] _] "map_stream_per" = Just $ \desc ->
      internaliseStreamMap desc Disorder f arr
    handleSOACs [TupLit [rf, dest, op, ne, buckets, img] _] "hist" = Just $ \desc ->
      internaliseHist desc rf dest op ne buckets img loc
    handleSOACs _ _ = Nothing

    handleAccs [TupLit [dest, f, bs] _] "scatter_stream" = Just $ \desc ->
      internaliseStreamAcc desc dest Nothing f bs
    handleAccs [TupLit [dest, op, ne, f, bs] _] "hist_stream" = Just $ \desc ->
      internaliseStreamAcc desc dest (Just (op, ne)) f bs
    handleAccs [TupLit [acc, i, v] _] "acc_write" = Just $ \desc -> do
      acc' <- head <$> internaliseExpToVars "acc" acc
      i' <- internaliseExp1 "acc_i" i
      vs <- internaliseExp "acc_v" v
      fmap pure $ letSubExp desc $ BasicOp $ UpdateAcc acc' [i'] vs
    handleAccs _ _ = Nothing

    handleRest [x] "!" = Just $ complementF x
    handleRest [x] "opaque" = Just $ \desc ->
      mapM (letSubExp desc . BasicOp . Opaque) =<< internaliseExp "opaque_arg" x
    handleRest [E.TupLit [a, si, v] _] "scatter" = Just $ scatterF 1 a si v
    handleRest [E.TupLit [a, si, v] _] "scatter_2d" = Just $ scatterF 2 a si v
    handleRest [E.TupLit [a, si, v] _] "scatter_3d" = Just $ scatterF 3 a si v
    handleRest [E.TupLit [n, m, arr] _] "unflatten" = Just $ \desc -> do
      arrs <- internaliseExpToVars "unflatten_arr" arr
      n' <- internaliseExp1 "n" n
      m' <- internaliseExp1 "m" m
      -- The unflattened dimension needs to have the same number of elements
      -- as the original dimension.
      old_dim <- I.arraysSize 0 <$> mapM lookupType arrs
      dim_ok <-
        letSubExp "dim_ok"
          =<< eCmpOp
            (I.CmpEq I.int64)
            (eBinOp (I.Mul Int64 I.OverflowUndef) (eSubExp n') (eSubExp m'))
            (eSubExp old_dim)
      dim_ok_cert <-
        assert
          "dim_ok_cert"
          dim_ok
          "new shape has different number of elements than old shape"
          loc
      certifying dim_ok_cert $
        forM arrs $ \arr' -> do
          arr_t <- lookupType arr'
          letSubExp desc $
            I.BasicOp $
              I.Reshape (reshapeOuter [DimNew n', DimNew m'] 1 $ I.arrayShape arr_t) arr'
    handleRest [arr] "flatten" = Just $ \desc -> do
      arrs <- internaliseExpToVars "flatten_arr" arr
      forM arrs $ \arr' -> do
        arr_t <- lookupType arr'
        let n = arraySize 0 arr_t
            m = arraySize 1 arr_t
        k <- letSubExp "flat_dim" $ I.BasicOp $ I.BinOp (Mul Int64 I.OverflowUndef) n m
        letSubExp desc $
          I.BasicOp $
            I.Reshape (reshapeOuter [DimNew k] 2 $ I.arrayShape arr_t) arr'
    handleRest [TupLit [x, y] _] "concat" = Just $ \desc -> do
      xs <- internaliseExpToVars "concat_x" x
      ys <- internaliseExpToVars "concat_y" y
      outer_size <- arraysSize 0 <$> mapM lookupType xs
      let sumdims xsize ysize =
            letSubExp "conc_tmp" $
              I.BasicOp $
                I.BinOp (I.Add I.Int64 I.OverflowUndef) xsize ysize
      ressize <-
        foldM sumdims outer_size
          =<< mapM (fmap (arraysSize 0) . mapM lookupType) [ys]

      let conc xarr yarr =
            I.BasicOp $ I.Concat 0 xarr [yarr] ressize
      letSubExps desc $ zipWith conc xs ys
    handleRest [TupLit [offset, e] _] "rotate" = Just $ \desc -> do
      offset' <- internaliseExp1 "rotation_offset" offset
      internaliseOperation desc e $ \v -> do
        r <- I.arrayRank <$> lookupType v
        let zero = intConst Int64 0
            offsets = offset' : replicate (r -1) zero
        return $ I.Rotate offsets v
    handleRest [e] "transpose" = Just $ \desc ->
      internaliseOperation desc e $ \v -> do
        r <- I.arrayRank <$> lookupType v
        return $ I.Rearrange ([1, 0] ++ [2 .. r -1]) v
    handleRest [TupLit [x, y] _] "zip" = Just $ \desc ->
      mapM (letSubExp "zip_copy" . BasicOp . Copy)
        =<< ( (++)
                <$> internaliseExpToVars (desc ++ "_zip_x") x
                <*> internaliseExpToVars (desc ++ "_zip_y") y
            )
    handleRest [x] "unzip" = Just $ flip internaliseExp x
    handleRest [x] "trace" = Just $ flip internaliseExp x
    handleRest [x] "break" = Just $ flip internaliseExp x
    handleRest _ _ = Nothing

    toSigned int_to e desc = do
      e' <- internaliseExp1 "trunc_arg" e
      case E.typeOf e of
        E.Scalar (E.Prim E.Bool) ->
          letTupExp' desc $
            I.If
              e'
              (resultBody [intConst int_to 1])
              (resultBody [intConst int_to 0])
              $ ifCommon [I.Prim $ I.IntType int_to]
        E.Scalar (E.Prim (E.Signed int_from)) ->
          letTupExp' desc $ I.BasicOp $ I.ConvOp (I.SExt int_from int_to) e'
        E.Scalar (E.Prim (E.Unsigned int_from)) ->
          letTupExp' desc $ I.BasicOp $ I.ConvOp (I.ZExt int_from int_to) e'
        E.Scalar (E.Prim (E.FloatType float_from)) ->
          letTupExp' desc $ I.BasicOp $ I.ConvOp (I.FPToSI float_from int_to) e'
        _ -> error "Futhark.Internalise: non-numeric type in ToSigned"

    toUnsigned int_to e desc = do
      e' <- internaliseExp1 "trunc_arg" e
      case E.typeOf e of
        E.Scalar (E.Prim E.Bool) ->
          letTupExp' desc $
            I.If
              e'
              (resultBody [intConst int_to 1])
              (resultBody [intConst int_to 0])
              $ ifCommon [I.Prim $ I.IntType int_to]
        E.Scalar (E.Prim (E.Signed int_from)) ->
          letTupExp' desc $ I.BasicOp $ I.ConvOp (I.ZExt int_from int_to) e'
        E.Scalar (E.Prim (E.Unsigned int_from)) ->
          letTupExp' desc $ I.BasicOp $ I.ConvOp (I.ZExt int_from int_to) e'
        E.Scalar (E.Prim (E.FloatType float_from)) ->
          letTupExp' desc $ I.BasicOp $ I.ConvOp (I.FPToUI float_from int_to) e'
        _ -> error "Futhark.Internalise.internaliseExp: non-numeric type in ToUnsigned"

    complementF e desc = do
      e' <- internaliseExp1 "complement_arg" e
      et <- subExpType e'
      case et of
        I.Prim (I.IntType t) ->
          letTupExp' desc $ I.BasicOp $ I.UnOp (I.Complement t) e'
        I.Prim I.Bool ->
          letTupExp' desc $ I.BasicOp $ I.UnOp I.Not e'
        _ ->
          error "Futhark.Internalise.internaliseExp: non-int/bool type in Complement"

    scatterF dim a si v desc = do
      si' <- internaliseExpToVars "write_arg_i" si
      svs <- internaliseExpToVars "write_arg_v" v
      sas <- internaliseExpToVars "write_arg_a" a

      si_w <- I.arraysSize 0 <$> mapM lookupType si'
      sv_ts <- mapM lookupType svs

      svs' <- forM (zip svs sv_ts) $ \(sv, sv_t) -> do
        let sv_shape = I.arrayShape sv_t
            sv_w = arraySize 0 sv_t

        -- Generate an assertion and reshapes to ensure that sv and si' are the same
        -- size.
        cmp <-
          letSubExp "write_cmp" $
            I.BasicOp $
              I.CmpOp (I.CmpEq I.int64) si_w sv_w
        c <-
          assert
            "write_cert"
            cmp
            "length of index and value array does not match"
            loc
        certifying c $
          letExp (baseString sv ++ "_write_sv") $
            I.BasicOp $ I.Reshape (reshapeOuter [DimCoercion si_w] 1 sv_shape) sv

      indexType <- fmap rowType <$> mapM lookupType si'
      indexName <- mapM (\_ -> newVName "write_index") indexType
      valueNames <- replicateM (length sv_ts) $ newVName "write_value"

      sa_ts <- mapM lookupType sas
      let bodyTypes = concat (replicate (length sv_ts) indexType) ++ map (I.stripArray dim) sa_ts
          paramTypes = indexType <> map rowType sv_ts
          bodyNames = indexName <> valueNames
          bodyParams = zipWith I.Param bodyNames paramTypes

      -- This body is pretty boring right now, as every input is exactly the output.
      -- But it can get funky later on if fused with something else.
      body <- localScope (scopeOfLParams bodyParams) . buildBody_ $ do
        let outs = concat (replicate (length valueNames) indexName) ++ valueNames
        results <- forM outs $ \name ->
          letSubExp "write_res" $ I.BasicOp $ I.SubExp $ I.Var name
        ensureResultShape
          "scatter value has wrong size"
          loc
          bodyTypes
          results

      let lam =
            I.Lambda
              { I.lambdaParams = bodyParams,
                I.lambdaReturnType = bodyTypes,
                I.lambdaBody = body
              }
          sivs = si' <> svs'

      let sa_ws = map (Shape . take dim . arrayDims) sa_ts
      letTupExp' desc $ I.Op $ I.Scatter si_w lam sivs $ zip3 sa_ws (repeat 1) sas

funcall ::
  String ->
  QualName VName ->
  [SubExp] ->
  SrcLoc ->
  InternaliseM ([SubExp], [I.ExtType])
funcall desc (QualName _ fname) args loc = do
  (shapes, value_paramts, fun_params, rettype_fun) <-
    lookupFunction fname
  argts <- mapM subExpType args

  shapeargs <- argShapes shapes fun_params argts
  let diets =
        replicate (length shapeargs) I.ObservePrim
          ++ map I.diet value_paramts
  args' <-
    ensureArgShapes
      "function arguments of wrong shape"
      loc
      (map I.paramName fun_params)
      (map I.paramType fun_params)
      (shapeargs ++ args)
  argts' <- mapM subExpType args'
  case rettype_fun $ zip args' argts' of
    Nothing ->
      error $
        concat
          [ "Cannot apply ",
            pretty fname,
            " to ",
            show (length args'),
            " arguments\n ",
            pretty args',
            "\nof types\n ",
            pretty argts',
            "\nFunction has ",
            show (length fun_params),
            " parameters\n ",
            pretty fun_params
          ]
    Just ts -> do
      safety <- askSafety
      attrs <- asks envAttrs
      ses <-
        attributing attrs $
          letTupExp' desc $
            I.Apply (internaliseFunName fname) (zip args' diets) ts (safety, loc, mempty)
      return (ses, map I.fromDecl ts)

-- Bind existential names defined by an expression, based on the
-- concrete values that expression evaluated to.  This most
-- importantly should be done after function calls, but also
-- everything else that can produce existentials in the source
-- language.
bindExtSizes :: AppRes -> [SubExp] -> InternaliseM ()
bindExtSizes (AppRes ret retext) ses = do
  ts <- internaliseType $ E.toStruct ret
  ses_ts <- mapM subExpType ses

  let combine t1 t2 =
        mconcat $ zipWith combine' (arrayExtDims t1) (arrayDims t2)
      combine' (I.Free (I.Var v)) se
        | v `elem` retext = M.singleton v se
      combine' _ _ = mempty

  forM_ (M.toList $ mconcat $ zipWith combine ts ses_ts) $ \(v, se) ->
    letBindNames [v] $ BasicOp $ SubExp se

askSafety :: InternaliseM Safety
askSafety = do
  check <- asks envDoBoundsChecks
  return $ if check then I.Safe else I.Unsafe

-- Implement partitioning using maps, scans and writes.
partitionWithSOACS :: Int -> I.Lambda -> [I.VName] -> InternaliseM ([I.SubExp], [I.SubExp])
partitionWithSOACS k lam arrs = do
  arr_ts <- mapM lookupType arrs
  let w = arraysSize 0 arr_ts
  classes_and_increments <- letTupExp "increments" $ I.Op $ I.Screma w arrs (mapSOAC lam)
  (classes, increments) <- case classes_and_increments of
    classes : increments -> return (classes, take k increments)
    _ -> error "partitionWithSOACS"

  add_lam_x_params <-
    replicateM k $ I.Param <$> newVName "x" <*> pure (I.Prim int64)
  add_lam_y_params <-
    replicateM k $ I.Param <$> newVName "y" <*> pure (I.Prim int64)
  add_lam_body <- runBodyBinder $
    localScope (scopeOfLParams $ add_lam_x_params ++ add_lam_y_params) $
      fmap resultBody $
        forM (zip add_lam_x_params add_lam_y_params) $ \(x, y) ->
          letSubExp "z" $
            I.BasicOp $
              I.BinOp
                (I.Add Int64 I.OverflowUndef)
                (I.Var $ I.paramName x)
                (I.Var $ I.paramName y)
  let add_lam =
        I.Lambda
          { I.lambdaBody = add_lam_body,
            I.lambdaParams = add_lam_x_params ++ add_lam_y_params,
            I.lambdaReturnType = replicate k $ I.Prim int64
          }
      nes = replicate (length increments) $ intConst Int64 0

  scan <- I.scanSOAC [I.Scan add_lam nes]
  all_offsets <- letTupExp "offsets" $ I.Op $ I.Screma w increments scan

  -- We have the offsets for each of the partitions, but we also need
  -- the total sizes, which are the last elements in the offests.  We
  -- just have to be careful in case the array is empty.
  last_index <- letSubExp "last_index" $ I.BasicOp $ I.BinOp (I.Sub Int64 OverflowUndef) w $ constant (1 :: Int64)
  nonempty_body <- runBodyBinder $
    fmap resultBody $
      forM all_offsets $ \offset_array ->
        letSubExp "last_offset" $ I.BasicOp $ I.Index offset_array [I.DimFix last_index]
  let empty_body = resultBody $ replicate k $ constant (0 :: Int64)
  is_empty <- letSubExp "is_empty" $ I.BasicOp $ I.CmpOp (CmpEq int64) w $ constant (0 :: Int64)
  sizes <-
    letTupExp "partition_size" $
      I.If is_empty empty_body nonempty_body $
        ifCommon $ replicate k $ I.Prim int64

  -- The total size of all partitions must necessarily be equal to the
  -- size of the input array.

  -- Create scratch arrays for the result.
  blanks <- forM arr_ts $ \arr_t ->
    letExp "partition_dest" $
      I.BasicOp $ Scratch (I.elemType arr_t) (w : drop 1 (I.arrayDims arr_t))

  -- Now write into the result.
  write_lam <- do
    c_param <- I.Param <$> newVName "c" <*> pure (I.Prim int64)
    offset_params <- replicateM k $ I.Param <$> newVName "offset" <*> pure (I.Prim int64)
    value_params <- forM arr_ts $ \arr_t ->
      I.Param <$> newVName "v" <*> pure (I.rowType arr_t)
    (offset, offset_stms) <-
      collectStms $
        mkOffsetLambdaBody
          (map I.Var sizes)
          (I.Var $ I.paramName c_param)
          0
          offset_params
    return
      I.Lambda
        { I.lambdaParams = c_param : offset_params ++ value_params,
          I.lambdaReturnType =
            replicate (length arr_ts) (I.Prim int64)
              ++ map I.rowType arr_ts,
          I.lambdaBody =
            mkBody offset_stms $
              replicate (length arr_ts) offset
                ++ map (I.Var . I.paramName) value_params
        }
  results <-
    letTupExp "partition_res" $
      I.Op $
        I.Scatter
          w
          write_lam
          (classes : all_offsets ++ arrs)
          $ zip3 (repeat $ Shape [w]) (repeat 1) blanks
  sizes' <-
    letSubExp "partition_sizes" $
      I.BasicOp $
        I.ArrayLit (map I.Var sizes) $ I.Prim int64
  return (map I.Var results, [sizes'])
  where
    mkOffsetLambdaBody ::
      [SubExp] ->
      SubExp ->
      Int ->
      [I.LParam] ->
      InternaliseM SubExp
    mkOffsetLambdaBody _ _ _ [] =
      return $ constant (-1 :: Int64)
    mkOffsetLambdaBody sizes c i (p : ps) = do
      is_this_one <-
        letSubExp "is_this_one" $
          I.BasicOp $
            I.CmpOp (CmpEq int64) c $
              intConst Int64 $ toInteger i
      next_one <- mkOffsetLambdaBody sizes c (i + 1) ps
      this_one <-
        letSubExp "this_offset"
          =<< foldBinOp
            (Add Int64 OverflowUndef)
            (constant (-1 :: Int64))
            (I.Var (I.paramName p) : take i sizes)
      letSubExp "total_res" $
        I.If
          is_this_one
          (resultBody [this_one])
          (resultBody [next_one])
          $ ifCommon [I.Prim int64]

typeExpForError :: E.TypeExp VName -> InternaliseM [ErrorMsgPart SubExp]
typeExpForError (E.TEVar qn _) =
  return [ErrorString $ pretty qn]
typeExpForError (E.TEUnique te _) =
  ("*" :) <$> typeExpForError te
typeExpForError (E.TEArray te d _) = do
  d' <- dimExpForError d
  te' <- typeExpForError te
  return $ ["[", d', "]"] ++ te'
typeExpForError (E.TETuple tes _) = do
  tes' <- mapM typeExpForError tes
  return $ ["("] ++ intercalate [", "] tes' ++ [")"]
typeExpForError (E.TERecord fields _) = do
  fields' <- mapM onField fields
  return $ ["{"] ++ intercalate [", "] fields' ++ ["}"]
  where
    onField (k, te) =
      (ErrorString (pretty k ++ ": ") :) <$> typeExpForError te
typeExpForError (E.TEArrow _ t1 t2 _) = do
  t1' <- typeExpForError t1
  t2' <- typeExpForError t2
  return $ t1' ++ [" -> "] ++ t2'
typeExpForError (E.TEApply t arg _) = do
  t' <- typeExpForError t
  arg' <- case arg of
    TypeArgExpType argt -> typeExpForError argt
    TypeArgExpDim d _ -> pure <$> dimExpForError d
  return $ t' ++ [" "] ++ arg'
typeExpForError (E.TESum cs _) = do
  cs' <- mapM (onClause . snd) cs
  return $ intercalate [" | "] cs'
  where
    onClause c = do
      c' <- mapM typeExpForError c
      return $ intercalate [" "] c'

dimExpForError :: E.DimExp VName -> InternaliseM (ErrorMsgPart SubExp)
dimExpForError (DimExpNamed d _) = do
  substs <- lookupSubst $ E.qualLeaf d
  d' <- case substs of
    Just [v] -> return v
    _ -> return $ I.Var $ E.qualLeaf d
  return $ ErrorInt64 d'
dimExpForError (DimExpConst d _) =
  return $ ErrorString $ pretty d
dimExpForError DimExpAny = return ""

-- A smart constructor that compacts neighbouring literals for easier
-- reading in the IR.
errorMsg :: [ErrorMsgPart a] -> ErrorMsg a
errorMsg = ErrorMsg . compact
  where
    compact [] = []
    compact (ErrorString x : ErrorString y : parts) =
      compact (ErrorString (x ++ y) : parts)
    compact (x : y) = x : compact y
