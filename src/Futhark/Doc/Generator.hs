{-# LANGUAGE OverloadedStrings #-}

-- | The core logic of @futhark doc@.
module Futhark.Doc.Generator (renderFiles) where

import qualified CMarkGFM as GFM
import Control.Arrow ((***))
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer hiding (Sum)
import Data.Char (isAlpha, isSpace, toUpper)
import Data.List (find, groupBy, inits, intersperse, isPrefixOf, partition, sort, sortOn, tails)
import qualified Data.Map as M
import Data.Maybe
import Data.Ord
import qualified Data.Set as S
import Data.String (fromString)
import qualified Data.Text as T
import Data.Version
import Futhark.Util.Pretty (Doc, ppr)
import Futhark.Version
import Language.Futhark
import Language.Futhark.Semantic
import Language.Futhark.TypeChecker.Monad hiding (warn)
import System.FilePath (makeRelative, splitPath, (-<.>), (<.>), (</>))
import Text.Blaze.Html5 (AttributeValue, Html, toHtml, (!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import Prelude hiding (abs)

docToHtml :: Doc -> Html
docToHtml = toHtml . pretty

primTypeHtml :: PrimType -> Html
primTypeHtml = docToHtml . ppr

prettyU :: Uniqueness -> Html
prettyU = docToHtml . ppr

renderName :: Name -> Html
renderName name = docToHtml (ppr name)

joinBy :: Html -> [Html] -> Html
joinBy _ [] = mempty
joinBy _ [x] = x
joinBy sep (x : xs) = x <> foldMap (sep <>) xs

commas :: [Html] -> Html
commas = joinBy ", "

parens :: Html -> Html
parens x = "(" <> x <> ")"

braces :: Html -> Html
braces x = "{" <> x <> "}"

brackets :: Html -> Html
brackets x = "[" <> x <> "]"

pipes :: [Html] -> Html
pipes = joinBy " | "

-- | A set of names that we should not generate links to, because they
-- are uninteresting.  These are for example type parameters.
type NoLink = S.Set VName

data Context = Context
  { ctxCurrent :: String,
    ctxFileMod :: FileModule,
    ctxImports :: Imports,
    ctxNoLink :: NoLink,
    ctxFileMap :: FileMap,
    -- | Local module types that show up in the
    -- interface.  These should be documented,
    -- but clearly marked local.
    ctxVisibleMTys :: S.Set VName
  }

type FileMap = M.Map VName (String, Namespace)

type DocM = ReaderT Context (WriterT Documented (Writer Warnings))

data IndexWhat = IndexValue | IxFun | IndexModule | IndexModuleType | IndexType

-- | We keep a mapping of the names we have actually documented, so we
-- can generate an index.
type Documented = M.Map VName IndexWhat

warn :: SrcLoc -> Doc -> DocM ()
warn loc s = lift $ lift $ tell $ singleWarning loc s

document :: VName -> IndexWhat -> DocM ()
document v what = tell $ M.singleton v what

noLink :: [VName] -> DocM a -> DocM a
noLink names = local $ \ctx ->
  ctx {ctxNoLink = S.fromList names <> ctxNoLink ctx}

selfLink :: AttributeValue -> Html -> Html
selfLink s = H.a ! A.id s ! A.href ("#" <> s) ! A.class_ "self_link"

fullRow :: Html -> Html
fullRow = H.tr . (H.td ! A.colspan "3")

emptyRow :: Html
emptyRow = H.tr $ H.td mempty <> H.td mempty <> H.td mempty

specRow :: Html -> Html -> Html -> Html
specRow a b c =
  H.tr $
    (H.td ! A.class_ "spec_lhs") a
      <> (H.td ! A.class_ "spec_eql") b
      <> (H.td ! A.class_ "spec_rhs") c

vnameToFileMap :: Imports -> FileMap
vnameToFileMap = mconcat . map forFile
  where
    forFile (file, FileModule abs file_env _prog) =
      mconcat (map (vname Type) (M.keys abs))
        <> forEnv file_env
      where
        vname ns v = M.singleton (qualLeaf v) (file, ns)
        vname' ((ns, _), v) = vname ns v

        forEnv env =
          mconcat (map vname' $ M.toList $ envNameMap env)
            <> mconcat (map forMty $ M.elems $ envSigTable env)
        forMod (ModEnv env) = forEnv env
        forMod ModFun {} = mempty
        forMty = forMod . mtyMod

-- | @renderFiles important_imports imports@ produces HTML files
-- documenting the type-checked program @imports@, with the files in
-- @important_imports@ considered most important.  The HTML files must
-- be written to the specific locations indicated in the return value,
-- or the relative links will be wrong.
renderFiles :: [FilePath] -> Imports -> ([(FilePath, Html)], Warnings)
renderFiles important_imports imports = runWriter $ do
  (import_pages, documented) <- runWriterT $
    forM imports $ \(current, fm) ->
      let ctx =
            Context
              current
              fm
              imports
              mempty
              file_map
              (progModuleTypes $ fileProg fm)
       in flip runReaderT ctx $ do
            (first_paragraph, maybe_abstract, maybe_sections) <- headerDoc $ fileProg fm

            synopsis <- (H.div ! A.id "module") <$> synopsisDecs (progDecs $ fileProg fm)

            description <- describeDecs $ progDecs $ fileProg fm

            return
              ( current,
                ( H.docTypeHtml ! A.lang "en" $
                    addBoilerplateWithNav important_imports imports ("doc" </> current) current $
                      H.main $
                        maybe_abstract
                          <> selfLink "synopsis" (H.h2 "Synopsis")
                          <> (H.div ! A.id "overview") synopsis
                          <> selfLink "description" (H.h2 "Description")
                          <> description
                          <> maybe_sections,
                  first_paragraph
                )
              )

  return $
    [ ("index.html", contentsPage important_imports $ map (fmap snd) import_pages),
      ("doc-index.html", indexPage important_imports imports documented file_map)
    ]
      ++ map (importHtml *** fst) import_pages
  where
    file_map = vnameToFileMap imports
    importHtml import_name = "doc" </> import_name <.> "html"

-- | The header documentation (which need not be present) can contain
-- an abstract and further sections.
headerDoc :: Prog -> DocM (Html, Html, Html)
headerDoc prog =
  case progDoc prog of
    Just (DocComment doc loc) -> do
      let (abstract, more_sections) = splitHeaderDoc doc
      first_paragraph <- docHtml $ Just $ DocComment (firstParagraph abstract) loc
      abstract' <- docHtml $ Just $ DocComment abstract loc
      more_sections' <- docHtml $ Just $ DocComment more_sections loc
      return
        ( first_paragraph,
          selfLink "abstract" (H.h2 "Abstract") <> abstract',
          more_sections'
        )
    _ -> return mempty
  where
    splitHeaderDoc s =
      fromMaybe (s, mempty) $
        find (("\n##" `isPrefixOf`) . snd) $
          zip (inits s) (tails s)
    firstParagraph = unlines . takeWhile (not . paragraphSeparator) . lines
    paragraphSeparator = all isSpace

contentsPage :: [FilePath] -> [(String, Html)] -> Html
contentsPage important_imports pages =
  H.docTypeHtml $
    addBoilerplate "index.html" "Futhark Library Documentation" $
      H.main $
        H.h2 "Main libraries"
          <> fileList important_pages
          <> if null unimportant_pages
            then mempty
            else
              H.h2 "Supporting libraries"
                <> fileList unimportant_pages
  where
    (important_pages, unimportant_pages) =
      partition ((`elem` important_imports) . fst) pages

    fileList pages' =
      H.dl ! A.class_ "file_list" $
        mconcat $ map linkTo $ sortOn fst pages'

    linkTo (name, maybe_abstract) =
      H.div ! A.class_ "file_desc" $
        (H.dt ! A.class_ "desc_header") (importLink "index.html" name)
          <> (H.dd ! A.class_ "desc_doc") maybe_abstract

importLink :: FilePath -> String -> Html
importLink current name =
  let file = relativise (makeRelative "/" $ "doc" </> name -<.> "html") current
   in (H.a ! A.href (fromString file) $ fromString name)

indexPage :: [FilePath] -> Imports -> Documented -> FileMap -> Html
indexPage important_imports imports documented fm =
  H.docTypeHtml $
    addBoilerplateWithNav important_imports imports "doc-index.html" "Index" $
      H.main $
        ( H.ul ! A.id "doc_index_list" $
            mconcat $
              map initialListEntry $
                letter_group_links ++ [symbol_group_link]
        )
          <> ( H.table ! A.id "doc_index" $
                 H.thead (H.tr $ H.td "Who" <> H.td "What" <> H.td "Where")
                   <> mconcat (letter_groups ++ [symbol_group])
             )
  where
    (letter_names, sym_names) =
      partition (isLetterName . baseString . fst) $
        sortOn (map toUpper . baseString . fst) $
          mapMaybe isDocumented $ M.toList fm

    isDocumented (k, (file, _)) = do
      what <- M.lookup k documented
      Just (k, (file, what))

    (letter_groups, letter_group_links) =
      unzip $ map tbodyForNames $ groupBy sameInitial letter_names
    (symbol_group, symbol_group_link) =
      tbodyForInitial "Symbols" sym_names

    isLetterName [] = False
    isLetterName (c : _) = isAlpha c

    sameInitial (x, _) (y, _) =
      case (baseString x, baseString y) of
        (x' : _, y' : _) -> toUpper x' == toUpper y'
        _ -> False

    tbodyForNames names@((s, _) : _) =
      tbodyForInitial (map toUpper $ take 1 $ baseString s) names
    tbodyForNames _ = mempty

    tbodyForInitial initial names =
      ( H.tbody $ mconcat $ initial' : map linkTo names,
        initial
      )
      where
        initial' =
          H.tr $
            H.td ! A.colspan "2" ! A.class_ "doc_index_initial" $
              H.a ! A.id (fromString initial)
                ! A.href (fromString $ '#' : initial)
                $ fromString initial

    initialListEntry initial =
      H.li $ H.a ! A.href (fromString $ '#' : initial) $ fromString initial

    linkTo (name, (file, what)) =
      let link =
            (H.a ! A.href (fromString (makeRelative "/" $ "doc" </> vnameLink' name "" file))) $
              fromString $ baseString name
          what' = case what of
            IndexValue -> "value"
            IxFun -> "function"
            IndexType -> "type"
            IndexModuleType -> "module type"
            IndexModule -> "module"
          html_file = makeRelative "/" $ "doc" </> file -<.> "html"
       in H.tr $
            (H.td ! A.class_ "doc_index_name" $ link)
              <> (H.td ! A.class_ "doc_index_namespace" $ what')
              <> ( H.td ! A.class_ "doc_index_file" $
                     (H.a ! A.href (fromString html_file) $ fromString file)
                 )

addBoilerplate :: String -> String -> Html -> Html
addBoilerplate current titleText content =
  let headHtml =
        H.head $
          H.meta
            ! A.charset "utf-8"
              <> H.title (fromString titleText)
              <> H.link
            ! A.href (fromString $ relativise "style.css" current)
            ! A.rel "stylesheet"
            ! A.type_ "text/css"

      navigation =
        H.ul ! A.id "navigation" $
          H.li (H.a ! A.href (fromString $ relativise "index.html" current) $ "Contents")
            <> H.li (H.a ! A.href (fromString $ relativise "doc-index.html" current) $ "Index")

      madeByHtml =
        "Generated by " <> (H.a ! A.href futhark_doc_url) "futhark-doc"
          <> " "
          <> fromString (showVersion version)
   in headHtml
        <> H.body
          ( (H.div ! A.id "header") (H.h1 (toHtml titleText) <> navigation)
              <> (H.div ! A.id "content") content
              <> (H.div ! A.id "footer") madeByHtml
          )
  where
    futhark_doc_url =
      "https://futhark.readthedocs.io/en/latest/man/futhark-doc.html"

addBoilerplateWithNav :: [FilePath] -> Imports -> String -> String -> Html -> Html
addBoilerplateWithNav important_imports imports current titleText content =
  addBoilerplate current titleText $
    (H.nav ! A.id "filenav" $ files) <> content
  where
    files = H.ul $ mconcat $ map pp $ sort $ filter visible important_imports
    pp name = H.li $ importLink current name
    visible = (`elem` map fst imports)

synopsisDecs :: [Dec] -> DocM Html
synopsisDecs decs = do
  visible <- asks ctxVisibleMTys
  fm <- asks ctxFileMod
  -- We add an empty row to avoid generating invalid HTML in cases
  -- where all rows are otherwise colspan=2.
  (H.table ! A.class_ "specs") . (emptyRow <>) . mconcat
    <$> sequence (mapMaybe (synopsisDec visible fm) decs)

synopsisDec :: S.Set VName -> FileModule -> Dec -> Maybe (DocM Html)
synopsisDec visible fm dec = case dec of
  SigDec s -> synopsisModType mempty s
  ModDec m -> synopsisMod fm m
  ValDec v -> synopsisValBind v
  TypeDec t -> synopsisType t
  OpenDec x _
    | Just opened <- synopsisOpened x -> Just $ do
      opened' <- opened
      return $ fullRow $ keyword "open " <> opened'
    | otherwise ->
      Just $
        return $
          fullRow $
            keyword "open" <> fromString (" <" <> pretty x <> ">")
  LocalDec (SigDec s) _
    | sigName s `S.member` visible ->
      synopsisModType (keyword "local" <> " ") s
  LocalDec {} -> Nothing
  ImportDec {} -> Nothing

synopsisOpened :: ModExp -> Maybe (DocM Html)
synopsisOpened (ModVar qn _) = Just $ qualNameHtml qn
synopsisOpened (ModParens me _) = do
  me' <- synopsisOpened me
  Just $ parens <$> me'
synopsisOpened (ModImport _ (Info file) _) = Just $ do
  current <- asks ctxCurrent
  let dest = fromString $ relativise file current <> ".html"
  return $ keyword "import " <> (H.a ! A.href dest) (fromString $ show file)
synopsisOpened (ModAscript _ se _ _) = Just $ do
  se' <- synopsisSigExp se
  return $ "... : " <> se'
synopsisOpened _ = Nothing

synopsisValBind :: ValBind -> Maybe (DocM Html)
synopsisValBind vb = Just $ do
  let name' = vnameSynopsisDef $ valBindName vb
  (lhs, mhs, rhs) <- valBindHtml name' vb
  return $ specRow lhs (mhs <> " : ") rhs

valBindHtml :: Html -> ValBind -> DocM (Html, Html, Html)
valBindHtml name (ValBind _ _ retdecl (Info (rettype, _)) tparams params _ _ _ _) = do
  let tparams' = mconcat $ map ((" " <>) . typeParamHtml) tparams
      noLink' =
        noLink $
          map typeParamName tparams
            ++ map identName (S.toList $ mconcat $ map patternIdents params)
  rettype' <- noLink' $ maybe (typeHtml rettype) typeExpHtml retdecl
  params' <- noLink' $ mapM patternHtml params
  return
    ( keyword "val " <> (H.span ! A.class_ "decl_name") name,
      tparams',
      mconcat (intersperse " -> " $ params' ++ [rettype'])
    )

synopsisModType :: Html -> SigBind -> Maybe (DocM Html)
synopsisModType prefix sb = Just $ do
  let name' = vnameSynopsisDef $ sigName sb
  fullRow <$> do
    se' <- synopsisSigExp $ sigExp sb
    return $ prefix <> keyword "module type " <> name' <> " = " <> se'

synopsisMod :: FileModule -> ModBind -> Maybe (DocM Html)
synopsisMod fm (ModBind name ps sig _ _ _) =
  case sig of
    Nothing -> (proceed <=< envSig) <$> M.lookup name modtable
    Just (s, _) -> Just $ proceed =<< synopsisSigExp s
  where
    proceed sig' = do
      let name' = vnameSynopsisDef name
      ps' <- modParamHtml ps
      return $ specRow (keyword "module " <> name') ": " (ps' <> sig')

    FileModule _abs Env {envModTable = modtable} _ = fm
    envSig (ModEnv e) = renderEnv e
    envSig (ModFun (FunSig _ _ (MTy _ m))) = envSig m

synopsisType :: TypeBind -> Maybe (DocM Html)
synopsisType tb = Just $ do
  let name' = vnameSynopsisDef $ typeAlias tb
  fullRow <$> typeBindHtml name' tb

typeBindHtml :: Html -> TypeBind -> DocM Html
typeBindHtml name' (TypeBind _ l tparams t _ _) = do
  t' <- noLink (map typeParamName tparams) $ typeDeclHtml t
  return $ typeAbbrevHtml l name' tparams <> " = " <> t'

renderEnv :: Env -> DocM Html
renderEnv (Env vtable ttable sigtable modtable _) = do
  typeBinds <- mapM renderTypeBind (M.toList ttable)
  valBinds <- mapM renderValBind (M.toList vtable)
  sigBinds <- mapM renderModType (M.toList sigtable)
  modBinds <- mapM renderMod (M.toList modtable)
  return $ braces $ mconcat $ typeBinds ++ valBinds ++ sigBinds ++ modBinds

renderModType :: (VName, MTy) -> DocM Html
renderModType (name, _sig) =
  (keyword "module type " <>) <$> qualNameHtml (qualName name)

renderMod :: (VName, Mod) -> DocM Html
renderMod (name, _mod) =
  (keyword "module " <>) <$> qualNameHtml (qualName name)

renderValBind :: (VName, BoundV) -> DocM Html
renderValBind = fmap H.div . synopsisValBindBind

renderTypeBind :: (VName, TypeBinding) -> DocM Html
renderTypeBind (name, TypeAbbr l tps tp) = do
  tp' <- typeHtml tp
  return $ H.div $ typeAbbrevHtml l (vnameHtml name) tps <> " = " <> tp'

synopsisValBindBind :: (VName, BoundV) -> DocM Html
synopsisValBindBind (name, BoundV tps t) = do
  let tps' = map typeParamHtml tps
  t' <- typeHtml t
  return $
    keyword "val " <> vnameHtml name
      <> mconcat (map (" " <>) tps')
      <> ": "
      <> t'

typeHtml :: StructType -> DocM Html
typeHtml t = case t of
  Array _ u et shape -> do
    shape' <- prettyShapeDecl shape
    et' <- typeHtml $ Scalar et
    return $ prettyU u <> shape' <> et'
  Scalar (Prim et) -> return $ primTypeHtml et
  Scalar (Record fs)
    | Just ts <- areTupleFields fs ->
      parens . commas <$> mapM typeHtml ts
    | otherwise ->
      braces . commas <$> mapM ppField (M.toList fs)
    where
      ppField (name, tp) = do
        tp' <- typeHtml tp
        return $ toHtml (nameToString name) <> ": " <> tp'
  Scalar (TypeVar _ u et targs) -> do
    targs' <- mapM typeArgHtml targs
    et' <- typeNameHtml et
    return $ prettyU u <> et' <> mconcat (map (" " <>) targs')
  Scalar (Arrow _ pname t1 t2) -> do
    t1' <- typeHtml t1
    t2' <- typeHtml t2
    return $ case pname of
      Named v ->
        parens (vnameHtml v <> ": " <> t1') <> " -> " <> t2'
      Unnamed ->
        t1' <> " -> " <> t2'
  Scalar (Sum cs) -> pipes <$> mapM ppClause (sortConstrs cs)
    where
      ppClause (n, ts) = joinBy " " . (ppConstr n :) <$> mapM typeHtml ts
      ppConstr name = "#" <> toHtml (nameToString name)

prettyShapeDecl :: ShapeDecl (DimDecl VName) -> DocM Html
prettyShapeDecl (ShapeDecl ds) =
  mconcat <$> mapM (fmap brackets . dimDeclHtml) ds

typeArgHtml :: TypeArg (DimDecl VName) -> DocM Html
typeArgHtml (TypeArgDim d _) = brackets <$> dimDeclHtml d
typeArgHtml (TypeArgType t _) = typeHtml t

modParamHtml :: [ModParamBase Info VName] -> DocM Html
modParamHtml [] = return mempty
modParamHtml (ModParam pname psig _ _ : mps) =
  liftM2 f (synopsisSigExp psig) (modParamHtml mps)
  where
    f se params =
      "(" <> vnameHtml pname
        <> ": "
        <> se
        <> ") -> "
        <> params

synopsisSigExp :: SigExpBase Info VName -> DocM Html
synopsisSigExp e = case e of
  SigVar v _ _ -> qualNameHtml v
  SigParens e' _ -> parens <$> synopsisSigExp e'
  SigSpecs ss _ -> braces . (H.table ! A.class_ "specs") . mconcat <$> mapM synopsisSpec ss
  SigWith s (TypeRef v ps t _) _ -> do
    s' <- synopsisSigExp s
    t' <- typeDeclHtml t
    v' <- qualNameHtml v
    let ps' = mconcat $ map ((" " <>) . typeParamHtml) ps
    return $ s' <> keyword " with " <> v' <> ps' <> " = " <> t'
  SigArrow Nothing e1 e2 _ ->
    liftM2 f (synopsisSigExp e1) (synopsisSigExp e2)
    where
      f e1' e2' = e1' <> " -> " <> e2'
  SigArrow (Just v) e1 e2 _ ->
    do
      let name = vnameHtml v
      e1' <- synopsisSigExp e1
      e2' <- noLink [v] $ synopsisSigExp e2
      return $ "(" <> name <> ": " <> e1' <> ") -> " <> e2'

keyword :: String -> Html
keyword = (H.span ! A.class_ "keyword") . fromString

vnameHtml :: VName -> Html
vnameHtml (VName name tag) =
  H.span ! A.id (fromString (show tag)) $ renderName name

vnameDescDef :: VName -> IndexWhat -> DocM Html
vnameDescDef v what = do
  document v what
  return $ H.a ! A.id (fromString (show (baseTag v))) $ renderName (baseName v)

vnameSynopsisDef :: VName -> Html
vnameSynopsisDef (VName name tag) =
  H.span ! A.id (fromString (show tag ++ "s")) $
    H.a ! A.href (fromString ("#" ++ show tag)) $ renderName name

vnameSynopsisRef :: VName -> Html
vnameSynopsisRef v =
  H.a ! A.class_ "synopsis_link"
    ! A.href (fromString ("#" ++ show (baseTag v) ++ "s"))
    $ "↑"

synopsisSpec :: SpecBase Info VName -> DocM Html
synopsisSpec spec = case spec of
  TypeAbbrSpec tpsig ->
    fullRow <$> typeBindHtml (vnameSynopsisDef $ typeAlias tpsig) tpsig
  TypeSpec l name ps _ _ ->
    return $ fullRow $ keyword l' <> vnameSynopsisDef name <> mconcat (map ((" " <>) . typeParamHtml) ps)
    where
      l' = case l of
        Unlifted -> "type "
        SizeLifted -> "type~ "
        Lifted -> "type^ "
  ValSpec name tparams rettype _ _ -> do
    let tparams' = map typeParamHtml tparams
    rettype' <-
      noLink (map typeParamName tparams) $
        typeDeclHtml rettype
    return $
      specRow
        (keyword "val " <> vnameSynopsisDef name)
        (mconcat (map (" " <>) tparams') <> ": ")
        rettype'
  ModSpec name sig _ _ ->
    specRow (keyword "module " <> vnameSynopsisDef name) ": " <$> synopsisSigExp sig
  IncludeSpec e _ -> fullRow . (keyword "include " <>) <$> synopsisSigExp e

typeDeclHtml :: TypeDeclBase f VName -> DocM Html
typeDeclHtml = typeExpHtml . declaredType

typeExpHtml :: TypeExp VName -> DocM Html
typeExpHtml e = case e of
  TEUnique t _ -> ("*" <>) <$> typeExpHtml t
  TEArray at d _ -> do
    at' <- typeExpHtml at
    d' <- dimExpHtml d
    return $ brackets d' <> at'
  TETuple ts _ -> parens . commas <$> mapM typeExpHtml ts
  TERecord fs _ -> braces . commas <$> mapM ppField fs
    where
      ppField (name, t) = do
        t' <- typeExpHtml t
        return $ toHtml (nameToString name) <> ": " <> t'
  TEVar name _ -> qualNameHtml name
  TEApply t arg _ -> do
    t' <- typeExpHtml t
    arg' <- typeArgExpHtml arg
    return $ t' <> " " <> arg'
  TEArrow pname t1 t2 _ -> do
    t1' <- case t1 of
      TEArrow {} -> parens <$> typeExpHtml t1
      _ -> typeExpHtml t1
    t2' <- typeExpHtml t2
    return $ case pname of
      Just v ->
        parens (vnameHtml v <> ": " <> t1') <> " -> " <> t2'
      Nothing ->
        t1' <> " -> " <> t2'
  TESum cs _ -> pipes <$> mapM ppClause cs
    where
      ppClause (n, ts) = joinBy " " . (ppConstr n :) <$> mapM typeExpHtml ts
      ppConstr name = "#" <> toHtml (nameToString name)
  TEDim dims t _ -> do
    t' <- typeExpHtml t
    pure $ "?" <> mconcat (map (brackets . renderName . baseName) dims) <> "." <> t'

qualNameHtml :: QualName VName -> DocM Html
qualNameHtml (QualName names vname@(VName name tag)) =
  if tag <= maxIntrinsicTag
    then return $ renderName name
    else f <$> ref
  where
    prefix :: Html
    prefix = mapM_ ((<> ".") . renderName . baseName) names
    f (Just s) = H.a ! A.href (fromString s) $ prefix <> renderName name
    f Nothing = prefix <> renderName name

    ref = do
      boring <- asks $ S.member vname . ctxNoLink
      if boring
        then return Nothing
        else Just <$> vnameLink vname

vnameLink' :: VName -> String -> String -> String
vnameLink :: VName -> DocM String
vnameLink vname = do
  current <- asks ctxCurrent
  file <- asks $ maybe current fst . M.lookup vname . ctxFileMap
  return $ vnameLink' vname current file
vnameLink' (VName _ tag) current file =
  if file == current
    then "#" ++ show tag
    else relativise file current ++ ".html#" ++ show tag

typeNameHtml :: TypeName -> DocM Html
typeNameHtml = qualNameHtml . qualNameFromTypeName

patternHtml :: Pattern -> DocM Html
patternHtml pat = do
  let (pat_param, t) = patternParam pat
  t' <- typeHtml t
  return $ case pat_param of
    Named v -> parens (vnameHtml v <> ": " <> t')
    Unnamed -> t'

relativise :: FilePath -> FilePath -> FilePath
relativise dest src =
  concat (replicate (length (splitPath src) - 1) "../") ++ dest

dimDeclHtml :: DimDecl VName -> DocM Html
dimDeclHtml (AnyDim _) = return mempty
dimDeclHtml (NamedDim v) = qualNameHtml v
dimDeclHtml (ConstDim n) = return $ toHtml (show n)

dimExpHtml :: DimExp VName -> DocM Html
dimExpHtml DimExpAny = return mempty
dimExpHtml (DimExpNamed v _) = qualNameHtml v
dimExpHtml (DimExpConst n _) = return $ toHtml (show n)

typeArgExpHtml :: TypeArgExp VName -> DocM Html
typeArgExpHtml (TypeArgExpDim d _) = dimExpHtml d
typeArgExpHtml (TypeArgExpType d) = typeExpHtml d

typeParamHtml :: TypeParam -> Html
typeParamHtml (TypeParamDim name _) =
  brackets $ vnameHtml name
typeParamHtml (TypeParamType l name _) =
  "'" <> fromString (pretty l) <> vnameHtml name

typeAbbrevHtml :: Liftedness -> Html -> [TypeParam] -> Html
typeAbbrevHtml l name params =
  what <> name <> mconcat (map ((" " <>) . typeParamHtml) params)
  where
    what = keyword $ "type" ++ pretty l ++ " "

docHtml :: Maybe DocComment -> DocM Html
docHtml (Just (DocComment doc loc)) =
  H.preEscapedText
    . GFM.commonmarkToHtml [] [GFM.extAutolink]
    . T.pack
    <$> identifierLinks loc doc
docHtml Nothing = return mempty

identifierLinks :: SrcLoc -> String -> DocM String
identifierLinks _ [] = return []
identifierLinks loc s
  | Just ((name, namespace, file), s') <- identifierReference s = do
    let proceed x = (x <>) <$> identifierLinks loc s'
        unknown = proceed $ "`" <> name <> "`"
    case knownNamespace namespace of
      Just namespace' -> do
        maybe_v <- lookupName (namespace', name, file)
        case maybe_v of
          Nothing -> do
            warn loc $
              "Identifier '" <> fromString name <> "' not found in namespace '"
                <> fromString namespace
                <> "'"
                <> fromString (maybe "" (" in file " <>) file)
                <> "."
            unknown
          Just v' -> do
            link <- vnameLink v'
            proceed $ "[`" <> name <> "`](" <> link <> ")"
      _ -> do
        warn loc $ "Unknown namespace '" <> fromString namespace <> "'."
        unknown
  where
    knownNamespace "term" = Just Term
    knownNamespace "mtype" = Just Signature
    knownNamespace "type" = Just Type
    knownNamespace _ = Nothing
identifierLinks loc (c : s') = (c :) <$> identifierLinks loc s'

lookupName :: (Namespace, String, Maybe FilePath) -> DocM (Maybe VName)
lookupName (namespace, name, file) = do
  current <- asks ctxCurrent
  let file' = includeToString . flip (mkImportFrom (mkInitialImport current)) mempty <$> file
  env <- lookupEnvForFile file'
  case M.lookup (namespace, nameFromString name) . envNameMap =<< env of
    Nothing -> return Nothing
    Just qn -> return $ Just $ qualLeaf qn

lookupEnvForFile :: Maybe FilePath -> DocM (Maybe Env)
lookupEnvForFile Nothing = asks $ Just . fileEnv . ctxFileMod
lookupEnvForFile (Just file) = asks $ fmap fileEnv . lookup file . ctxImports

describeGeneric ::
  VName ->
  IndexWhat ->
  Maybe DocComment ->
  (Html -> DocM Html) ->
  DocM Html
describeGeneric name what doc f = do
  name' <- H.span ! A.class_ "decl_name" <$> vnameDescDef name what
  decl_type <- f name'
  doc' <- docHtml doc
  let decl_doc = H.dd ! A.class_ "desc_doc" $ doc'
      decl_header =
        (H.dt ! A.class_ "desc_header") $
          vnameSynopsisRef name <> decl_type
  return $ decl_header <> decl_doc

describeGenericMod ::
  VName ->
  IndexWhat ->
  SigExp ->
  Maybe DocComment ->
  (Html -> DocM Html) ->
  DocM Html
describeGenericMod name what se doc f = do
  name' <- H.span ! A.class_ "decl_name" <$> vnameDescDef name what

  decl_type <- f name'

  doc' <- case se of
    SigSpecs specs _ -> (<>) <$> docHtml doc <*> describeSpecs specs
    _ -> docHtml doc

  let decl_doc = H.dd ! A.class_ "desc_doc" $ doc'
      decl_header =
        (H.dt ! A.class_ "desc_header") $
          vnameSynopsisRef name <> decl_type
  return $ decl_header <> decl_doc

describeDecs :: [Dec] -> DocM Html
describeDecs decs = do
  visible <- asks ctxVisibleMTys
  H.dl . mconcat
    <$> mapM
      (fmap $ H.div ! A.class_ "decl_description")
      (mapMaybe (describeDec visible) decs)

describeDec :: S.Set VName -> Dec -> Maybe (DocM Html)
describeDec _ (ValDec vb) = Just $
  describeGeneric (valBindName vb) (valBindWhat vb) (valBindDoc vb) $ \name -> do
    (lhs, mhs, rhs) <- valBindHtml name vb
    return $ lhs <> mhs <> ": " <> rhs
describeDec _ (TypeDec vb) =
  Just $
    describeGeneric (typeAlias vb) IndexType (typeDoc vb) (`typeBindHtml` vb)
describeDec _ (SigDec (SigBind name se doc _)) = Just $
  describeGenericMod name IndexModuleType se doc $ \name' ->
    return $ keyword "module type " <> name'
describeDec _ (ModDec mb) = Just $
  describeGeneric (modName mb) IndexModule (modDoc mb) $ \name' ->
    return $ keyword "module " <> name'
describeDec _ OpenDec {} = Nothing
describeDec visible (LocalDec (SigDec (SigBind name se doc _)) _)
  | name `S.member` visible = Just $
    describeGenericMod name IndexModuleType se doc $ \name' ->
      return $ keyword "local module type " <> name'
describeDec _ LocalDec {} = Nothing
describeDec _ ImportDec {} = Nothing

valBindWhat :: ValBind -> IndexWhat
valBindWhat vb
  | null (valBindParams vb),
    orderZero (fst $ unInfo $ valBindRetType vb) =
    IndexValue
  | otherwise =
    IxFun

describeSpecs :: [Spec] -> DocM Html
describeSpecs specs =
  H.dl . mconcat <$> mapM describeSpec specs

describeSpec :: Spec -> DocM Html
describeSpec (ValSpec name tparams t doc _) =
  describeGeneric name what doc $ \name' -> do
    let tparams' = mconcat $ map ((" " <>) . typeParamHtml) tparams
    t' <-
      noLink (map typeParamName tparams) $
        typeExpHtml $ declaredType t
    return $ keyword "val " <> name' <> tparams' <> ": " <> t'
  where
    what =
      if orderZero (unInfo $ expandedType t)
        then IndexValue
        else IxFun
describeSpec (TypeAbbrSpec vb) =
  describeGeneric (typeAlias vb) IndexType (typeDoc vb) (`typeBindHtml` vb)
describeSpec (TypeSpec l name tparams doc _) =
  describeGeneric name IndexType doc $
    return . (\name' -> typeAbbrevHtml l name' tparams)
describeSpec (ModSpec name se doc _) =
  describeGenericMod name IndexModule se doc $ \name' ->
    case se of
      SigSpecs {} -> return $ keyword "module " <> name'
      _ -> do
        se' <- synopsisSigExp se
        return $ keyword "module " <> name' <> ": " <> se'
describeSpec (IncludeSpec sig _) = do
  sig' <- synopsisSigExp sig
  doc' <- docHtml Nothing
  let decl_header =
        (H.dt ! A.class_ "desc_header") $
          (H.span ! A.class_ "synopsis_link") mempty
            <> keyword "include "
            <> sig'
      decl_doc = H.dd ! A.class_ "desc_doc" $ doc'
  return $ decl_header <> decl_doc
