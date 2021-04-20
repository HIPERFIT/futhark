{-# LANGUAGE FlexibleContexts #-}

-- | Facilities for answering queries about a program, such as "what
-- appears at this source location", or "where is this name bound".
-- The intent is that this is used as a building block for IDE-like
-- functionality.
module Language.Futhark.Query
  ( BoundTo (..),
    boundLoc,
    AtPos (..),
    atPos,
    Pos (..),
  )
where

import Control.Monad
import Control.Monad.State
import Data.List (find)
import qualified Data.Map as M
import Futhark.Util.Loc (Loc (..), Pos (..))
import Language.Futhark
import Language.Futhark.Semantic
import Language.Futhark.Traversals
import qualified System.FilePath.Posix as Posix

-- | What a name is bound to.
data BoundTo
  = BoundTerm StructType Loc
  | BoundModule Loc
  | BoundModuleType Loc
  | BoundType Loc
  deriving (Eq, Show)

data Def = DefBound BoundTo | DefIndirect VName
  deriving (Eq, Show)

type Defs = M.Map VName Def

-- | Where was a bound variable actually bound?  That is, what is the
-- location of its definition?
boundLoc :: BoundTo -> Loc
boundLoc (BoundTerm _ loc) = loc
boundLoc (BoundModule loc) = loc
boundLoc (BoundModuleType loc) = loc
boundLoc (BoundType loc) = loc

sizeDefs :: SizeBinder VName -> Defs
sizeDefs (SizeBinder v loc) =
  M.singleton v $ DefBound $ BoundTerm (Scalar (Prim (Signed Int64))) (locOf loc)

patternDefs :: Pattern -> Defs
patternDefs (Id vn (Info t) loc) =
  M.singleton vn $ DefBound $ BoundTerm (toStruct t) (locOf loc)
patternDefs (TuplePattern pats _) =
  mconcat $ map patternDefs pats
patternDefs (RecordPattern fields _) =
  mconcat $ map (patternDefs . snd) fields
patternDefs (PatternParens pat _) =
  patternDefs pat
patternDefs Wildcard {} = mempty
patternDefs PatternLit {} = mempty
patternDefs (PatternAscription pat _ _) =
  patternDefs pat
patternDefs (PatternConstr _ _ pats _) =
  mconcat $ map patternDefs pats

typeParamDefs :: TypeParamBase VName -> Defs
typeParamDefs (TypeParamDim vn loc) =
  M.singleton vn $ DefBound $ BoundTerm (Scalar $ Prim $ Signed Int32) (locOf loc)
typeParamDefs (TypeParamType _ vn loc) =
  M.singleton vn $ DefBound $ BoundType $ locOf loc

expDefs :: Exp -> Defs
expDefs e =
  execState (astMap mapper e) extra
  where
    mapper =
      identityMapper {mapOnExp = onExp}
    onExp e' = do
      modify (<> expDefs e')
      return e'

    identDefs (Ident v (Info vt) vloc) =
      M.singleton v $ DefBound $ BoundTerm (toStruct vt) $ locOf vloc

    extra =
      case e of
        AppExp (LetPat sizes pat _ _ _) _ ->
          foldMap sizeDefs sizes <> patternDefs pat
        Lambda params _ _ _ _ ->
          mconcat (map patternDefs params)
        AppExp (LetFun name (tparams, params, _, Info ret, _) _ loc) _ ->
          let name_t = foldFunType (map patternStructType params) ret
           in M.singleton name (DefBound $ BoundTerm name_t (locOf loc))
                <> mconcat (map typeParamDefs tparams)
                <> mconcat (map patternDefs params)
        AppExp (LetWith v _ _ _ _ _) _ ->
          identDefs v
        AppExp (DoLoop _ merge _ form _ _) _ ->
          patternDefs merge
            <> case form of
              For i _ -> identDefs i
              ForIn pat _ -> patternDefs pat
              While {} -> mempty
        _ ->
          mempty

valBindDefs :: ValBind -> Defs
valBindDefs vbind =
  M.insert (valBindName vbind) (DefBound $ BoundTerm vbind_t (locOf vbind)) $
    mconcat (map typeParamDefs (valBindTypeParams vbind))
      <> mconcat (map patternDefs (valBindParams vbind))
      <> expDefs (valBindBody vbind)
  where
    vbind_t =
      foldFunType (map patternStructType (valBindParams vbind)) $
        fst $ unInfo $ valBindRetType vbind

typeBindDefs :: TypeBind -> Defs
typeBindDefs tbind =
  M.singleton (typeAlias tbind) $ DefBound $ BoundType $ locOf tbind

modParamDefs :: ModParam -> Defs
modParamDefs (ModParam p se _ loc) =
  M.singleton p (DefBound $ BoundModule $ locOf loc)
    <> sigExpDefs se

modExpDefs :: ModExp -> Defs
modExpDefs ModVar {} =
  mempty
modExpDefs (ModParens me _) =
  modExpDefs me
modExpDefs ModImport {} =
  mempty
modExpDefs (ModDecs decs _) =
  mconcat $ map decDefs decs
modExpDefs (ModApply e1 e2 _ (Info substs) _) =
  modExpDefs e1 <> modExpDefs e2 <> M.map DefIndirect substs
modExpDefs (ModAscript e _ (Info substs) _) =
  modExpDefs e <> M.map DefIndirect substs
modExpDefs (ModLambda p _ e _) =
  modParamDefs p <> modExpDefs e

modBindDefs :: ModBind -> Defs
modBindDefs mbind =
  M.singleton (modName mbind) (DefBound $ BoundModule $ locOf mbind)
    <> mconcat (map modParamDefs (modParams mbind))
    <> modExpDefs (modExp mbind)
    <> case modSignature mbind of
      Nothing -> mempty
      Just (_, Info substs) ->
        M.map DefIndirect substs

specDefs :: Spec -> Defs
specDefs spec =
  case spec of
    ValSpec v tparams tdecl _ loc ->
      let vdef = DefBound $ BoundTerm (unInfo $ expandedType tdecl) (locOf loc)
       in M.insert v vdef $ mconcat (map typeParamDefs tparams)
    TypeAbbrSpec tbind -> typeBindDefs tbind
    TypeSpec _ v _ _ loc ->
      M.singleton v $ DefBound $ BoundType $ locOf loc
    ModSpec v se _ loc ->
      M.singleton v (DefBound $ BoundModuleType $ locOf loc)
        <> sigExpDefs se
    IncludeSpec se _ -> sigExpDefs se

sigExpDefs :: SigExp -> Defs
sigExpDefs se =
  case se of
    SigVar _ (Info substs) _ -> M.map DefIndirect substs
    SigParens e _ -> sigExpDefs e
    SigSpecs specs _ -> mconcat $ map specDefs specs
    SigWith e _ _ -> sigExpDefs e
    SigArrow _ e1 e2 _ -> sigExpDefs e1 <> sigExpDefs e2

sigBindDefs :: SigBind -> Defs
sigBindDefs sbind =
  M.singleton (sigName sbind) (DefBound $ BoundModuleType $ locOf sbind)
    <> sigExpDefs (sigExp sbind)

decDefs :: Dec -> Defs
decDefs (ValDec vbind) = valBindDefs vbind
decDefs (TypeDec vbind) = typeBindDefs vbind
decDefs (ModDec mbind) = modBindDefs mbind
decDefs (SigDec mbind) = sigBindDefs mbind
decDefs (OpenDec me _) = modExpDefs me
decDefs (LocalDec dec _) = decDefs dec
decDefs ImportDec {} = mempty

-- | All bindings of everything in the program.
progDefs :: Prog -> Defs
progDefs = mconcat . map decDefs . progDecs

allBindings :: Imports -> M.Map VName BoundTo
allBindings imports = M.mapMaybe forward defs
  where
    defs = mconcat $ map (progDefs . fileProg . snd) imports
    forward (DefBound x) = Just x
    forward (DefIndirect v) = forward =<< M.lookup v defs

data RawAtPos = RawAtName (QualName VName) Loc

contains :: Located a => a -> Pos -> Bool
contains a pos =
  case locOf a of
    Loc start end -> pos >= start && pos <= end
    NoLoc -> False

atPosInTypeExp :: TypeExp VName -> Pos -> Maybe RawAtPos
atPosInTypeExp te pos =
  case te of
    TEVar qn loc -> do
      guard $ loc `contains` pos
      Just $ RawAtName qn $ locOf loc
    TETuple es _ ->
      msum $ map (`atPosInTypeExp` pos) es
    TERecord fields _ ->
      msum $ map ((`atPosInTypeExp` pos) . snd) fields
    TEArray te' dim _ ->
      atPosInTypeExp te' pos `mplus` inDim dim
    TEUnique te' _ ->
      atPosInTypeExp te' pos
    TEApply e1 arg _ ->
      atPosInTypeExp e1 pos `mplus` inArg arg
    TEArrow _ e1 e2 _ ->
      atPosInTypeExp e1 pos `mplus` atPosInTypeExp e2 pos
    TESum cs _ ->
      msum $ map (`atPosInTypeExp` pos) $ concatMap snd cs
    TEDim _ t _ ->
      atPosInTypeExp t pos
  where
    inArg (TypeArgExpDim dim _) = inDim dim
    inArg (TypeArgExpType e2) = atPosInTypeExp e2 pos
    inDim (DimExpNamed qn loc) = do
      guard $ loc `contains` pos
      Just $ RawAtName qn $ locOf loc
    inDim _ = Nothing

atPosInPattern :: Pattern -> Pos -> Maybe RawAtPos
atPosInPattern (Id vn _ loc) pos = do
  guard $ loc `contains` pos
  Just $ RawAtName (qualName vn) $ locOf loc
atPosInPattern (TuplePattern pats _) pos =
  msum $ map (`atPosInPattern` pos) pats
atPosInPattern (RecordPattern fields _) pos =
  msum $ map ((`atPosInPattern` pos) . snd) fields
atPosInPattern (PatternParens pat _) pos =
  atPosInPattern pat pos
atPosInPattern (PatternAscription pat tdecl _) pos =
  atPosInPattern pat pos `mplus` atPosInTypeExp (declaredType tdecl) pos
atPosInPattern (PatternConstr _ _ pats _) pos =
  msum $ map (`atPosInPattern` pos) pats
atPosInPattern PatternLit {} _ = Nothing
atPosInPattern Wildcard {} _ = Nothing

atPosInExp :: Exp -> Pos -> Maybe RawAtPos
atPosInExp (Var qn _ loc) pos = do
  guard $ loc `contains` pos
  Just $ RawAtName qn $ locOf loc
atPosInExp (QualParens (qn, loc) _ _) pos
  | loc `contains` pos = Just $ RawAtName qn $ locOf loc
-- All the value cases are TODO - we need another RawAtPos constructor.
atPosInExp Literal {} _ = Nothing
atPosInExp IntLit {} _ = Nothing
atPosInExp FloatLit {} _ = Nothing
atPosInExp (AppExp (LetPat _ pat _ _ _) _) pos
  | pat `contains` pos = atPosInPattern pat pos
atPosInExp (AppExp (LetWith a b _ _ _ _) _) pos
  | a `contains` pos = Just $ RawAtName (qualName $ identName a) (locOf a)
  | b `contains` pos = Just $ RawAtName (qualName $ identName b) (locOf b)
atPosInExp (AppExp (DoLoop _ merge _ _ _ _) _) pos
  | merge `contains` pos = atPosInPattern merge pos
atPosInExp (Ascript _ tdecl _) pos
  | tdecl `contains` pos = atPosInTypeExp (declaredType tdecl) pos
atPosInExp (AppExp (Coerce _ tdecl _) _) pos
  | tdecl `contains` pos = atPosInTypeExp (declaredType tdecl) pos
atPosInExp e pos = do
  guard $ e `contains` pos
  -- Use the Either monad for short-circuiting for efficiency reasons.
  -- The first hit is going to be the only one.
  case astMap mapper e of
    Left atpos -> Just atpos
    Right _ -> Nothing
  where
    mapper =
      identityMapper {mapOnExp = onExp}
    onExp e' =
      case atPosInExp e' pos of
        Just atpos -> Left atpos
        Nothing -> Right e'

atPosInModExp :: ModExp -> Pos -> Maybe RawAtPos
atPosInModExp (ModVar qn loc) pos = do
  guard $ loc `contains` pos
  Just $ RawAtName qn $ locOf loc
atPosInModExp (ModParens me _) pos =
  atPosInModExp me pos
atPosInModExp ModImport {} _ =
  Nothing
atPosInModExp (ModDecs decs _) pos =
  msum $ map (`atPosInDec` pos) decs
atPosInModExp (ModApply e1 e2 _ _ _) pos =
  atPosInModExp e1 pos `mplus` atPosInModExp e2 pos
atPosInModExp (ModAscript e _ _ _) pos =
  atPosInModExp e pos
atPosInModExp (ModLambda _ _ e _) pos =
  atPosInModExp e pos

atPosInSpec :: Spec -> Pos -> Maybe RawAtPos
atPosInSpec spec pos =
  case spec of
    ValSpec _ _ tdecl _ _ -> atPosInTypeExp (declaredType tdecl) pos
    TypeAbbrSpec tbind -> atPosInTypeBind tbind pos
    TypeSpec {} -> Nothing
    ModSpec _ se _ _ -> atPosInSigExp se pos
    IncludeSpec se _ -> atPosInSigExp se pos

atPosInSigExp :: SigExp -> Pos -> Maybe RawAtPos
atPosInSigExp se pos =
  case se of
    SigVar qn _ loc -> do
      guard $ loc `contains` pos
      Just $ RawAtName qn $ locOf loc
    SigParens e _ -> atPosInSigExp e pos
    SigSpecs specs _ -> msum $ map (`atPosInSpec` pos) specs
    SigWith e _ _ -> atPosInSigExp e pos
    SigArrow _ e1 e2 _ -> atPosInSigExp e1 pos `mplus` atPosInSigExp e2 pos

atPosInValBind :: ValBind -> Pos -> Maybe RawAtPos
atPosInValBind vbind pos =
  msum (map (`atPosInPattern` pos) (valBindParams vbind))
    `mplus` atPosInExp (valBindBody vbind) pos
    `mplus` join (atPosInTypeExp <$> valBindRetDecl vbind <*> pure pos)

atPosInTypeBind :: TypeBind -> Pos -> Maybe RawAtPos
atPosInTypeBind = atPosInTypeExp . typeExp

atPosInModBind :: ModBind -> Pos -> Maybe RawAtPos
atPosInModBind (ModBind _ params sig e _ _) pos =
  msum (map inParam params)
    `mplus` atPosInModExp e pos
    `mplus` case sig of
      Nothing -> Nothing
      Just (se, _) -> atPosInSigExp se pos
  where
    inParam (ModParam _ se _ _) = atPosInSigExp se pos

atPosInSigBind :: SigBind -> Pos -> Maybe RawAtPos
atPosInSigBind = atPosInSigExp . sigExp

atPosInDec :: Dec -> Pos -> Maybe RawAtPos
atPosInDec dec pos = do
  guard $ dec `contains` pos
  case dec of
    ValDec vbind -> atPosInValBind vbind pos
    TypeDec tbind -> atPosInTypeBind tbind pos
    ModDec mbind -> atPosInModBind mbind pos
    SigDec sbind -> atPosInSigBind sbind pos
    OpenDec e _ -> atPosInModExp e pos
    LocalDec dec' _ -> atPosInDec dec' pos
    ImportDec {} -> Nothing

atPosInProg :: Prog -> Pos -> Maybe RawAtPos
atPosInProg prog pos =
  msum $ map (`atPosInDec` pos) (progDecs prog)

containingModule :: Imports -> Pos -> Maybe FileModule
containingModule imports (Pos file _ _ _) =
  snd <$> find ((== file') . fst) imports
  where
    file' =
      includeToString $
        mkInitialImport $
          fst $ Posix.splitExtension file

-- | Information about what is at the given source location.
data AtPos = AtName (QualName VName) (Maybe BoundTo) Loc
  deriving (Eq, Show)

-- | Information about what's at the given source position.  Returns
-- 'Nothing' if there is nothing there, including if the source
-- position is invalid.
atPos :: Imports -> Pos -> Maybe AtPos
atPos imports pos = do
  prog <- fileProg <$> containingModule imports pos
  RawAtName qn loc <- atPosInProg prog pos
  Just $ AtName qn (qualLeaf qn `M.lookup` allBindings imports) loc
