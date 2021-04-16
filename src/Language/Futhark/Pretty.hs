{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Futhark prettyprinter.  This module defines 'Pretty' instances
-- for the AST defined in "Language.Futhark.Syntax".
module Language.Futhark.Pretty
  ( pretty,
    prettyTuple,
    leadingOperator,
    IsName (..),
    prettyName,
    Annot (..),
  )
where

import Codec.Binary.UTF8.String (decode)
import Control.Monad
import Data.Array
import Data.Functor
import Data.List (intersperse)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Monoid hiding (Sum)
import Data.Ord
import Data.Word
import Futhark.Util
import Futhark.Util.Pretty
import Language.Futhark.Prop
import Language.Futhark.Syntax
import Prelude

-- | A class for types that are variable names in the Futhark source
-- language.  This is used instead of a mere 'Pretty' instance because
-- in the compiler frontend we want to print VNames differently
-- depending on whether the FUTHARK_COMPILER_DEBUGGING environment
-- variable is set, yet in the backend we want to always print VNames
-- with the tag.  To avoid erroneously using the 'Pretty' instance for
-- VNames, we in fact only define it inside the modules for the core
-- language (as an orphan instance).
class IsName v where
  pprName :: v -> Doc

-- | Depending on the environment variable FUTHARK_COMPILER_DEBUGGING,
-- VNames are printed as either the name with an internal tag, or just
-- the base name.
instance IsName VName where
  pprName
    | isEnvVarAtLeast "FUTHARK_COMPILER_DEBUGGING" 1 =
      \(VName vn i) -> ppr vn <> text "_" <> text (show i)
    | otherwise = ppr . baseName

instance IsName Name where
  pprName = ppr

-- | Prettyprint a name to a string.
prettyName :: IsName v => v -> String
prettyName = prettyDoc 80 . pprName

-- | Class for type constructors that represent annotations.  Used in
-- the prettyprinter to either print the original AST, or the computed
-- decoration.
class Annot f where
  -- | Extract value, if any.
  unAnnot :: f a -> Maybe a

instance Annot NoInfo where
  unAnnot = const Nothing

instance Annot Info where
  unAnnot = Just . unInfo

pprAnnot :: (Annot f, Pretty a, Pretty b) => a -> f b -> Doc
pprAnnot a b = maybe (ppr a) ppr $ unAnnot b

instance Pretty Value where
  ppr (PrimValue bv) = ppr bv
  ppr (ArrayValue a t)
    | [] <- elems a = text "empty" <> parens (ppr t)
    | Array {} <- t = brackets $ commastack $ map ppr $ elems a
    | otherwise = brackets $ commasep $ map ppr $ elems a

instance Pretty PrimValue where
  ppr (UnsignedValue (Int8Value v)) =
    text (show (fromIntegral v :: Word8)) <> text "u8"
  ppr (UnsignedValue (Int16Value v)) =
    text (show (fromIntegral v :: Word16)) <> text "u16"
  ppr (UnsignedValue (Int32Value v)) =
    text (show (fromIntegral v :: Word32)) <> text "u32"
  ppr (UnsignedValue (Int64Value v)) =
    text (show (fromIntegral v :: Word64)) <> text "u64"
  ppr (SignedValue v) = ppr v
  ppr (BoolValue True) = text "true"
  ppr (BoolValue False) = text "false"
  ppr (FloatValue v) = ppr v

instance IsName vn => Pretty (DimDecl vn) where
  ppr (AnyDim Nothing) = mempty
  ppr (AnyDim (Just v)) = text "?" <> pprName v
  ppr (NamedDim v) = ppr v
  ppr (ConstDim n) = ppr n

instance IsName vn => Pretty (DimExp vn) where
  ppr DimExpAny = mempty
  ppr (DimExpNamed v _) = ppr v
  ppr (DimExpConst n _) = ppr n

instance IsName vn => Pretty (ShapeDecl (DimDecl vn)) where
  ppr (ShapeDecl ds) = mconcat (map (brackets . ppr) ds)

instance Pretty (ShapeDecl ()) where
  ppr (ShapeDecl ds) = mconcat $ replicate (length ds) $ text "[]"

instance Pretty (ShapeDecl Int64) where
  ppr (ShapeDecl ds) = mconcat (map (brackets . ppr) ds)

instance Pretty (ShapeDecl Bool) where
  ppr (ShapeDecl ds) = mconcat (map (brackets . ppr) ds)

instance Pretty (ShapeDecl dim) => Pretty (ScalarTypeBase dim as) where
  ppr = pprPrec 0
  pprPrec _ (Prim et) = ppr et
  pprPrec p (TypeVar _ u et targs) =
    parensIf (not (null targs) && p > 3) $
      ppr u <> ppr (qualNameFromTypeName et) <+> spread (map (pprPrec 3) targs)
  pprPrec _ (Record fs)
    | Just ts <- areTupleFields fs =
      oneLine (parens $ commasep $ map ppr ts)
        <|> parens (align $ mconcat $ punctuate (text "," <> line) $ map ppr ts)
    | otherwise =
      oneLine (braces $ commasep fs')
        <|> braces (align $ mconcat $ punctuate (text "," <> line) fs')
    where
      ppField (name, t) = text (nameToString name) <> colon <+> align (ppr t)
      fs' = map ppField $ M.toList fs
  pprPrec p (Arrow _ (Named v) t1 t2) =
    parensIf (p > 1) $
      parens (pprName v <> colon <+> align (ppr t1)) <+/> text "->" <+> pprPrec 1 t2
  pprPrec p (Arrow _ Unnamed t1 t2) =
    parensIf (p > 1) $ pprPrec 2 t1 <+/> text "->" <+> pprPrec 1 t2
  pprPrec p (Sum cs) =
    parensIf (p > 0) $
      oneLine (mconcat $ punctuate (text " | ") cs')
        <|> align (mconcat $ punctuate (text " |" <> line) cs')
    where
      ppConstr (name, fs) = sep $ (text "#" <> ppr name) : map (pprPrec 2) fs
      cs' = map ppConstr $ M.toList cs

instance Pretty (ShapeDecl dim) => Pretty (TypeBase dim as) where
  ppr = pprPrec 0
  pprPrec _ (Array _ u at shape) = ppr u <> ppr shape <> align (pprPrec 1 at)
  pprPrec p (Scalar t) = pprPrec p t

instance Pretty (ShapeDecl dim) => Pretty (TypeArg dim) where
  ppr = pprPrec 0
  pprPrec _ (TypeArgDim d _) = ppr $ ShapeDecl [d]
  pprPrec p (TypeArgType t _) = pprPrec p t

instance (Eq vn, IsName vn) => Pretty (TypeExp vn) where
  ppr (TEUnique t _) = text "*" <> ppr t
  ppr (TEArray at d _) = brackets (ppr d) <> ppr at
  ppr (TETuple ts _) = parens $ commasep $ map ppr ts
  ppr (TERecord fs _) = braces $ commasep $ map ppField fs
    where
      ppField (name, t) = text (nameToString name) <> colon <+> ppr t
  ppr (TEVar name _) = ppr name
  ppr (TEApply t arg _) = ppr t <+> ppr arg
  ppr (TEArrow (Just v) t1 t2 _) = parens v' <+> text "->" <+> ppr t2
    where
      v' = pprName v <> colon <+> ppr t1
  ppr (TEArrow Nothing t1 t2 _) = ppr t1 <+> text "->" <+> ppr t2
  ppr (TESum cs _) =
    align $ cat $ punctuate (text " |" <> softline) $ map ppConstr cs
    where
      ppConstr (name, fs) = text "#" <> ppr name <+> sep (map ppr fs)
  ppr (TEDim dims te _) =
    text "?" <> mconcat (map (brackets . pprName) dims) <> text "." <> ppr te

instance (Eq vn, IsName vn) => Pretty (TypeArgExp vn) where
  ppr (TypeArgExpDim d _) = brackets $ ppr d
  ppr (TypeArgExpType t) = ppr t

instance (Eq vn, IsName vn, Annot f) => Pretty (TypeDeclBase f vn) where
  ppr x = pprAnnot (declaredType x) (expandedType x)

instance IsName vn => Pretty (QualName vn) where
  ppr (QualName names name) =
    mconcat $ punctuate (text ".") $ map pprName names ++ [pprName name]

instance IsName vn => Pretty (IdentBase f vn) where
  ppr = pprName . identName

hasArrayLit :: ExpBase ty vn -> Bool
hasArrayLit ArrayLit {} = True
hasArrayLit (TupLit es2 _) = any hasArrayLit es2
hasArrayLit _ = False

instance (Eq vn, IsName vn, Annot f) => Pretty (DimIndexBase f vn) where
  ppr (DimFix e) = ppr e
  ppr (DimSlice i j (Just s)) =
    maybe mempty ppr i <> text ":"
      <> maybe mempty ppr j
      <> text ":"
      <> ppr s
  ppr (DimSlice i (Just j) s) =
    maybe mempty ppr i <> text ":"
      <> ppr j
      <> maybe mempty ((text ":" <>) . ppr) s
  ppr (DimSlice i Nothing Nothing) =
    maybe mempty ppr i <> text ":"

instance IsName vn => Pretty (SizeBinder vn) where
  ppr (SizeBinder v _) = brackets $ pprName v

letBody :: (Eq vn, IsName vn, Annot f) => ExpBase f vn -> Doc
letBody body@(AppExp LetPat {} _) = ppr body
letBody body@(AppExp LetFun {} _) = ppr body
letBody body = text "in" <+> align (ppr body)

instance (Eq vn, IsName vn, Annot f) => Pretty (AppExpBase f vn) where
  ppr = pprPrec (-1)
  pprPrec p (Coerce e t _) =
    parensIf (p /= -1) $ pprPrec 0 e <+> text ":>" <+> align (pprPrec 0 t)
  pprPrec p (BinOp (bop, _) _ (x, _) (y, _) _) = prettyBinOp p bop x y
  pprPrec _ (Match e cs _) = text "match" <+> ppr e </> (stack . map ppr) (NE.toList cs)
  pprPrec _ (DoLoop sizeparams pat initexp form loopbody _) =
    text "loop"
      <+> align
        ( spread (map (brackets . pprName) sizeparams)
            <+/> ppr pat <+> equals
            <+/> ppr initexp
            <+/> ppr form <+> text "do"
        )
      </> indent 2 (ppr loopbody)
  pprPrec _ (Index e idxs _) =
    pprPrec 9 e <> brackets (commasep (map ppr idxs))
  pprPrec p (LetPat sizes pat e body _) =
    parensIf (p /= -1) $
      align $
        text "let" <+> spread (map ppr sizes) <+> align (ppr pat)
          <+> ( if linebreak
                  then equals </> indent 2 (ppr e)
                  else equals <+> align (ppr e)
              )
          </> letBody body
    where
      linebreak = case e of
        AppExp {} -> True
        Attr {} -> True
        ArrayLit {} -> False
        _ -> hasArrayLit e
  pprPrec _ (LetFun fname (tparams, params, retdecl, rettype, e) body _) =
    text "let" <+> pprName fname <+> spread (map ppr tparams ++ map ppr params)
      <> retdecl' <+> equals
      </> indent 2 (ppr e)
      </> letBody body
    where
      retdecl' = case (ppr <$> unAnnot rettype) `mplus` (ppr <$> retdecl) of
        Just rettype' -> colon <+> align rettype'
        Nothing -> mempty
  pprPrec _ (LetWith dest src idxs ve body _)
    | dest == src =
      text "let" <+> ppr dest <> list (map ppr idxs)
        <+> equals
        <+> align (ppr ve)
        </> letBody body
    | otherwise =
      text "let" <+> ppr dest <+> equals <+> ppr src
        <+> text "with"
        <+> brackets (commasep (map ppr idxs))
        <+> text "="
        <+> align (ppr ve)
        </> letBody body
  pprPrec p (Range start maybe_step end _) =
    parensIf (p /= -1) $
      ppr start
        <> maybe mempty ((text ".." <>) . ppr) maybe_step
        <> case end of
          DownToExclusive end' -> text "..>" <> ppr end'
          ToInclusive end' -> text "..." <> ppr end'
          UpToExclusive end' -> text "..<" <> ppr end'
  pprPrec _ (If c t f _) =
    text "if" <+> ppr c
      </> text "then" <+> align (ppr t)
      </> text "else" <+> align (ppr f)
  pprPrec p (Apply f arg _ _) =
    parensIf (p >= 10) $ pprPrec 0 f <+/> pprPrec 10 arg

instance (Eq vn, IsName vn, Annot f) => Pretty (ExpBase f vn) where
  ppr = pprPrec (-1)
  pprPrec _ (Var name t _) = ppr name <> inst
    where
      inst = case unAnnot t of
        Just t'
          | isEnvVarAtLeast "FUTHARK_COMPILER_DEBUGGING" 2 ->
            text "@" <> parens (align $ ppr t')
        _ -> mempty
  pprPrec _ (Parens e _) = align $ parens $ ppr e
  pprPrec _ (QualParens (v, _) e _) = ppr v <> text "." <> align (parens $ ppr e)
  pprPrec p (Ascript e t _) =
    parensIf (p /= -1) $ pprPrec 0 e <+> text ":" <+> align (pprPrec 0 t)
  pprPrec _ (Literal v _) = ppr v
  pprPrec _ (IntLit v _ _) = ppr v
  pprPrec _ (FloatLit v _ _) = ppr v
  pprPrec _ (TupLit es _)
    | any hasArrayLit es = parens $ commastack $ map ppr es
    | otherwise = parens $ commasep $ map ppr es
  pprPrec _ (RecordLit fs _)
    | any fieldArray fs = braces $ commastack $ map ppr fs
    | otherwise = braces $ commasep $ map ppr fs
    where
      fieldArray (RecordFieldExplicit _ e _) = hasArrayLit e
      fieldArray RecordFieldImplicit {} = False
  pprPrec _ (ArrayLit es info _) =
    brackets (commasep $ map ppr es) <> info'
    where
      info' = case unAnnot info of
        Just t
          | isEnvVarAtLeast "FUTHARK_COMPILER_DEBUGGING" 2 ->
            text "@" <> parens (align $ ppr t)
        _ -> mempty
  pprPrec _ (StringLit s _) =
    text $ show $ decode s
  pprPrec _ (Project k e _ _) = ppr e <> text "." <> ppr k
  pprPrec _ (Negate e _) = text "-" <> ppr e
  pprPrec _ (Update src idxs ve _) =
    ppr src <+> text "with"
      <+> brackets (commasep (map ppr idxs))
      <+> text "="
      <+> align (ppr ve)
  pprPrec _ (RecordUpdate src fs ve _ _) =
    ppr src <+> text "with"
      <+> mconcat (intersperse (text ".") (map ppr fs))
      <+> text "="
      <+> align (ppr ve)
  pprPrec _ (Assert e1 e2 _ _) = text "assert" <+> pprPrec 10 e1 <+> pprPrec 10 e2
  pprPrec p (Lambda params body rettype _ _) =
    parensIf (p /= -1) $
      text "\\" <> spread (map ppr params) <> ppAscription rettype
        <+> text "->" </> indent 2 (ppr body)
  pprPrec _ (OpSection binop _ _) =
    parens $ ppr binop
  pprPrec _ (OpSectionLeft binop _ x _ _ _) =
    parens $ ppr x <+> ppBinOp binop
  pprPrec _ (OpSectionRight binop _ x _ _ _) =
    parens $ ppBinOp binop <+> ppr x
  pprPrec _ (ProjectSection fields _ _) =
    parens $ mconcat $ map p fields
    where
      p name = text "." <> ppr name
  pprPrec _ (IndexSection idxs _ _) =
    parens $ text "." <> brackets (commasep (map ppr idxs))
  pprPrec _ (Constr n cs _ _) = text "#" <> ppr n <+> sep (map ppr cs)
  pprPrec _ (Attr attr e _) =
    text "#[" <> ppr attr <> text "]" </> pprPrec (-1) e
  pprPrec i (AppExp e _) = pprPrec i e

instance Pretty AttrInfo where
  ppr (AttrAtom attr) = ppr attr
  ppr (AttrComp f attrs) = ppr f <> parens (commasep $ map ppr attrs)

instance (Eq vn, IsName vn, Annot f) => Pretty (FieldBase f vn) where
  ppr (RecordFieldExplicit name e _) = ppr name <> equals <> ppr e
  ppr (RecordFieldImplicit name _ _) = pprName name

instance (Eq vn, IsName vn, Annot f) => Pretty (CaseBase f vn) where
  ppr (CasePat p e _) = text "case" <+> ppr p <+> text "->" </> indent 2 (ppr e)

instance (Eq vn, IsName vn, Annot f) => Pretty (LoopFormBase f vn) where
  ppr (For i ubound) =
    text "for" <+> ppr i <+> text "<" <+> align (ppr ubound)
  ppr (ForIn x e) =
    text "for" <+> ppr x <+> text "in" <+> ppr e
  ppr (While cond) =
    text "while" <+> ppr cond

instance Pretty PatLit where
  ppr (PatLitInt x) = ppr x
  ppr (PatLitFloat f) = ppr f
  ppr (PatLitPrim v) = ppr v

instance (Eq vn, IsName vn, Annot f) => Pretty (PatternBase f vn) where
  ppr (PatternAscription p t _) = ppr p <> colon <+> align (ppr t)
  ppr (PatternParens p _) = parens $ ppr p
  ppr (Id v t _) = case unAnnot t of
    Just t' -> parens $ pprName v <> colon <+> align (ppr t')
    Nothing -> pprName v
  ppr (TuplePattern pats _) = parens $ commasep $ map ppr pats
  ppr (RecordPattern fs _) = braces $ commasep $ map ppField fs
    where
      ppField (name, t) = text (nameToString name) <> equals <> ppr t
  ppr (Wildcard t _) = case unAnnot t of
    Just t' -> parens $ text "_" <> colon <+> ppr t'
    Nothing -> text "_"
  ppr (PatternLit e _ _) = ppr e
  ppr (PatternConstr n _ ps _) = text "#" <> ppr n <+> sep (map ppr ps)

ppAscription :: Pretty t => Maybe t -> Doc
ppAscription Nothing = mempty
ppAscription (Just t) = colon <> align (ppr t)

instance (Eq vn, IsName vn, Annot f) => Pretty (ProgBase f vn) where
  ppr = stack . punctuate line . map ppr . progDecs

instance (Eq vn, IsName vn, Annot f) => Pretty (DecBase f vn) where
  ppr (ValDec dec) = ppr dec
  ppr (TypeDec dec) = ppr dec
  ppr (SigDec sig) = ppr sig
  ppr (ModDec sd) = ppr sd
  ppr (OpenDec x _) = text "open" <+> ppr x
  ppr (LocalDec dec _) = text "local" <+> ppr dec
  ppr (ImportDec x _ _) = text "import" <+> ppr x

instance (Eq vn, IsName vn, Annot f) => Pretty (ModExpBase f vn) where
  ppr (ModVar v _) = ppr v
  ppr (ModParens e _) = parens $ ppr e
  ppr (ModImport v _ _) = text "import" <+> ppr (show v)
  ppr (ModDecs ds _) = nestedBlock "{" "}" (stack $ punctuate line $ map ppr ds)
  ppr (ModApply f a _ _ _) = parens $ ppr f <+> parens (ppr a)
  ppr (ModAscript me se _ _) = ppr me <> colon <+> ppr se
  ppr (ModLambda param maybe_sig body _) =
    text "\\" <> ppr param <> maybe_sig'
      <+> text "->" </> indent 2 (ppr body)
    where
      maybe_sig' = case maybe_sig of
        Nothing -> mempty
        Just (sig, _) -> colon <+> ppr sig

instance Pretty Liftedness where
  ppr Unlifted = text ""
  ppr SizeLifted = text "~"
  ppr Lifted = text "^"

instance (Eq vn, IsName vn, Annot f) => Pretty (TypeBindBase f vn) where
  ppr (TypeBind name l params usertype _ _) =
    text "type" <> ppr l <+> pprName name
      <+> spread (map ppr params)
      <+> equals
      <+> ppr usertype

instance (Eq vn, IsName vn) => Pretty (TypeParamBase vn) where
  ppr (TypeParamDim name _) = brackets $ pprName name
  ppr (TypeParamType l name _) = text "'" <> ppr l <> pprName name

instance (Eq vn, IsName vn, Annot f) => Pretty (ValBindBase f vn) where
  ppr (ValBind entry name retdecl rettype tparams args body _ attrs _) =
    mconcat (map ((<> line) . ppr) attrs)
      <> text fun
      <+> pprName name
      <+> align (sep (map ppr tparams ++ map ppr args))
      <> retdecl'
      <> text " ="
      </> indent 2 (ppr body)
    where
      fun
        | isJust entry = "entry"
        | otherwise = "let"
      retdecl' = case (ppr . fst <$> unAnnot rettype) `mplus` (ppr <$> retdecl) of
        Just rettype' -> colon <+> align rettype'
        Nothing -> mempty

instance (Eq vn, IsName vn, Annot f) => Pretty (SpecBase f vn) where
  ppr (TypeAbbrSpec tpsig) = ppr tpsig
  ppr (TypeSpec l name ps _ _) =
    text "type" <> ppr l <+> pprName name <+> spread (map ppr ps)
  ppr (ValSpec name tparams vtype _ _) =
    text "val" <+> pprName name <+> spread (map ppr tparams) <> colon <+> ppr vtype
  ppr (ModSpec name sig _ _) =
    text "module" <+> pprName name <> colon <+> ppr sig
  ppr (IncludeSpec e _) =
    text "include" <+> ppr e

instance (Eq vn, IsName vn, Annot f) => Pretty (SigExpBase f vn) where
  ppr (SigVar v _ _) = ppr v
  ppr (SigParens e _) = parens $ ppr e
  ppr (SigSpecs ss _) = nestedBlock "{" "}" (stack $ punctuate line $ map ppr ss)
  ppr (SigWith s (TypeRef v ps td _) _) =
    ppr s <+> text "with" <+> ppr v <+> spread (map ppr ps) <> text " =" <+> ppr td
  ppr (SigArrow (Just v) e1 e2 _) =
    parens (pprName v <> colon <+> ppr e1) <+> text "->" <+> ppr e2
  ppr (SigArrow Nothing e1 e2 _) =
    ppr e1 <+> text "->" <+> ppr e2

instance (Eq vn, IsName vn, Annot f) => Pretty (SigBindBase f vn) where
  ppr (SigBind name e _ _) =
    text "module type" <+> pprName name <+> equals <+> ppr e

instance (Eq vn, IsName vn, Annot f) => Pretty (ModParamBase f vn) where
  ppr (ModParam pname psig _ _) =
    parens (pprName pname <> colon <+> ppr psig)

instance (Eq vn, IsName vn, Annot f) => Pretty (ModBindBase f vn) where
  ppr (ModBind name ps sig e _ _) =
    text "module" <+> pprName name <+> spread (map ppr ps) <+> sig' <> text " =" <+> ppr e
    where
      sig' = case sig of
        Nothing -> mempty
        Just (s, _) -> colon <+> ppr s <> text " "

ppBinOp :: IsName v => QualName v -> Doc
ppBinOp bop =
  case leading of
    Backtick -> text "`" <> ppr bop <> text "`"
    _ -> ppr bop
  where
    leading =
      leadingOperator $ nameFromString $ pretty $ pprName $ qualLeaf bop

prettyBinOp ::
  (Eq vn, IsName vn, Annot f) =>
  Int ->
  QualName vn ->
  ExpBase f vn ->
  ExpBase f vn ->
  Doc
prettyBinOp p bop x y =
  parensIf (p > symPrecedence) $
    pprPrec symPrecedence x
      <+/> bop'
      <+> pprPrec symRPrecedence y
  where
    bop' = case leading of
      Backtick -> text "`" <> ppr bop <> text "`"
      _ -> ppr bop
    leading = leadingOperator $ nameFromString $ pretty $ pprName $ qualLeaf bop
    symPrecedence = precedence leading
    symRPrecedence = rprecedence leading
    precedence PipeRight = -1
    precedence PipeLeft = -1
    precedence LogAnd = 0
    precedence LogOr = 0
    precedence Band = 1
    precedence Bor = 1
    precedence Xor = 1
    precedence Equal = 2
    precedence NotEqual = 2
    precedence Less = 2
    precedence Leq = 2
    precedence Greater = 2
    precedence Geq = 2
    precedence ShiftL = 3
    precedence ShiftR = 3
    precedence Plus = 4
    precedence Minus = 4
    precedence Times = 5
    precedence Divide = 5
    precedence Mod = 5
    precedence Quot = 5
    precedence Rem = 5
    precedence Pow = 6
    precedence Backtick = 9
    rprecedence Minus = 10
    rprecedence Divide = 10
    rprecedence op = precedence op
