{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | L0 prettyprinter.  This module defines 'Pretty' instances for the
-- AST defined in "Language.L0.Syntax", but also a number of
-- convenience functions if you don't want to use the interface from
-- 'Pretty'.
module Language.L0.Pretty
  ( ppType
  , ppValue
  , ppExp
  , ppLambda
  , ppTupleLambda
  , ppTupId
  , prettyPrint
  )
  where

import Data.Array
import qualified Data.Set as S

import Text.PrettyPrint.Mainland

import Language.L0.Syntax
import Language.L0.Attributes

tildes :: String -> String
tildes = map tilde
  where tilde '-' = '~'
        tilde c   = c

-- | The document @'apply' ds@ separates @ds@ with commas and encloses them with
-- parentheses.
apply :: [Doc] -> Doc
apply = encloseSep lparen rparen comma . map align

commastack :: [Doc] -> Doc
commastack = align . stack . punctuate comma

aliasComment :: (Ord vn, Pretty vn, TypeBox ty) => TupIdentBase ty vn -> Doc -> Doc
aliasComment pat d = case aliasComment' pat of
                       []   -> d
                       l:ls -> foldl (</>) l ls </> d
  where aliasComment' (Wildcard {}) = []
        aliasComment' (TupId pats _) = concatMap aliasComment' pats
        aliasComment' (Id ident) =
          case maybe [] (clean . S.toList . aliases)
                 $ unboxType $ identType ident of
            [] -> []
            als -> [oneline $
                    text "// " <> ppr ident <> text " aliases " <>
                    commasep (map ppr als)]
          where clean = filter (/= identName ident)
                oneline s = text $ displayS (renderCompact s) ""

instance Pretty Name where
  ppr (Name t) = fromText t

instance Pretty Value where
  ppr (IntVal x) = text $ tildes $ show x
  ppr (CharVal c) = text $ show c
  ppr (LogVal b) = text $ show b
  ppr (RealVal x) = text $ tildes $ show x
  ppr Checked = text "Checked"
  ppr (TupVal vs)
    | any (not . basicType . valueType) vs =
      braces $ commastack $ map ppr vs
    | otherwise =
      braces $ commasep $ map ppr vs
  ppr v@(ArrayVal a t)
    | Just s <- arrayString v = text $ show s
    | [] <- elems a = text "empty" <> parens (ppr t)
    | Array {} <- t = brackets $ commastack $ map ppr $ elems a
    | otherwise     = brackets $ commasep $ map ppr $ elems a

instance (Ord vn, Pretty vn) => Pretty (ElemTypeBase as vn) where
  ppr Int = text "int"
  ppr Char = text "char"
  ppr Bool = text "bool"
  ppr Real = text "real"
  ppr Cert = text "cert"
  ppr (Tuple ets) = braces $ commasep $ map ppr ets

instance (Ord vn, Pretty vn) => Pretty (TypeBase as vn) where
  ppr (Elem et) = ppr et
  ppr (Array et ds u _) = u' <> foldl f (ppr et) ds
    where f s Nothing = brackets s
          f s (Just e) = brackets $ s <> comma <> ppr e
          u' | Unique <- u = star
             | otherwise = empty

instance (Ord vn, Pretty vn) => Pretty (IdentBase ty vn) where
  ppr = ppr . identName

instance (Ord vn, Pretty vn, TypeBox ty) => Pretty (ExpBase ty vn) where
  ppr = pprPrec 0
  pprPrec _ (Var v) = ppr v
  pprPrec _ (Literal v _) = ppr v
  pprPrec _ (TupLit es _)
    | any hasArrayLit es = braces $ commastack $ map ppr es
    | otherwise          = braces $ commasep $ map ppr es
    where hasArrayLit (ArrayLit {}) = True
          hasArrayLit (TupLit es2 _) = any hasArrayLit es2
          hasArrayLit (Literal val _) = hasArrayVal val
          hasArrayLit _ = False
          hasArrayVal (ArrayVal {}) = True
          hasArrayVal (TupVal vs) = any hasArrayVal vs
          hasArrayVal _ = False
  pprPrec _ (ArrayLit es rt _) =
    case unboxType rt of
      Just (Array {}) -> brackets $ commastack $ map ppr es
      _               -> brackets $ commasep $ map ppr es
  pprPrec p (BinOp bop x y _ _) = ppBinOp p bop x y
  pprPrec p (And x y _) = ppBinOp p LogAnd x y
  pprPrec p (Or x y _) = ppBinOp p LogOr x y
  pprPrec _ (Not e _) = text "not" <+> pprPrec 9 e
  pprPrec _ (Negate e _ _) = text "~" <> pprPrec 9 e
  pprPrec _ (If c t f _ _) = text "if" <+> ppr c </>
                             text "then" <+> align (ppr t) </>
                             text "else" <+> align (ppr f)
  pprPrec _ (Apply fname args _ _) = text (nameToString fname) <>
                                     apply (map (align . ppr . fst) args)
  pprPrec _ (LetPat pat e body _) =
    aliasComment pat $
    text "let" <+> align (ppr pat) <+>
    (if linebreak
     then equals </> indent 2 (ppr e)
     else equals <+> align (ppr e)) <+> text "in" </>
    ppr body
    where linebreak = case e of
                        Map {} -> True
                        Reduce {} -> True
                        Filter {} -> True
                        Redomap {} -> True
                        Scan {} -> True
                        Map2 {} -> True
                        Reduce2 {} -> True
                        Filter2 {} -> True
                        Redomap2 {} -> True
                        Scan2 {} -> True
                        DoLoop {} -> True
                        LetPat {} -> True
                        LetWith {} -> True
                        _ -> False
  pprPrec _ (LetWith cs dest src idxs ve body _)
    | dest == src =
      text "let" <+> ppCertificates cs <> ppr dest <+> list (map ppr idxs) <+>
      equals <+> align (ppr ve) <+>
      text "in" </> ppr body
    | otherwise =
      text "let" <+> ppCertificates cs <> ppr dest <+> equals <+> ppr src <+>
      text "with" <+> list (map ppr idxs) <+> text "<-" <+> align (ppr ve) <+>
      text "in" </> ppr body
  pprPrec _ (Index cs v idxs _ _) =
    ppCertificates cs <> ppr v <> list (map ppr idxs)
  pprPrec _ (Iota e _) = text "iota" <> parens (ppr e)
  pprPrec _ (Size cs i e _) =
    ppCertificates cs <> text "size" <> apply [text $ tildes $ show i, ppr e]
  pprPrec _ (Replicate ne ve _) =
    text "replicate" <> apply [ppr ne, align (ppr ve)]
  pprPrec _ (Reshape cs shape e _) =
    ppCertificates cs <> text "reshape" <> apply [apply (map ppr shape), ppr e]
  pprPrec _ (Transpose cs 0 1 e _) =
    ppCertificates cs <> text "transpose" <> apply [ppr e]
  pprPrec _ (Transpose cs k n e _) =
        ppCertificates cs <>
        text "transpose" <> apply [text $ tildes $ show k,
                                   text $ tildes $ show n,
                                   ppr e]
  pprPrec _ (Map lam a _ _) = ppSOAC "map" [lam] [a]
  pprPrec _ (Reduce lam e a _ _) = ppSOAC "reduce" [lam] [e, a]
  pprPrec _ (Redomap redlam maplam e a _ _) =
    ppSOAC "redomap" [redlam, maplam] [e, a]
  pprPrec _ (Scan lam e a _ _) = ppSOAC "scan" [lam] [e, a]
  pprPrec _ (Filter lam a _ _) = ppSOAC "filter" [lam] [a]
  pprPrec _ (Zip es _) = text "zip" <> apply (map (ppr . fst) es)
  pprPrec _ (Unzip e _ _) = text "unzip" <> parens (ppr e)
  pprPrec _ (Split cs e a _ _) =
    ppCertificates cs <> text "split" <> apply [ppr e, ppr a]
  pprPrec _ (Concat cs x y _) =
    ppCertificates cs <> text "concat" <> apply [ppr x, ppr y]
  pprPrec _ (Copy e _) = text "copy" <> parens (ppr e)
  pprPrec _ (Assert e _) = text "assert" <> parens (ppr e)
  pprPrec _ (Conjoin es _) = text "conjoin" <> parens (commasep $ map ppr es)
  pprPrec _ (DoLoop pat initexp i bound loopbody letbody _) =
    aliasComment pat $
    text "loop" <+> parens (ppr pat <+> equals <+> ppr initexp) <+>
    equals <+> text "for" <+> ppr i <+> text "<" <+> align (ppr bound) <+> text "do" </>
    indent 2 (ppr loopbody) <+> text "in" </>
    ppr letbody
  pprPrec _ (Map2 cs lam as _ _) =
    ppCertificates cs <> ppSOAC "map2" [lam] as
  pprPrec _ (Reduce2 cs lam es as _ _) =
    ppCertificates cs <> ppSOAC "reduce2" [lam] (es++as)
  pprPrec _ (Redomap2 cs outer inner es as _ _) =
    ppCertificates cs <> text "redomap2" <>
    parens (ppr outer <> comma </> ppr inner <> comma </>
            commasep (braces (commasep $ map ppr es) : map ppr as))
  pprPrec _ (Scan2 cs lam es as _ _) =
    ppCertificates cs <> ppSOAC "scan2" [lam] (es++as)
  pprPrec _ (Filter2 cs lam as _) =
    ppCertificates cs <> ppSOAC "filter2" [lam] as

instance (Ord vn, Pretty vn) => Pretty (TupIdentBase ty vn) where
  ppr (Id ident)     = ppr ident
  ppr (TupId pats _) = braces $ commasep $ map ppr pats
  ppr (Wildcard _ _) = text "_"

instance (Ord vn, Pretty vn, TypeBox ty) => Pretty (LambdaBase ty vn) where
  ppr (CurryFun fname [] _ _) = text $ nameToString fname
  ppr (CurryFun fname curryargs _ _) =
    text (nameToString fname) <+> apply (map ppr curryargs)
  ppr (AnonymFun params body rettype _) =
    text "fn" <+> ppr rettype <+>
    apply (map ppParam params) <+>
    text "=>" </> indent 2 (ppr body)

instance (Ord vn, Pretty vn, TypeBox ty) => Pretty (TupleLambdaBase ty vn) where
  ppr (TupleLambda params body rets loc) =
    ppr (AnonymFun params body (Elem $ Tuple rets) loc)

instance (Ord vn, Pretty vn, TypeBox ty) => Pretty (ProgBase ty vn) where
  ppr = stack . punctuate line . map ppFun . progFunctions
    where ppFun (name, rettype, args, body, _) =
            text "fun" <+> ppr rettype <+>
            text (nameToString name) <//>
            apply (map ppParam args) <+>
            equals </> indent 2 (ppr body)

ppParam :: (Ord vn, Pretty (ty vn), Pretty vn, TypeBox ty) => IdentBase ty vn -> Doc
ppParam param = ppr (identType param) <+> ppr param

ppBinOp :: (Ord vn, Pretty vn, TypeBox ty) => Int -> BinOp -> ExpBase ty vn -> ExpBase ty vn -> Doc
ppBinOp p bop x y = parensIf (p > precedence bop) $
                    pprPrec (precedence bop) x <+>
                    text (opStr bop) <+>
                    pprPrec (rprecedence bop) y
  where precedence LogAnd = 0
        precedence LogOr = 0
        precedence Band = 1
        precedence Bor = 1
        precedence Xor = 1
        precedence Equal = 2
        precedence Less = 2
        precedence Leq = 2
        precedence ShiftL = 3
        precedence ShiftR = 3
        precedence Plus = 4
        precedence Minus = 4
        precedence Times = 5
        precedence Divide = 5
        precedence Mod = 5
        precedence Pow = 6
        rprecedence Minus = 10
        rprecedence op = precedence op

ppSOAC :: (Ord vn, Pretty vn, TypeBox ty, Pretty fn) =>
          String -> [fn] -> [ExpBase ty vn] -> Doc
ppSOAC name funs es =
  text name <> parens (ppList funs </>
                       commasep (map ppr es))

ppList :: (Pretty a) => [a] -> Doc
ppList as = case map ppr as of
              []     -> empty
              a':as' -> foldl (</>) (a' <> comma) $ map (<> comma) as'

ppCertificates :: (Ord vn, TypeBox ty, Pretty vn) => CertificatesBase ty vn -> Doc
ppCertificates [] = empty
ppCertificates cs = text "<" <> commasep (map ppr cs) <> text ">"

render80 :: Pretty a => a -> String
render80 = pretty 80 . ppr

-- | Prettyprint a value, wrapped to 80 characters.
ppValue :: Value -> String
ppValue = render80

-- | Prettyprint a type, wrapped to 80 characters.
ppType :: (Ord vn, Pretty vn) => TypeBase as vn -> String
ppType = render80

-- | Prettyprint an expression, wrapped to 80 characters.
ppExp :: (Ord vn, Pretty vn, TypeBox ty) => ExpBase ty vn -> String
ppExp = render80

-- | Prettyprint a lambda, wrapped to 80 characters.
ppLambda :: (Ord vn, Pretty vn, TypeBox ty) => LambdaBase ty vn -> String
ppLambda = render80

-- | Prettyprint a tuple lambda, wrapped to 80 characters.
ppTupleLambda :: (Ord vn, Pretty vn, TypeBox ty) => TupleLambdaBase ty vn -> String
ppTupleLambda = render80

-- | Prettyprint a pattern, wrapped to 80 characters.
ppTupId :: (Ord vn, Pretty vn, TypeBox ty) => TupIdentBase ty vn -> String
ppTupId = render80

-- | Prettyprint an entire L0 program, wrapped to 80 characters.
prettyPrint :: (Ord vn, Pretty vn, TypeBox ty) => ProgBase ty vn -> String
prettyPrint = render80
