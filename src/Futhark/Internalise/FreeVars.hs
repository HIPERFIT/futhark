-- | Facilities for computing free variables in an expression, which
-- we need for both lambda-lifting and defunctionalisation.
module Futhark.Internalise.FreeVars
  ( freeVars,
    without,
    member,
    ident,
    size,
    sizes,
    NameSet (..),
    patternVars,
  )
where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Futhark.IR.Pretty ()
import Language.Futhark

-- | A set of names where we also track uniqueness.
newtype NameSet = NameSet {unNameSet :: M.Map VName StructType}
  deriving (Show)

instance Semigroup NameSet where
  NameSet x <> NameSet y = NameSet $ M.unionWith max x y

instance Monoid NameSet where
  mempty = NameSet mempty

-- | Set subtraction.
without :: NameSet -> S.Set VName -> NameSet
without (NameSet x) y = NameSet $ M.filterWithKey keep x
  where
    keep k _ = k `S.notMember` y

withoutM :: NameSet -> NameSet -> NameSet
withoutM (NameSet x) (NameSet y) = NameSet $ x `M.difference` y

-- | Is this name in the 'NameSet'?
member :: VName -> NameSet -> Bool
member v (NameSet m) = v `M.member` m

-- | A 'NameSet' with a single 'Nonunique' name.
ident :: Ident -> NameSet
ident v = NameSet $ M.singleton (identName v) (toStruct $ unInfo $ identType v)

size :: VName -> NameSet
size v = NameSet $ M.singleton v $ Scalar $ Prim $ Signed Int64

sizes :: S.Set VName -> NameSet
sizes = foldMap size

-- | Compute the set of free variables of an expression.
freeVars :: Exp -> NameSet
freeVars expr = case expr of
  Literal {} -> mempty
  IntLit {} -> mempty
  FloatLit {} -> mempty
  StringLit {} -> mempty
  Parens e _ -> freeVars e
  QualParens _ e _ -> freeVars e
  TupLit es _ -> foldMap freeVars es
  RecordLit fs _ -> foldMap freeVarsField fs
    where
      freeVarsField (RecordFieldExplicit _ e _) = freeVars e
      freeVarsField (RecordFieldImplicit vn t _) = ident $ Ident vn t mempty
  ArrayLit es t _ ->
    foldMap freeVars es <> sizes (typeDimNames $ unInfo t)
  AppExp (Range e me incl _) _ ->
    freeVars e <> foldMap freeVars me <> foldMap freeVars incl
  Var qn (Info t) _ -> NameSet $ M.singleton (qualLeaf qn) $ toStruct t
  Ascript e t _ -> freeVars e <> sizes (typeDimNames $ unInfo $ expandedType t)
  AppExp (Coerce e t _) _ -> freeVars e <> sizes (typeDimNames $ unInfo $ expandedType t)
  AppExp (LetPat let_sizes pat e1 e2 _) _ ->
    freeVars e1
      <> ( (sizes (patternDimNames pat) <> freeVars e2)
             `withoutM` (patternVars pat <> foldMap (size . sizeName) let_sizes)
         )
  AppExp (LetFun vn (tparams, pats, _, _, e1) e2 _) _ ->
    ( (freeVars e1 <> sizes (foldMap patternDimNames pats))
        `without` ( S.map identName (foldMap patternIdents pats)
                      <> S.fromList (map typeParamName tparams)
                  )
    )
      <> (freeVars e2 `without` S.singleton vn)
  AppExp (If e1 e2 e3 _) _ -> freeVars e1 <> freeVars e2 <> freeVars e3
  AppExp (Apply e1 e2 _ _) _ -> freeVars e1 <> freeVars e2
  Negate e _ -> freeVars e
  Lambda pats e0 _ (Info (_, RetType dims t)) _ ->
    (sizes (foldMap patternDimNames pats) <> freeVars e0 <> sizes (typeDimNames t))
      `withoutM` (foldMap patternVars pats <> foldMap size dims)
  OpSection {} -> mempty
  OpSectionLeft _ _ e _ _ _ -> freeVars e
  OpSectionRight _ _ e _ _ _ -> freeVars e
  ProjectSection {} -> mempty
  IndexSection idxs _ _ -> foldMap freeDimIndex idxs
  AppExp (DoLoop sparams pat e1 form e3 _) _ ->
    let (e2fv, e2ident) = formVars form
     in freeVars e1
          <> ( (e2fv <> freeVars e3)
                 `withoutM` (sizes (S.fromList sparams) <> patternVars pat <> e2ident)
             )
    where
      formVars (For v e2) = (freeVars e2, ident v)
      formVars (ForIn p e2) = (freeVars e2, patternVars p)
      formVars (While e2) = (freeVars e2, mempty)
  AppExp (BinOp (qn, _) (Info qn_t) (e1, _) (e2, _) _) _ ->
    NameSet (M.singleton (qualLeaf qn) $ toStruct qn_t)
      <> freeVars e1
      <> freeVars e2
  Project _ e _ _ -> freeVars e
  AppExp (LetWith id1 id2 idxs e1 e2 _) _ ->
    ident id2 <> foldMap freeDimIndex idxs <> freeVars e1
      <> (freeVars e2 `without` S.singleton (identName id1))
  AppExp (Index e idxs _) _ -> freeVars e <> foldMap freeDimIndex idxs
  Update e1 idxs e2 _ -> freeVars e1 <> foldMap freeDimIndex idxs <> freeVars e2
  RecordUpdate e1 _ e2 _ _ -> freeVars e1 <> freeVars e2
  Assert e1 e2 _ _ -> freeVars e1 <> freeVars e2
  Constr _ es _ _ -> foldMap freeVars es
  Attr _ e _ -> freeVars e
  AppExp (Match e cs _) _ -> freeVars e <> foldMap caseFV cs
    where
      caseFV (CasePat p eCase _) =
        (sizes (patternDimNames p) <> freeVars eCase)
          `withoutM` patternVars p

freeDimIndex :: DimIndexBase Info VName -> NameSet
freeDimIndex (DimFix e) = freeVars e
freeDimIndex (DimSlice me1 me2 me3) =
  foldMap (foldMap freeVars) [me1, me2, me3]

-- | Extract all the variable names bound in a pattern.
patternVars :: Pattern -> NameSet
patternVars = mconcat . map ident . S.toList . patternIdents
