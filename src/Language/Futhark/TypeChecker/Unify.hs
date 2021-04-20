{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}

-- | Implementation of unification and other core type system building
-- blocks.
module Language.Futhark.TypeChecker.Unify
  ( Constraint (..),
    Usage,
    mkUsage,
    mkUsage',
    Level,
    Constraints,
    MonadUnify (..),
    Rigidity (..),
    RigidSource (..),
    BreadCrumbs,
    noBreadCrumbs,
    hasNoBreadCrumbs,
    dimNotes,
    mkTypeVarName,
    zeroOrderType,
    arrayElemType,
    mustHaveConstr,
    mustHaveField,
    mustBeOneOf,
    equalityType,
    normPatternType,
    normTypeFully,
    instantiateEmptyArrayDims,
    unify,
    expect,
    unifyMostCommon,
    anyDimOnMismatch,
    doUnification,
  )
where

import Control.Monad.Except
import Control.Monad.State
import Data.Bifoldable (biany)
import Data.Bifunctor
import Data.Char (isAscii)
import Data.List (foldl', intersect)
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Set as S
import Futhark.Util.Pretty hiding (empty)
import Language.Futhark hiding (unifyDims)
import Language.Futhark.TypeChecker.Monad hiding (BoundV)
import Language.Futhark.TypeChecker.Types

-- | A piece of information that describes what process the type
-- checker currently performing.  This is used to give better error
-- messages for unification errors.
data BreadCrumb
  = MatchingTypes StructType StructType
  | MatchingFields [Name]
  | MatchingConstructor Name
  | Matching Doc

instance Pretty BreadCrumb where
  ppr (MatchingTypes t1 t2) =
    "When matching type" </> indent 2 (ppr t1)
      </> "with"
      </> indent 2 (ppr t2)
  ppr (MatchingFields fields) =
    "When matching types of record field"
      <+> pquote (mconcat $ punctuate "." $ map ppr fields) <> dot
  ppr (MatchingConstructor c) =
    "When matching types of constructor" <+> pquote (ppr c) <> dot
  ppr (Matching s) =
    s

-- | Unification failures can occur deep down inside complicated types
-- (consider nested records).  We leave breadcrumbs behind us so we
-- can report the path we took to find the mismatch.
newtype BreadCrumbs = BreadCrumbs [BreadCrumb]

-- | An empty path.
noBreadCrumbs :: BreadCrumbs
noBreadCrumbs = BreadCrumbs []

-- | Is the path empty?
hasNoBreadCrumbs :: BreadCrumbs -> Bool
hasNoBreadCrumbs (BreadCrumbs xs) = null xs

-- | Drop a breadcrumb on the path behind you.
breadCrumb :: BreadCrumb -> BreadCrumbs -> BreadCrumbs
breadCrumb (MatchingFields xs) (BreadCrumbs (MatchingFields ys : bcs)) =
  BreadCrumbs $ MatchingFields (ys ++ xs) : bcs
breadCrumb bc (BreadCrumbs bcs) =
  BreadCrumbs $ bc : bcs

instance Pretty BreadCrumbs where
  ppr (BreadCrumbs []) = mempty
  ppr (BreadCrumbs bcs) = line <> stack (map ppr bcs)

-- | A usage that caused a type constraint.
data Usage = Usage (Maybe String) SrcLoc
  deriving (Show)

-- | Construct a 'Usage' from a location and a description.
mkUsage :: SrcLoc -> String -> Usage
mkUsage = flip (Usage . Just)

-- | Construct a 'Usage' that has just a location, but no particular
-- description.
mkUsage' :: SrcLoc -> Usage
mkUsage' = Usage Nothing

instance Pretty Usage where
  ppr (Usage Nothing loc) = "use at " <> textwrap (locStr loc)
  ppr (Usage (Just s) loc) = textwrap s <+/> "at" <+> textwrap (locStr loc)

instance Located Usage where
  locOf (Usage _ loc) = locOf loc

-- | The level at which a type variable is bound.  Higher means
-- deeper.  We can only unify a type variable at level @i@ with a type
-- @t@ if all type names that occur in @t@ are at most at level @i@.
type Level = Int

-- | A constraint on a yet-ambiguous type variable.
data Constraint
  = NoConstraint Liftedness Usage
  | ParamType Liftedness SrcLoc
  | Constraint StructRetType Usage
  | Overloaded [PrimType] Usage
  | HasFields (M.Map Name StructType) Usage
  | Equality Usage
  | HasConstrs (M.Map Name [StructType]) Usage
  | ParamSize SrcLoc
  | -- | Is not actually a type, but a term-level size,
    -- possibly already set to something specific.
    Size (Maybe (DimDecl VName)) Usage
  | -- | A size that does not unify with anything -
    -- created from the result of applying a function
    -- whose return size is existential, or otherwise
    -- hiding a size.
    UnknowableSize SrcLoc RigidSource
  deriving (Show)

instance Located Constraint where
  locOf (NoConstraint _ usage) = locOf usage
  locOf (ParamType _ usage) = locOf usage
  locOf (Constraint _ usage) = locOf usage
  locOf (Overloaded _ usage) = locOf usage
  locOf (HasFields _ usage) = locOf usage
  locOf (Equality usage) = locOf usage
  locOf (HasConstrs _ usage) = locOf usage
  locOf (ParamSize loc) = locOf loc
  locOf (Size _ usage) = locOf usage
  locOf (UnknowableSize loc _) = locOf loc

-- | Mapping from fresh type variables, instantiated from the type
-- schemes of polymorphic functions, to (possibly) specific types as
-- determined on application and the location of that application, or
-- a partial constraint on their type.
type Constraints = M.Map VName (Level, Constraint)

lookupSubst :: VName -> Constraints -> Maybe (Subst StructRetType)
lookupSubst v constraints = case snd <$> M.lookup v constraints of
  Just (Constraint t _) -> Just $ Subst [] $ applySubst (`lookupSubst` constraints) t
  Just Overloaded {} -> Just PrimSubst
  Just (Size (Just d) _) ->
    Just $ SizeSubst $ applySubst (`lookupSubst` constraints) d
  _ -> Nothing

-- | The source of a rigid size.
data RigidSource
  = -- | A function argument that is not a constant or variable name.
    RigidArg (Maybe (QualName VName)) String
  | -- | An existential return size.
    RigidRet (Maybe (QualName VName))
  | RigidLoop
  | -- | Produced by a complicated slice expression.
    RigidSlice (Maybe (DimDecl VName)) String
  | -- | Produced by a complicated range expression.
    RigidRange
  | -- | Produced by a range expression with this bound.
    RigidBound String
  | -- | Mismatch in branches.
    RigidCond StructType StructType
  | -- | Invented during unification.
    RigidUnify
  | RigidOutOfScope SrcLoc VName
  deriving (Eq, Ord, Show)

-- | The ridigity of a size variable.  All rigid sizes are tagged with
-- information about how they were generated.
data Rigidity = Rigid RigidSource | Nonrigid
  deriving (Eq, Ord, Show)

prettySource :: SrcLoc -> SrcLoc -> RigidSource -> Doc
prettySource ctx loc (RigidRet Nothing) =
  "is unknown size returned by function at"
    <+> text (locStrRel ctx loc) <> "."
prettySource ctx loc (RigidRet (Just fname)) =
  "is unknown size returned by" <+> pquote (ppr fname)
    <+> "at"
    <+> text (locStrRel ctx loc) <> "."
prettySource ctx loc (RigidArg fname arg) =
  "is value of argument"
    </> indent 2 (shorten arg)
    </> "passed to" <+> fname' <+> "at" <+> text (locStrRel ctx loc) <> "."
  where
    fname' = maybe "function" (pquote . ppr) fname
prettySource ctx loc (RigidSlice d slice) =
  "is size produced by slice"
    </> indent 2 (shorten slice)
    </> d_desc <> "at" <+> text (locStrRel ctx loc) <> "."
  where
    d_desc = case d of
      Just d' -> "of dimension of size " <> pquote (ppr d') <> " "
      Nothing -> mempty
prettySource ctx loc RigidLoop =
  "is unknown size of value returned at" <+> text (locStrRel ctx loc) <> "."
prettySource ctx loc RigidRange =
  "is unknown length of range at" <+> text (locStrRel ctx loc) <> "."
prettySource ctx loc (RigidBound bound) =
  "generated from expression"
    </> indent 2 (shorten bound)
    </> "used in range at " <> text (locStrRel ctx loc) <> "."
prettySource ctx loc (RigidOutOfScope boundloc v) =
  "is an unknown size arising from " <> pquote (pprName v)
    <> " going out of scope at "
    <> text (locStrRel ctx loc)
    <> "."
    </> "Originally bound at "
    <> text (locStrRel ctx boundloc)
    <> "."
prettySource _ _ RigidUnify =
  "is an artificial size invented during unification of functions with anonymous sizes."
prettySource ctx loc (RigidCond t1 t2) =
  "is unknown due to conditional expression at "
    <> text (locStrRel ctx loc)
    <> "."
    </> "One branch returns array of type: "
    <> align (ppr t1)
    </> "The other an array of type:       "
    <> align (ppr t2)

-- | Retrieve notes describing the purpose or origin of the given
-- 'DimDecl'.  The location is used as the *current* location, for the
-- purpose of reporting relative locations.
dimNotes :: (Located a, MonadUnify m) => a -> DimDecl VName -> m Notes
dimNotes ctx (NamedDim d) = do
  c <- M.lookup (qualLeaf d) <$> getConstraints
  case c of
    Just (_, UnknowableSize loc rsrc) ->
      return $
        aNote $
          pretty $
            pquote (ppr d) <+> prettySource (srclocOf ctx) loc rsrc
    _ -> return mempty
dimNotes _ _ = return mempty

typeNotes :: (Located a, MonadUnify m) => a -> StructType -> m Notes
typeNotes ctx =
  fmap mconcat . mapM (dimNotes ctx . NamedDim . qualName)
    . S.toList
    . typeDimNames

-- | Monads that which to perform unification must implement this type
-- class.
class Monad m => MonadUnify m where
  getConstraints :: m Constraints
  putConstraints :: Constraints -> m ()
  modifyConstraints :: (Constraints -> Constraints) -> m ()
  modifyConstraints f = do
    x <- getConstraints
    putConstraints $ f x

  newTypeVar :: Monoid als => SrcLoc -> String -> m (TypeBase dim als)
  newDimVar :: SrcLoc -> Rigidity -> String -> m VName

  curLevel :: m Level

  matchError ::
    Located loc =>
    loc ->
    Notes ->
    BreadCrumbs ->
    StructType ->
    StructType ->
    m a

  unifyError ::
    Located loc =>
    loc ->
    Notes ->
    BreadCrumbs ->
    Doc ->
    m a

-- | Replace all type variables with their substitution.
normTypeFully :: (Substitutable a, MonadUnify m) => a -> m a
normTypeFully t = do
  constraints <- getConstraints
  return $ applySubst (`lookupSubst` constraints) t

-- | Replace any top-level type variable with its substitution.
normType :: MonadUnify m => StructType -> m StructType
normType t@(Scalar (TypeVar _ _ (TypeName [] v) [])) = do
  constraints <- getConstraints
  case snd <$> M.lookup v constraints of
    Just (Constraint (RetType [] t') _) -> normType t'
    _ -> return t
normType t = return t

-- | Replace any top-level type variable with its substitution.
normPatternType :: MonadUnify m => PatternType -> m PatternType
normPatternType t@(Scalar (TypeVar als u (TypeName [] v) [])) = do
  constraints <- getConstraints
  case snd <$> M.lookup v constraints of
    Just (Constraint (RetType [] t') _) ->
      normPatternType $ t' `setUniqueness` u `setAliases` als
    _ -> return t
normPatternType t = return t

rigidConstraint :: Constraint -> Bool
rigidConstraint ParamType {} = True
rigidConstraint ParamSize {} = True
rigidConstraint UnknowableSize {} = True
rigidConstraint _ = False

-- | Instantiate existential context in return type.
instantiateEmptyArrayDims ::
  MonadUnify m =>
  SrcLoc ->
  Rigidity ->
  RetTypeBase (DimDecl VName) als ->
  m (TypeBase (DimDecl VName) als, [VName])
instantiateEmptyArrayDims tloc r (RetType dims t) = do
  dims' <- mapM new dims
  pure (first (onDim $ zip dims dims') t, dims')
  where
    new = newDimVar tloc r . takeWhile isAscii . baseString
    onDim dims' (NamedDim d) =
      NamedDim $ maybe d qualName (lookup (qualLeaf d) dims')
    onDim _ (ConstDim d) = ConstDim d

-- | Is the given type variable the name of an abstract type or type
-- parameter, which we cannot substitute?
isRigid :: VName -> Constraints -> Bool
isRigid v constraints =
  maybe True (rigidConstraint . snd) $ M.lookup v constraints

-- | If the given type variable is nonrigid, what is its level?
isNonRigid :: VName -> Constraints -> Maybe Level
isNonRigid v constraints = do
  (lvl, c) <- M.lookup v constraints
  guard $ not $ rigidConstraint c
  return lvl

type UnifyDims m =
  BreadCrumbs -> [VName] -> (VName -> Maybe Int) -> DimDecl VName -> DimDecl VName -> m ()

flipUnifyDims :: UnifyDims m -> UnifyDims m
flipUnifyDims onDims bcs bound nonrigid t1 t2 =
  onDims bcs bound nonrigid t2 t1

unifyWith ::
  MonadUnify m =>
  UnifyDims m ->
  Usage ->
  BreadCrumbs ->
  StructType ->
  StructType ->
  m ()
unifyWith onDims usage = subunify False mempty
  where
    swap True x y = (y, x)
    swap False x y = (x, y)

    subunify ord bound bcs t1 t2 = do
      constraints <- getConstraints

      t1' <- normType t1
      t2' <- normType t2

      let nonrigid v = isNonRigid v constraints

          failure = matchError (srclocOf usage) mempty bcs t1' t2'

          link ord' v lvl =
            linkVarToType bound linkDims usage bcs v lvl
            where
              -- We may have to flip the order of future calls to
              -- onDims inside linkVarToType.
              linkDims
                | ord' = flipUnifyDims onDims
                | otherwise = onDims

          unifyTypeArg bcs' (TypeArgDim d1 _) (TypeArgDim d2 _) =
            onDims' bcs' (swap ord d1 d2)
          unifyTypeArg bcs' (TypeArgType t _) (TypeArgType arg_t _) =
            subunify ord bound bcs' t arg_t
          unifyTypeArg bcs' _ _ =
            unifyError
              usage
              mempty
              bcs'
              "Cannot unify a type argument with a dimension argument (or vice versa)."

          onDims' bcs' (d1, d2) =
            onDims
              bcs'
              bound
              nonrigid
              (applySubst (`lookupSubst` constraints) d1)
              (applySubst (`lookupSubst` constraints) d2)

      case (t1', t2') of
        ( Scalar (Record fs),
          Scalar (Record arg_fs)
          )
            | M.keys fs == M.keys arg_fs ->
              forM_ (M.toList $ M.intersectionWith (,) fs arg_fs) $ \(k, (k_t1, k_t2)) -> do
                let bcs' = breadCrumb (MatchingFields [k]) bcs
                subunify ord bound bcs' k_t1 k_t2
            | otherwise -> do
              let missing =
                    filter (`notElem` M.keys arg_fs) (M.keys fs)
                      ++ filter (`notElem` M.keys fs) (M.keys arg_fs)
              unifyError usage mempty bcs $
                "Unshared fields:" <+> commasep (map ppr missing) <> "."
        ( Scalar (TypeVar _ _ (TypeName _ tn) targs),
          Scalar (TypeVar _ _ (TypeName _ arg_tn) arg_targs)
          )
            | tn == arg_tn,
              length targs == length arg_targs -> do
              let bcs' = breadCrumb (Matching "When matching type arguments.") bcs
              zipWithM_ (unifyTypeArg bcs') targs arg_targs
        ( Scalar (TypeVar _ _ (TypeName [] v1) []),
          Scalar (TypeVar _ _ (TypeName [] v2) [])
          ) ->
            case (nonrigid v1, nonrigid v2) of
              (Nothing, Nothing) -> failure
              (Just lvl1, Nothing) -> link ord v1 lvl1 t2'
              (Nothing, Just lvl2) -> link (not ord) v2 lvl2 t1'
              (Just lvl1, Just lvl2)
                | lvl1 <= lvl2 -> link ord v1 lvl1 t2'
                | otherwise -> link (not ord) v2 lvl2 t1'
        (Scalar (TypeVar _ _ (TypeName [] v1) []), _)
          | Just lvl <- nonrigid v1 ->
            link ord v1 lvl t2'
        (_, Scalar (TypeVar _ _ (TypeName [] v2) []))
          | Just lvl <- nonrigid v2 ->
            link (not ord) v2 lvl t1'
        ( Scalar (Arrow _ p1 a1 (RetType b1_dims b1)),
          Scalar (Arrow _ p2 a2 (RetType b2_dims b2))
          ) -> do
            -- Introduce the existentials as size variables so they
            -- are subject to unification.  We will remove them again
            -- afterwards.
            let (r1, r2) =
                  swap
                    ord
                    (Size Nothing $ Usage Nothing mempty)
                    (UnknowableSize mempty RigidUnify)
            lvl <- curLevel
            modifyConstraints (M.fromList (zip b1_dims $ repeat (lvl, r1)) <>)
            modifyConstraints (M.fromList (zip b2_dims $ repeat (lvl, r2)) <>)

            let bound' = bound <> mapMaybe pname [p1, p2] <> b1_dims <> b2_dims
            subunify
              (not ord)
              bound
              (breadCrumb (Matching "When matching parameter types.") bcs)
              a1
              a2
            subunify
              ord
              bound'
              (breadCrumb (Matching "When matching return types.") bcs)
              b1'
              b2'

            -- Delete the size variables we introduced to represent
            -- the existential sizes.
            modifyConstraints $ \m -> foldl' (flip M.delete) m (b1_dims <> b2_dims)
            where
              (b1', b2') =
                -- Replace one parameter name with the other in the
                -- return type, in case of dependent types.  I.e.,
                -- we want type '(n: i32) -> [n]i32' to unify with
                -- type '(x: i32) -> [x]i32'.
                case (p1, p2) of
                  (Named p1', Named p2') ->
                    let f v
                          | v == p2' = Just $ SizeSubst $ NamedDim $ qualName p1'
                          | otherwise = Nothing
                     in (b1, applySubst f b2)
                  (_, _) ->
                    (b1, b2)

              pname (Named x) = Just x
              pname Unnamed = Nothing
        (Array {}, Array {})
          | ShapeDecl (t1_d : _) <- arrayShape t1',
            ShapeDecl (t2_d : _) <- arrayShape t2',
            Just t1'' <- peelArray 1 t1',
            Just t2'' <- peelArray 1 t2' -> do
            onDims' bcs (swap ord t1_d t2_d)
            subunify ord bound bcs t1'' t2''
        ( Scalar (Sum cs),
          Scalar (Sum arg_cs)
          )
            | M.keys cs == M.keys arg_cs ->
              unifySharedConstructors onDims usage bcs cs arg_cs
            | otherwise -> do
              let missing =
                    filter (`notElem` M.keys arg_cs) (M.keys cs)
                      ++ filter (`notElem` M.keys cs) (M.keys arg_cs)
              unifyError usage mempty bcs $
                "Unshared constructors:" <+> commasep (map (("#" <>) . ppr) missing) <> "."
        _
          | t1' == t2' -> return ()
          | otherwise -> failure

unifyDims :: MonadUnify m => Usage -> UnifyDims m
unifyDims _ _ _ _ d1 d2
  | d1 == d2 = return ()
unifyDims usage bcs _ nonrigid (NamedDim (QualName _ d1)) d2
  | Just lvl1 <- nonrigid d1 =
    linkVarToDim usage bcs d1 lvl1 d2
unifyDims usage bcs _ nonrigid d1 (NamedDim (QualName _ d2))
  | Just lvl2 <- nonrigid d2 =
    linkVarToDim usage bcs d2 lvl2 d1
unifyDims usage bcs _ _ d1 d2 = do
  notes <- (<>) <$> dimNotes usage d1 <*> dimNotes usage d2
  unifyError usage notes bcs $
    "Dimensions" <+> pquote (ppr d1)
      <+> "and"
      <+> pquote (ppr d2)
      <+> "do not match."

-- | Unifies two types.
unify :: MonadUnify m => Usage -> StructType -> StructType -> m ()
unify usage = unifyWith (unifyDims usage) usage noBreadCrumbs

-- | @expect super sub@ checks that @sub@ is a subtype of @super@.
expect :: MonadUnify m => Usage -> StructType -> StructType -> m ()
expect usage = unifyWith onDims usage noBreadCrumbs
  where
    onDims _ _ _ d1 d2
      | d1 == d2 = return ()
    -- We identify existentially bound names by them being nonrigid
    -- and yet bound.  It's OK to unify with those.
    onDims bcs bound nonrigid (NamedDim (QualName _ d1)) d2
      | Just lvl1 <- nonrigid d1,
        not $ isAnyDim d2,
        not (boundParam bound d2) || (d1 `elem` bound) =
        linkVarToDim usage bcs d1 lvl1 d2
    onDims bcs bound nonrigid d1 (NamedDim (QualName _ d2))
      | Just lvl2 <- nonrigid d2,
        not (boundParam bound d1) || (d2 `elem` bound) =
        linkVarToDim usage bcs d2 lvl2 d1
    onDims bcs _ _ d1 d2 = do
      notes <- (<>) <$> dimNotes usage d1 <*> dimNotes usage d2
      unifyError usage notes bcs $
        "Dimensions" <+> pquote (ppr d1)
          <+> "and"
          <+> pquote (ppr d2)
          <+> "do not match."

    boundParam bound (NamedDim (QualName _ d)) = d `elem` bound
    boundParam _ _ = False

    isAnyDim _ = False

occursCheck ::
  MonadUnify m =>
  Usage ->
  BreadCrumbs ->
  VName ->
  StructType ->
  m ()
occursCheck usage bcs vn tp =
  when (vn `S.member` typeVars tp) $
    unifyError usage mempty bcs $
      "Occurs check: cannot instantiate"
        <+> pprName vn
        <+> "with"
        <+> ppr tp <> "."

scopeCheck ::
  MonadUnify m =>
  Usage ->
  BreadCrumbs ->
  VName ->
  Level ->
  StructType ->
  m ()
scopeCheck usage bcs vn max_lvl tp = do
  constraints <- getConstraints
  checkType constraints tp
  where
    checkType constraints t =
      mapM_ (check constraints) $ typeVars t <> typeDimNames t

    check constraints v
      | Just (lvl, c) <- M.lookup v constraints,
        lvl > max_lvl =
        if rigidConstraint c
          then scopeViolation v
          else modifyConstraints $ M.insert v (max_lvl, c)
      | otherwise =
        return ()

    scopeViolation v = do
      notes <- typeNotes usage tp
      unifyError usage notes bcs $
        "Cannot unify type"
          </> indent 2 (ppr tp)
          </> "with"
          <+> pquote (pprName vn)
          <+> "(scope violation)."
          </> "This is because"
          <+> pquote (pprName v)
          <+> "is rigidly bound in a deeper scope."

linkVarToType ::
  MonadUnify m =>
  [VName] ->
  UnifyDims m ->
  Usage ->
  BreadCrumbs ->
  VName ->
  Level ->
  StructType ->
  m ()
linkVarToType locally_bound onDims usage bcs vn lvl tp = do
  occursCheck usage bcs vn tp
  scopeCheck usage bcs vn lvl tp

  constraints <- getConstraints
  let ext = filter (`S.member` typeDimNames tp) locally_bound
  modifyConstraints $ M.insert vn (lvl, Constraint (RetType ext tp) usage)

  case snd <$> M.lookup vn constraints of
    Just (NoConstraint Unlifted unlift_usage) -> do
      let bcs' =
            breadCrumb
              ( Matching $
                  "When verifying that" <+> pquote (pprName vn)
                    <+> textwrap "is not instantiated with a function type, due to"
                    <+> ppr unlift_usage
              )
              bcs

      arrayElemTypeWith usage bcs' tp
      when (any (`elem` locally_bound) (typeDimNames tp)) $
        unifyError usage mempty bcs $
          "Type variable" <+> pprName vn
            <+> "cannot be instantiated with type containing anonymous sizes:"
            </> indent 2 (ppr tp)
            </> textwrap "This is usually because the size of an array returned by a higher-order function argument cannot be determined statically.  This can also be due to the return size being a value parameter.  Add type annotation to clarify."
    Just (Equality _) ->
      equalityType usage tp
    Just (Overloaded ts old_usage)
      | tp `notElem` map (Scalar . Prim) ts ->
        case tp of
          Scalar (TypeVar _ _ (TypeName [] v) [])
            | not $ isRigid v constraints ->
              linkVarToTypes usage v ts
          _ ->
            unifyError usage mempty bcs $
              "Cannot instantiate" <+> pquote (pprName vn)
                <+> "with type" </> indent 2 (ppr tp) </> "as"
                <+> pquote (pprName vn)
                <+> "must be one of"
                <+> commasep (map ppr ts)
                <+/> "due to"
                <+/> ppr old_usage <> "."
    Just (HasFields required_fields old_usage) ->
      case tp of
        Scalar (Record tp_fields)
          | all (`M.member` tp_fields) $ M.keys required_fields -> do
            required_fields' <- mapM normTypeFully required_fields
            let bcs' =
                  breadCrumb
                    ( Matching $
                        pprName vn
                          <+> "must be a record with at least the fields:"
                          </> indent 2 (ppr (Record required_fields'))
                          </> "due to"
                          <+> ppr old_usage <> "."
                    )
                    bcs
            mapM_ (uncurry $ unifyWith onDims usage bcs') $
              M.elems $
                M.intersectionWith (,) required_fields tp_fields
        Scalar (TypeVar _ _ (TypeName [] v) [])
          | not $ isRigid v constraints ->
            modifyConstraints $
              M.insert
                v
                (lvl, HasFields required_fields old_usage)
        _ ->
          unifyError usage mempty bcs $
            "Cannot instantiate" <+> pquote (pprName vn) <+> "with type"
              </> indent 2 (ppr tp)
              </> "as" <+> pquote (pprName vn) <+> "must be a record with fields"
              </> indent 2 (ppr (Record required_fields))
              </> "due to" <+> ppr old_usage <> "."
    Just (HasConstrs required_cs old_usage) ->
      case tp of
        Scalar (Sum ts)
          | all (`M.member` ts) $ M.keys required_cs ->
            unifySharedConstructors onDims usage bcs required_cs ts
        Scalar (TypeVar _ _ (TypeName [] v) [])
          | not $ isRigid v constraints -> do
            case M.lookup v constraints of
              Just (_, HasConstrs v_cs _) ->
                unifySharedConstructors onDims usage bcs required_cs v_cs
              _ -> return ()
            modifyConstraints $
              M.insertWith
                combineConstrs
                v
                (lvl, HasConstrs required_cs old_usage)
          where
            combineConstrs (_, HasConstrs cs1 usage1) (_, HasConstrs cs2 _) =
              (lvl, HasConstrs (M.union cs1 cs2) usage1)
            combineConstrs hasCs _ = hasCs
        _ -> noSumType
    _ -> return ()
  where
    noSumType =
      unifyError
        usage
        mempty
        bcs
        "Cannot unify a sum type with a non-sum type"

linkVarToDim ::
  MonadUnify m =>
  Usage ->
  BreadCrumbs ->
  VName ->
  Level ->
  DimDecl VName ->
  m ()
linkVarToDim usage bcs vn lvl dim = do
  constraints <- getConstraints

  case dim of
    NamedDim dim'
      | Just (dim_lvl, c) <- qualLeaf dim' `M.lookup` constraints,
        dim_lvl > lvl ->
        case c of
          ParamSize {} -> do
            notes <- dimNotes usage dim
            unifyError usage notes bcs $
              "Cannot unify size variable" <+> pquote (ppr dim')
                <+> "with"
                <+> pquote (pprName vn)
                <+> "(scope violation)."
                </> "This is because"
                <+> pquote (ppr dim')
                <+> "is rigidly bound in a deeper scope."
          _ -> modifyConstraints $ M.insert (qualLeaf dim') (lvl, c)
    _ -> return ()

  modifyConstraints $ M.insert vn (lvl, Size (Just dim) usage)

-- | Assert that this type must be one of the given primitive types.
mustBeOneOf :: MonadUnify m => [PrimType] -> Usage -> StructType -> m ()
mustBeOneOf [req_t] usage t = unify usage (Scalar (Prim req_t)) t
mustBeOneOf ts usage t = do
  t' <- normType t
  constraints <- getConstraints
  let isRigid' v = isRigid v constraints

  case t' of
    Scalar (TypeVar _ _ (TypeName [] v) [])
      | not $ isRigid' v -> linkVarToTypes usage v ts
    Scalar (Prim pt) | pt `elem` ts -> return ()
    _ -> failure
  where
    failure =
      unifyError usage mempty noBreadCrumbs $
        text "Cannot unify type" <+> pquote (ppr t)
          <+> "with any of " <> commasep (map ppr ts) <> "."

linkVarToTypes :: MonadUnify m => Usage -> VName -> [PrimType] -> m ()
linkVarToTypes usage vn ts = do
  vn_constraint <- M.lookup vn <$> getConstraints
  case vn_constraint of
    Just (lvl, Overloaded vn_ts vn_usage) ->
      case ts `intersect` vn_ts of
        [] ->
          unifyError usage mempty noBreadCrumbs $
            "Type constrained to one of"
              <+> commasep (map ppr ts)
              <+> "but also one of"
              <+> commasep (map ppr vn_ts)
              <+> "due to"
              <+> ppr vn_usage <> "."
        ts' -> modifyConstraints $ M.insert vn (lvl, Overloaded ts' usage)
    Just (_, HasConstrs _ vn_usage) ->
      unifyError usage mempty noBreadCrumbs $
        "Type constrained to one of" <+> commasep (map ppr ts)
          <> ", but also inferred to be sum type due to" <+> ppr vn_usage
          <> "."
    Just (_, HasFields _ vn_usage) ->
      unifyError usage mempty noBreadCrumbs $
        "Type constrained to one of" <+> commasep (map ppr ts)
          <> ", but also inferred to be record due to" <+> ppr vn_usage
          <> "."
    Just (lvl, _) -> modifyConstraints $ M.insert vn (lvl, Overloaded ts usage)
    Nothing ->
      unifyError usage mempty noBreadCrumbs $
        "Cannot constrain type to one of" <+> commasep (map ppr ts)

-- | Assert that this type must support equality.
equalityType ::
  (MonadUnify m, Pretty (ShapeDecl dim), Monoid as) =>
  Usage ->
  TypeBase dim as ->
  m ()
equalityType usage t = do
  unless (orderZero t) $
    unifyError usage mempty noBreadCrumbs $
      "Type " <+> pquote (ppr t) <+> "does not support equality (is higher-order)."
  mapM_ mustBeEquality $ typeVars t
  where
    mustBeEquality vn = do
      constraints <- getConstraints
      case M.lookup vn constraints of
        Just (_, Constraint (RetType [] (Scalar (TypeVar _ _ (TypeName [] vn') []))) _) ->
          mustBeEquality vn'
        Just (_, Constraint (RetType _ vn_t) cusage)
          | not $ orderZero vn_t ->
            unifyError usage mempty noBreadCrumbs $
              "Type" <+> pquote (ppr t) <+> "does not support equality."
                </> "Constrained to be higher-order due to" <+> ppr cusage <+> "."
          | otherwise -> return ()
        Just (lvl, NoConstraint _ _) ->
          modifyConstraints $ M.insert vn (lvl, Equality usage)
        Just (_, Overloaded _ _) ->
          return () -- All primtypes support equality.
        Just (_, Equality {}) ->
          return ()
        Just (_, HasConstrs cs _) ->
          mapM_ (equalityType usage) $ concat $ M.elems cs
        _ ->
          unifyError usage mempty noBreadCrumbs $
            "Type" <+> pprName vn <+> "does not support equality."

zeroOrderTypeWith ::
  (MonadUnify m, Pretty (ShapeDecl dim), Monoid as) =>
  Usage ->
  BreadCrumbs ->
  TypeBase dim as ->
  m ()
zeroOrderTypeWith usage bcs t = do
  unless (orderZero t) $
    unifyError usage mempty bcs $
      "Type" </> indent 2 (ppr t) </> "found to be functional."
  mapM_ mustBeZeroOrder . S.toList . typeVars $ t
  where
    mustBeZeroOrder vn = do
      constraints <- getConstraints
      case M.lookup vn constraints of
        Just (lvl, NoConstraint _ _) ->
          modifyConstraints $ M.insert vn (lvl, NoConstraint Unlifted usage)
        Just (_, ParamType Lifted ploc) ->
          unifyError usage mempty bcs $
            "Type parameter"
              <+> pquote (pprName vn)
              <+> "at"
              <+> text (locStr ploc)
              <+> "may be a function."
        _ -> return ()

-- | Assert that this type must be zero-order.
zeroOrderType ::
  (MonadUnify m, Pretty (ShapeDecl dim), Monoid as) =>
  Usage ->
  String ->
  TypeBase dim as ->
  m ()
zeroOrderType usage desc =
  zeroOrderTypeWith usage $ breadCrumb bc noBreadCrumbs
  where
    bc = Matching $ "When checking" <+> textwrap desc

arrayElemTypeWith ::
  (MonadUnify m, Pretty (ShapeDecl dim), Monoid as) =>
  Usage ->
  BreadCrumbs ->
  TypeBase dim as ->
  m ()
arrayElemTypeWith usage bcs t = do
  unless (orderZero t) $
    unifyError usage mempty bcs $
      "Type" </> indent 2 (ppr t) </> "found to be functional."
  mapM_ mustBeZeroOrder . S.toList . typeVars $ t
  where
    mustBeZeroOrder vn = do
      constraints <- getConstraints
      case M.lookup vn constraints of
        Just (lvl, NoConstraint _ _) ->
          modifyConstraints $ M.insert vn (lvl, NoConstraint Unlifted usage)
        Just (_, ParamType l ploc)
          | l `elem` [Lifted, SizeLifted] ->
            unifyError usage mempty bcs $
              "Type parameter"
                <+> pquote (pprName vn)
                <+> "bound at"
                <+> text (locStr ploc)
                <+> "is lifted and cannot be an array element."
        _ -> return ()

-- | Assert that this type must be valid as an array element.
arrayElemType ::
  (MonadUnify m, Pretty (ShapeDecl dim), Monoid as) =>
  Usage ->
  String ->
  TypeBase dim as ->
  m ()
arrayElemType usage desc =
  arrayElemTypeWith usage $ breadCrumb bc noBreadCrumbs
  where
    bc = Matching $ "When checking" <+> textwrap desc

unifySharedConstructors ::
  MonadUnify m =>
  UnifyDims m ->
  Usage ->
  BreadCrumbs ->
  M.Map Name [StructType] ->
  M.Map Name [StructType] ->
  m ()
unifySharedConstructors onDims usage bcs cs1 cs2 =
  forM_ (M.toList $ M.intersectionWith (,) cs1 cs2) $ \(c, (f1, f2)) ->
    unifyConstructor c f1 f2
  where
    unifyConstructor c f1 f2
      | length f1 == length f2 = do
        let bcs' = breadCrumb (MatchingConstructor c) bcs
        zipWithM_ (unifyWith onDims usage bcs') f1 f2
      | otherwise =
        unifyError usage mempty bcs $
          "Cannot unify constructor" <+> pquote (pprName c) <> "."

-- | In @mustHaveConstr usage c t fs@, the type @t@ must have a
-- constructor named @c@ that takes arguments of types @ts@.
mustHaveConstr ::
  MonadUnify m =>
  Usage ->
  Name ->
  StructType ->
  [StructType] ->
  m ()
mustHaveConstr usage c t fs = do
  constraints <- getConstraints
  case t of
    Scalar (TypeVar _ _ (TypeName _ tn) [])
      | Just (lvl, NoConstraint {}) <- M.lookup tn constraints -> do
        mapM_ (scopeCheck usage noBreadCrumbs tn lvl) fs
        modifyConstraints $ M.insert tn (lvl, HasConstrs (M.singleton c fs) usage)
      | Just (lvl, HasConstrs cs _) <- M.lookup tn constraints ->
        case M.lookup c cs of
          Nothing -> modifyConstraints $ M.insert tn (lvl, HasConstrs (M.insert c fs cs) usage)
          Just fs'
            | length fs == length fs' -> zipWithM_ (unify usage) fs fs'
            | otherwise ->
              unifyError usage mempty noBreadCrumbs $
                "Different arity for constructor" <+> pquote (ppr c) <> "."
    Scalar (Sum cs) ->
      case M.lookup c cs of
        Nothing ->
          unifyError usage mempty noBreadCrumbs $
            "Constuctor" <+> pquote (ppr c) <+> "not present in type."
        Just fs'
          | length fs == length fs' -> zipWithM_ (unify usage) fs fs'
          | otherwise ->
            unifyError usage mempty noBreadCrumbs $
              "Different arity for constructor" <+> pquote (ppr c) <+> "."
    _ -> do
      unify usage t $ Scalar $ Sum $ M.singleton c fs
      return ()

mustHaveFieldWith ::
  MonadUnify m =>
  UnifyDims m ->
  Usage ->
  BreadCrumbs ->
  Name ->
  PatternType ->
  m PatternType
mustHaveFieldWith onDims usage bcs l t = do
  constraints <- getConstraints
  l_type <- newTypeVar (srclocOf usage) "t"
  let l_type' = toStruct l_type
  case t of
    Scalar (TypeVar _ _ (TypeName _ tn) [])
      | Just (lvl, NoConstraint {}) <- M.lookup tn constraints -> do
        scopeCheck usage bcs tn lvl l_type'
        modifyConstraints $ M.insert tn (lvl, HasFields (M.singleton l l_type') usage)
        return l_type
      | Just (lvl, HasFields fields _) <- M.lookup tn constraints -> do
        case M.lookup l fields of
          Just t' -> unifyWith onDims usage bcs l_type' t'
          Nothing ->
            modifyConstraints $
              M.insert
                tn
                (lvl, HasFields (M.insert l l_type' fields) usage)
        return l_type
    Scalar (Record fields)
      | Just t' <- M.lookup l fields -> do
        unify usage l_type' $ toStruct t'
        return t'
      | otherwise ->
        unifyError usage mempty bcs $
          "Attempt to access field" <+> pquote (ppr l) <+> " of value of type"
            <+> ppr (toStructural t) <> "."
    _ -> do
      unify usage (toStruct t) $ Scalar $ Record $ M.singleton l l_type'
      return l_type

-- | Assert that some type must have a field with this name and type.
mustHaveField ::
  MonadUnify m =>
  Usage ->
  Name ->
  PatternType ->
  m PatternType
mustHaveField usage = mustHaveFieldWith (unifyDims usage) usage noBreadCrumbs

-- | Replace dimension mismatches with AnyDim.
anyDimOnMismatch ::
  Monoid as =>
  TypeBase (DimDecl VName) as ->
  TypeBase (DimDecl VName) as ->
  (TypeBase (DimDecl VName) as, [(DimDecl VName, DimDecl VName)])
anyDimOnMismatch t1 t2 = runState (matchDims onDims t1 t2) []
  where
    onDims d1 d2
      | d1 == d2 = return d1
      | otherwise = do
        modify ((d1, d2) :)
        return $ undefined

newDimOnMismatch ::
  (Monoid as, MonadUnify m) =>
  SrcLoc ->
  TypeBase (DimDecl VName) as ->
  TypeBase (DimDecl VName) as ->
  m (TypeBase (DimDecl VName) as, [VName])
newDimOnMismatch loc t1 t2 = do
  (t, seen) <- runStateT (matchDims onDims t1 t2) mempty
  return (t, M.elems seen)
  where
    r = Rigid $ RigidCond (toStruct t1) (toStruct t2)
    onDims d1 d2
      | d1 == d2 = return d1
      | otherwise = do
        -- Remember mismatches we have seen before and reuse the
        -- same new size.
        maybe_d <- gets $ M.lookup (d1, d2)
        case maybe_d of
          Just d -> return $ NamedDim $ qualName d
          Nothing -> do
            d <- lift $ newDimVar loc r "differ"
            modify $ M.insert (d1, d2) d
            return $ NamedDim $ qualName d

-- | Like unification, but creates new size variables where mismatches
-- occur.  Returns the new dimensions thus created.
unifyMostCommon ::
  MonadUnify m =>
  Usage ->
  PatternType ->
  PatternType ->
  m (PatternType, [VName])
unifyMostCommon usage t1 t2 = do
  -- We are ignoring the dimensions here, because any mismatches
  -- should be turned into fresh size variables.
  let allOK _ _ _ _ _ = return ()
  unifyWith allOK usage noBreadCrumbs (toStruct t1) (toStruct t2)
  t1' <- normTypeFully t1
  t2' <- normTypeFully t2
  newDimOnMismatch (srclocOf usage) t1' t2'

-- Simple MonadUnify implementation.

type UnifyMState = (Constraints, Int)

newtype UnifyM a = UnifyM (StateT UnifyMState (Except TypeError) a)
  deriving
    ( Monad,
      Functor,
      Applicative,
      MonadState UnifyMState,
      MonadError TypeError
    )

newVar :: String -> UnifyM VName
newVar name = do
  (x, i) <- get
  put (x, i + 1)
  return $ VName (mkTypeVarName name i) i

instance MonadUnify UnifyM where
  getConstraints = gets fst
  putConstraints x = modify $ \(_, i) -> (x, i)

  newTypeVar loc name = do
    v <- newVar name
    modifyConstraints $ M.insert v (0, NoConstraint Lifted $ Usage Nothing loc)
    return $ Scalar $ TypeVar mempty Nonunique (typeName v) []

  newDimVar loc rigidity name = do
    dim <- newVar name
    case rigidity of
      Rigid src -> modifyConstraints $ M.insert dim (0, UnknowableSize loc src)
      Nonrigid -> modifyConstraints $ M.insert dim (0, Size Nothing $ Usage Nothing loc)
    return dim

  curLevel = pure 0

  unifyError loc notes bcs doc =
    throwError $ TypeError (srclocOf loc) notes $ doc <> ppr bcs

  matchError loc notes bcs t1 t2 =
    throwError $ TypeError (srclocOf loc) notes $ doc <> ppr bcs
    where
      doc =
        "Types"
          </> indent 2 (ppr t1)
          </> "and"
          </> indent 2 (ppr t2)
          </> "do not match."

-- | Construct the name of a new type variable given a base
-- description and a tag number (note that this is distinct from
-- actually constructing a VName; the tag here is intended for human
-- consumption but the machine does not care).
mkTypeVarName :: String -> Int -> Name
mkTypeVarName desc i =
  nameFromString $ desc ++ mapMaybe subscript (show i)
  where
    subscript = flip lookup $ zip "0123456789" "₀₁₂₃₄₅₆₇₈₉"

runUnifyM :: [TypeParam] -> UnifyM a -> Either TypeError a
runUnifyM tparams (UnifyM m) = runExcept $ evalStateT m (constraints, 0)
  where
    constraints = M.fromList $ map f tparams
    f (TypeParamDim p loc) = (p, (0, Size Nothing $ Usage Nothing loc))
    f (TypeParamType l p loc) = (p, (0, NoConstraint l $ Usage Nothing loc))

-- | Perform a unification of two types outside a monadic context.
-- The type parameters are allowed to be instantiated; all other types
-- are considered rigid.
doUnification ::
  SrcLoc ->
  [TypeParam] ->
  StructType ->
  StructType ->
  Either TypeError StructType
doUnification loc tparams t1 t2 = runUnifyM tparams $ do
  expect (Usage Nothing loc) t1 t2
  normTypeFully t2
