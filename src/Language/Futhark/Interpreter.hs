{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

-- | An interpreter operating on type-checked source Futhark terms.
-- Relatively slow.
module Language.Futhark.Interpreter
  ( Ctx (..),
    Env,
    InterpreterError,
    initialCtx,
    interpretExp,
    interpretDec,
    interpretImport,
    interpretFunction,
    ExtOp (..),
    BreakReason (..),
    StackFrame (..),
    typeCheckerEnv,
    Value (ValuePrim, ValueArray, ValueRecord),
    fromTuple,
    isEmptyArray,
    prettyEmptyArray,
  )
where

import Control.Monad.Except
import Control.Monad.Free.Church
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Array
import Data.Bifunctor (first, second)
import Data.List
  ( find,
    foldl',
    genericLength,
    intercalate,
    isPrefixOf,
    transpose,
  )
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid hiding (Sum)
import Futhark.IR.Primitive (floatValue, intValue)
import qualified Futhark.IR.Primitive as P
import Futhark.Util (chunk, maybeHead, splitFromEnd)
import Futhark.Util.Loc
import Futhark.Util.Pretty hiding (apply, bool)
import Language.Futhark hiding (Value, matchDims)
import qualified Language.Futhark as F
import qualified Language.Futhark.Semantic as T
import Prelude hiding (break, mod)

data StackFrame = StackFrame
  { stackFrameLoc :: Loc,
    stackFrameCtx :: Ctx
  }

instance Located StackFrame where
  locOf = stackFrameLoc

-- | What is the reason for this break point?
data BreakReason
  = -- | An explicit breakpoint in the program.
    BreakPoint
  | -- | A
    BreakNaN

data ExtOp a
  = ExtOpTrace Loc String a
  | ExtOpBreak BreakReason (NE.NonEmpty StackFrame) a
  | ExtOpError InterpreterError

instance Functor ExtOp where
  fmap f (ExtOpTrace w s x) = ExtOpTrace w s $ f x
  fmap f (ExtOpBreak why backtrace x) = ExtOpBreak why backtrace $ f x
  fmap _ (ExtOpError err) = ExtOpError err

type Stack = [StackFrame]

type Sizes = M.Map VName Int64

-- | The monad in which evaluation takes place.
newtype EvalM a
  = EvalM
      ( ReaderT
          (Stack, M.Map FilePath Env)
          (StateT Sizes (F ExtOp))
          a
      )
  deriving
    ( Monad,
      Applicative,
      Functor,
      MonadFree ExtOp,
      MonadReader (Stack, M.Map FilePath Env),
      MonadState Sizes
    )

runEvalM :: M.Map FilePath Env -> EvalM a -> F ExtOp a
runEvalM imports (EvalM m) = evalStateT (runReaderT m (mempty, imports)) mempty

stacking :: SrcLoc -> Env -> EvalM a -> EvalM a
stacking loc env = local $ \(ss, imports) ->
  if isNoLoc loc
    then (ss, imports)
    else
      let s = StackFrame (locOf loc) (Ctx env imports)
       in (s : ss, imports)
  where
    isNoLoc :: SrcLoc -> Bool
    isNoLoc = (== NoLoc) . locOf

stacktrace :: EvalM [Loc]
stacktrace = asks $ map stackFrameLoc . fst

lookupImport :: FilePath -> EvalM (Maybe Env)
lookupImport f = asks $ M.lookup f . snd

putExtSize :: VName -> Int64 -> EvalM ()
putExtSize v x = modify $ M.insert v x

getSizes :: EvalM Sizes
getSizes = get

extSizeEnv :: EvalM Env
extSizeEnv = i64Env <$> getSizes

prettyRecord :: Pretty a => M.Map Name a -> Doc
prettyRecord m
  | Just vs <- areTupleFields m =
    parens $ commasep $ map ppr vs
  | otherwise =
    braces $ commasep $ map field $ M.toList m
  where
    field (k, v) = ppr k <+> equals <+> ppr v

valueStructType :: ValueType -> StructType
valueStructType = first (ConstDim . fromIntegral)

-- | A shape is a tree to accomodate the case of records.  It is
-- parameterised over the representation of dimensions.
data Shape d
  = ShapeDim d (Shape d)
  | ShapeLeaf
  | ShapeRecord (M.Map Name (Shape d))
  | ShapeSum (M.Map Name [Shape d])
  deriving (Eq, Show, Functor, Foldable, Traversable)

type ValueShape = Shape Int64

instance Pretty d => Pretty (Shape d) where
  ppr ShapeLeaf = mempty
  ppr (ShapeDim d s) = brackets (ppr d) <> ppr s
  ppr (ShapeRecord m) = prettyRecord m
  ppr (ShapeSum cs) =
    mconcat (punctuate (text " | ") cs')
    where
      ppConstr (name, fs) = sep $ (text "#" <> ppr name) : map ppr fs
      cs' = map ppConstr $ M.toList cs

emptyShape :: ValueShape -> Bool
emptyShape (ShapeDim d s) = d == 0 || emptyShape s
emptyShape _ = False

typeShape :: M.Map VName (Shape d) -> TypeBase d () -> Shape d
typeShape shapes = go
  where
    go (Array _ _ et shape) =
      foldr ShapeDim (go (Scalar et)) $ shapeDims shape
    go (Scalar (Record fs)) =
      ShapeRecord $ M.map go fs
    go (Scalar (Sum cs)) =
      ShapeSum $ M.map (map go) cs
    go (Scalar (TypeVar _ _ (TypeName [] v) []))
      | Just shape <- M.lookup v shapes =
        shape
    go _ =
      ShapeLeaf

structTypeShape :: M.Map VName ValueShape -> StructType -> Shape (Maybe Int64)
structTypeShape shapes = fmap dim . typeShape shapes'
  where
    dim (ConstDim d) = Just $ fromIntegral d
    dim _ = Nothing
    shapes' = M.map (fmap $ ConstDim . fromIntegral) shapes

resolveTypeParams :: [VName] -> StructType -> StructType -> Env
resolveTypeParams names = match
  where
    match (Scalar (TypeVar _ _ tn _)) t
      | typeLeaf tn `elem` names =
        typeEnv $ M.singleton (typeLeaf tn) t
    match (Scalar (Record poly_fields)) (Scalar (Record fields)) =
      mconcat $
        M.elems $
          M.intersectionWith match poly_fields fields
    match (Scalar (Sum poly_fields)) (Scalar (Sum fields)) =
      mconcat $
        map mconcat $
          M.elems $
            M.intersectionWith (zipWith match) poly_fields fields
    match
      (Scalar (Arrow _ _ poly_t1 (RetType _ poly_t2)))
      (Scalar (Arrow _ _ t1 (RetType _ t2))) =
        match poly_t1 t1 <> match poly_t2 t2
    match poly_t t
      | d1 : _ <- shapeDims (arrayShape poly_t),
        d2 : _ <- shapeDims (arrayShape t) =
        matchDims d1 d2 <> match (stripArray 1 poly_t) (stripArray 1 t)
    match _ _ = mempty

    matchDims (NamedDim (QualName _ d1)) (ConstDim d2)
      | d1 `elem` names =
        i64Env $ M.singleton d1 $ fromIntegral d2
    matchDims _ _ = mempty

resolveExistentials :: [VName] -> StructType -> ValueShape -> M.Map VName Int64
resolveExistentials names = match
  where
    match (Scalar (Record poly_fields)) (ShapeRecord fields) =
      mconcat $
        M.elems $
          M.intersectionWith match poly_fields fields
    match (Scalar (Sum poly_fields)) (ShapeSum fields) =
      mconcat $
        map mconcat $
          M.elems $
            M.intersectionWith (zipWith match) poly_fields fields
    match poly_t (ShapeDim d2 rowshape)
      | d1 : _ <- shapeDims (arrayShape poly_t) =
        matchDims d1 d2 <> match (stripArray 1 poly_t) rowshape
    match _ _ = mempty

    matchDims (NamedDim (QualName _ d1)) d2
      | d1 `elem` names = M.singleton d1 d2
    matchDims _ _ = mempty

-- | A fully evaluated Futhark value.
data Value
  = ValuePrim !PrimValue
  | ValueArray ValueShape !(Array Int Value)
  | -- Stores the full shape.
    ValueRecord (M.Map Name Value)
  | ValueFun (Value -> EvalM Value)
  | -- Stores the full shape.
    ValueSum ValueShape Name [Value]
  | -- The update function and the array.
    ValueAcc (Value -> Value -> EvalM Value) !(Array Int Value)

instance Eq Value where
  ValuePrim (SignedValue x) == ValuePrim (SignedValue y) =
    P.doCmpEq (P.IntValue x) (P.IntValue y)
  ValuePrim (UnsignedValue x) == ValuePrim (UnsignedValue y) =
    P.doCmpEq (P.IntValue x) (P.IntValue y)
  ValuePrim (FloatValue x) == ValuePrim (FloatValue y) =
    P.doCmpEq (P.FloatValue x) (P.FloatValue y)
  ValuePrim (BoolValue x) == ValuePrim (BoolValue y) =
    P.doCmpEq (P.BoolValue x) (P.BoolValue y)
  ValueArray _ x == ValueArray _ y = x == y
  ValueRecord x == ValueRecord y = x == y
  ValueSum _ n1 vs1 == ValueSum _ n2 vs2 = n1 == n2 && vs1 == vs2
  ValueAcc _ x == ValueAcc _ y = x == y
  _ == _ = False

instance Pretty Value where
  ppr = pprPrec 0
  pprPrec _ (ValuePrim v) = ppr v
  pprPrec _ (ValueArray _ a) =
    let elements = elems a -- [Value]
        (x : _) = elements
        separator = case x of
          ValueArray _ _ -> comma <> line
          _ -> comma <> space
     in brackets $ cat $ punctuate separator (map ppr elements)
  pprPrec _ (ValueRecord m) = prettyRecord m
  pprPrec _ ValueFun {} = text "#<fun>"
  pprPrec _ ValueAcc {} = text "#<acc>"
  pprPrec p (ValueSum _ n vs) =
    parensIf (p > 0) $ text "#" <> sep (ppr n : map (pprPrec 1) vs)

valueShape :: Value -> ValueShape
valueShape (ValueArray shape _) = shape
valueShape (ValueRecord fs) = ShapeRecord $ M.map valueShape fs
valueShape (ValueSum shape _ _) = shape
valueShape _ = ShapeLeaf

checkShape :: Shape (Maybe Int64) -> ValueShape -> Maybe ValueShape
checkShape (ShapeDim Nothing shape1) (ShapeDim d2 shape2) =
  ShapeDim d2 <$> checkShape shape1 shape2
checkShape (ShapeDim (Just d1) shape1) (ShapeDim d2 shape2) = do
  guard $ d1 == d2
  ShapeDim d2 <$> checkShape shape1 shape2
checkShape (ShapeDim d1 shape1) ShapeLeaf =
  -- This case is for handling polymorphism, when a function doesn't
  -- know that the array it produced actually has more dimensions.
  ShapeDim (fromMaybe 0 d1) <$> checkShape shape1 ShapeLeaf
checkShape (ShapeRecord shapes1) (ShapeRecord shapes2) =
  ShapeRecord <$> sequence (M.intersectionWith checkShape shapes1 shapes2)
checkShape (ShapeRecord shapes1) ShapeLeaf =
  Just $ fromMaybe 0 <$> ShapeRecord shapes1
checkShape (ShapeSum shapes1) (ShapeSum shapes2) =
  ShapeSum <$> sequence (M.intersectionWith (zipWithM checkShape) shapes1 shapes2)
checkShape (ShapeSum shapes1) ShapeLeaf =
  Just $ fromMaybe 0 <$> ShapeSum shapes1
checkShape _ shape2 =
  Just shape2

-- | Does the value correspond to an empty array?
isEmptyArray :: Value -> Bool
isEmptyArray = emptyShape . valueShape

-- | String representation of an empty array with the provided element
-- type.  This is pretty ad-hoc - don't expect good results unless the
-- element type is a primitive.
prettyEmptyArray :: TypeBase () () -> Value -> String
prettyEmptyArray t v =
  "empty(" ++ dims (valueShape v) ++ pretty t' ++ ")"
  where
    t' = stripArray (arrayRank t) t
    dims (ShapeDim n rowshape) =
      "[" ++ pretty n ++ "]" ++ dims rowshape
    dims _ = ""

-- | Create an array value; failing if that would result in an
-- irregular array.
mkArray :: TypeBase Int64 () -> [Value] -> Maybe Value
mkArray t [] =
  return $ toArray (typeShape mempty t) []
mkArray _ (v : vs) = do
  let v_shape = valueShape v
  guard $ all ((== v_shape) . valueShape) vs
  return $ toArray' v_shape $ v : vs

arrayLength :: Integral int => Array Int Value -> int
arrayLength = fromIntegral . (+ 1) . snd . bounds

toTuple :: [Value] -> Value
toTuple = ValueRecord . M.fromList . zip tupleFieldNames

fromTuple :: Value -> Maybe [Value]
fromTuple (ValueRecord m) = areTupleFields m
fromTuple _ = Nothing

asInteger :: Value -> Integer
asInteger (ValuePrim (SignedValue v)) = P.valueIntegral v
asInteger (ValuePrim (UnsignedValue v)) =
  toInteger (P.valueIntegral (P.doZExt v Int64) :: Word64)
asInteger v = error $ "Unexpectedly not an integer: " ++ pretty v

asInt :: Value -> Int
asInt = fromIntegral . asInteger

asSigned :: Value -> IntValue
asSigned (ValuePrim (SignedValue v)) = v
asSigned v = error $ "Unexpected not a signed integer: " ++ pretty v

asInt64 :: Value -> Int64
asInt64 = fromIntegral . asInteger

asBool :: Value -> Bool
asBool (ValuePrim (BoolValue x)) = x
asBool v = error $ "Unexpectedly not a boolean: " ++ pretty v

lookupInEnv ::
  (Env -> M.Map VName x) ->
  QualName VName ->
  Env ->
  Maybe x
lookupInEnv onEnv qv env = f env $ qualQuals qv
  where
    f m (q : qs) =
      case M.lookup q $ envTerm m of
        Just (TermModule (Module mod)) -> f mod qs
        _ -> Nothing
    f m [] = M.lookup (qualLeaf qv) $ onEnv m

lookupVar :: QualName VName -> Env -> Maybe TermBinding
lookupVar = lookupInEnv envTerm

lookupType :: QualName VName -> Env -> Maybe T.TypeBinding
lookupType = lookupInEnv envType

-- | A TermValue with a 'Nothing' type annotation is an intrinsic.
data TermBinding
  = TermValue (Maybe T.BoundV) Value
  | -- | A polymorphic value that must be instantiated.
    TermPoly (Maybe T.BoundV) (StructType -> EvalM Value)
  | TermModule Module

data Module
  = Module Env
  | ModuleFun (Module -> EvalM Module)

-- | The actual type- and value environment.
data Env = Env
  { envTerm :: M.Map VName TermBinding,
    envType :: M.Map VName T.TypeBinding,
    -- | A mapping from type parameters to the shapes of
    -- the value to which they were initially bound.
    envShapes :: M.Map VName ValueShape
  }

instance Monoid Env where
  mempty = Env mempty mempty mempty

instance Semigroup Env where
  Env vm1 tm1 sm1 <> Env vm2 tm2 sm2 =
    Env (vm1 <> vm2) (tm1 <> tm2) (sm1 <> sm2)

-- | An error occurred during interpretation due to an error in the
-- user program.  Actual interpreter errors will be signaled with an
-- IO exception ('error').
newtype InterpreterError = InterpreterError String

valEnv :: M.Map VName (Maybe T.BoundV, Value) -> Env
valEnv m =
  Env
    { envTerm = M.map (uncurry TermValue) m,
      envType = mempty,
      envShapes = mempty
    }

modEnv :: M.Map VName Module -> Env
modEnv m =
  Env
    { envTerm = M.map TermModule m,
      envType = mempty,
      envShapes = mempty
    }

typeEnv :: M.Map VName StructType -> Env
typeEnv m =
  Env
    { envTerm = mempty,
      envType = M.map tbind m,
      envShapes = mempty
    }
  where
    tbind = T.TypeAbbr Unlifted [] . RetType []

i64Env :: M.Map VName Int64 -> Env
i64Env = valEnv . M.map f
  where
    f x =
      ( Just $ T.BoundV [] $ Scalar $ Prim $ Signed Int64,
        ValuePrim $ SignedValue $ Int64Value x
      )

instance Show InterpreterError where
  show (InterpreterError s) = s

bad :: SrcLoc -> Env -> String -> EvalM a
bad loc env s = stacking loc env $ do
  ss <- map (locStr . srclocOf) <$> stacktrace
  liftF $ ExtOpError $ InterpreterError $ "Error at\n" ++ prettyStacktrace 0 ss ++ s

trace :: Value -> EvalM ()
trace v = do
  -- We take the second-to-top element of the stack, because any
  -- actual call to 'implicits.trace' is going to be in the trace
  -- function in the prelude, which is not interesting.
  top <- fromMaybe noLoc . maybeHead . drop 1 <$> stacktrace
  liftF $ ExtOpTrace top (prettyOneLine v) ()

typeCheckerEnv :: Env -> T.Env
typeCheckerEnv env =
  -- FIXME: some shadowing issues are probably not right here.
  let valMap (TermValue (Just t) _) = Just t
      valMap _ = Nothing
      vtable = M.mapMaybe valMap $ envTerm env
      nameMap k
        | k `M.member` vtable = Just ((T.Term, baseName k), qualName k)
        | otherwise = Nothing
   in mempty
        { T.envNameMap = M.fromList $ mapMaybe nameMap $ M.keys $ envTerm env,
          T.envVtable = vtable
        }

break :: EvalM ()
break = do
  -- We don't want the env of the function that is calling
  -- intrinsics.break, since that is just going to be the boring
  -- wrapper function (intrinsics are never called directly).
  -- This is why we go a step up the stack.
  backtrace <- asks $ drop 1 . fst
  case NE.nonEmpty backtrace of
    Nothing -> return ()
    Just backtrace' -> liftF $ ExtOpBreak BreakPoint backtrace' ()

fromArray :: Value -> (ValueShape, [Value])
fromArray (ValueArray shape as) = (shape, elems as)
fromArray v = error $ "Expected array value, but found: " ++ pretty v

toArray :: ValueShape -> [Value] -> Value
toArray shape vs = ValueArray shape (listArray (0, length vs - 1) vs)

toArray' :: ValueShape -> [Value] -> Value
toArray' rowshape vs = ValueArray shape (listArray (0, length vs - 1) vs)
  where
    shape = ShapeDim (genericLength vs) rowshape

apply :: SrcLoc -> Env -> Value -> Value -> EvalM Value
apply loc env (ValueFun f) v = stacking loc env (f v)
apply _ _ f _ = error $ "Cannot apply non-function: " ++ pretty f

apply2 :: SrcLoc -> Env -> Value -> Value -> Value -> EvalM Value
apply2 loc env f x y = stacking loc env $ do
  f' <- apply noLoc mempty f x
  apply noLoc mempty f' y

matchPattern :: Env -> Pattern -> Value -> EvalM Env
matchPattern env p v = do
  m <- runMaybeT $ patternMatch env p v
  case m of
    Nothing -> error $ "matchPattern: missing case for " ++ pretty p ++ " and " ++ pretty v
    Just env' -> return env'

patternMatch :: Env -> Pattern -> Value -> MaybeT EvalM Env
patternMatch env (Id v (Info t) _) val =
  lift $
    pure $
      valEnv (M.singleton v (Just $ T.BoundV [] $ toStruct t, val)) <> env
patternMatch env Wildcard {} _ =
  lift $ pure env
patternMatch env (TuplePattern ps _) (ValueRecord vs) =
  foldM (\env' (p, v) -> patternMatch env' p v) env $
    zip ps (map snd $ sortFields vs)
patternMatch env (RecordPattern ps _) (ValueRecord vs) =
  foldM (\env' (p, v) -> patternMatch env' p v) env $
    M.intersectionWith (,) (M.fromList ps) vs
patternMatch env (PatternParens p _) v = patternMatch env p v
patternMatch env (PatternAscription p _ _) v =
  patternMatch env p v
patternMatch env (PatternLit l t _) v = do
  l' <- case l of
    PatLitInt x -> lift $ eval env $ IntLit x t mempty
    PatLitFloat x -> lift $ eval env $ FloatLit x t mempty
    PatLitPrim lv -> pure $ ValuePrim lv
  if v == l'
    then pure env
    else mzero
patternMatch env (PatternConstr n _ ps _) (ValueSum _ n' vs)
  | n == n' =
    foldM (\env' (p, v) -> patternMatch env' p v) env $ zip ps vs
patternMatch _ _ _ = mzero

data Indexing
  = IndexingFix Int64
  | IndexingSlice (Maybe Int64) (Maybe Int64) (Maybe Int64)

instance Pretty Indexing where
  ppr (IndexingFix i) = ppr i
  ppr (IndexingSlice i j (Just s)) =
    maybe mempty ppr i <> text ":"
      <> maybe mempty ppr j
      <> text ":"
      <> ppr s
  ppr (IndexingSlice i (Just j) s) =
    maybe mempty ppr i <> text ":"
      <> ppr j
      <> maybe mempty ((text ":" <>) . ppr) s
  ppr (IndexingSlice i Nothing Nothing) =
    maybe mempty ppr i <> text ":"

indexesFor ::
  Maybe Int64 ->
  Maybe Int64 ->
  Maybe Int64 ->
  Int64 ->
  Maybe [Int]
indexesFor start end stride n
  | (start', end', stride') <- slice,
    end' == start' || signum' (end' - start') == signum' stride',
    stride' /= 0,
    is <- [start', start' + stride' .. end' - signum stride'],
    all inBounds is =
    Just $ map fromIntegral is
  | otherwise =
    Nothing
  where
    inBounds i = i >= 0 && i < n

    slice =
      case (start, end, stride) of
        (Just start', _, _) ->
          let end' = fromMaybe n end
           in (start', end', fromMaybe 1 stride)
        (Nothing, Just end', _) ->
          let start' = 0
           in (start', end', fromMaybe 1 stride)
        (Nothing, Nothing, Just stride') ->
          ( if stride' > 0 then 0 else n -1,
            if stride' > 0 then n else -1,
            stride'
          )
        (Nothing, Nothing, Nothing) ->
          (0, n, 1)

-- | 'signum', but with 0 as 1.
signum' :: (Eq p, Num p) => p -> p
signum' 0 = 1
signum' x = signum x

indexShape :: [Indexing] -> ValueShape -> ValueShape
indexShape (IndexingFix {} : is) (ShapeDim _ shape) =
  indexShape is shape
indexShape (IndexingSlice start end stride : is) (ShapeDim d shape) =
  ShapeDim n $ indexShape is shape
  where
    n = maybe 0 genericLength $ indexesFor start end stride d
indexShape _ shape =
  shape

indexArray :: [Indexing] -> Value -> Maybe Value
indexArray (IndexingFix i : is) (ValueArray _ arr)
  | i >= 0,
    i < n =
    indexArray is $ arr ! fromIntegral i
  | otherwise =
    Nothing
  where
    n = arrayLength arr
indexArray (IndexingSlice start end stride : is) (ValueArray (ShapeDim _ rowshape) arr) = do
  js <- indexesFor start end stride $ arrayLength arr
  toArray' (indexShape is rowshape) <$> mapM (indexArray is . (arr !)) js
indexArray _ v = Just v

updateArray :: [Indexing] -> Value -> Value -> Maybe Value
updateArray (IndexingFix i : is) (ValueArray shape arr) v
  | i >= 0,
    i < n = do
    v' <- updateArray is (arr ! i') v
    Just $ ValueArray shape $ arr // [(i', v')]
  | otherwise =
    Nothing
  where
    n = arrayLength arr
    i' = fromIntegral i
updateArray (IndexingSlice start end stride : is) (ValueArray shape arr) (ValueArray _ v) = do
  arr_is <- indexesFor start end stride $ arrayLength arr
  guard $ length arr_is == arrayLength v
  let update arr' (i, v') = do
        x <- updateArray is (arr ! i) v'
        return $ arr' // [(i, x)]
  fmap (ValueArray shape) $ foldM update arr $ zip arr_is $ elems v
updateArray _ _ v = Just v

evalDimIndex :: Env -> DimIndex -> EvalM Indexing
evalDimIndex env (DimFix x) =
  IndexingFix . asInt64 <$> eval env x
evalDimIndex env (DimSlice start end stride) =
  IndexingSlice <$> traverse (fmap asInt64 . eval env) start
    <*> traverse (fmap asInt64 . eval env) end
    <*> traverse (fmap asInt64 . eval env) stride

evalIndex :: SrcLoc -> Env -> [Indexing] -> Value -> EvalM Value
evalIndex loc env is arr = do
  let oob =
        bad loc env $
          "Index [" <> intercalate ", " (map pretty is)
            <> "] out of bounds for array of shape "
            <> pretty (valueShape arr)
            <> "."
  maybe oob return $ indexArray is arr

-- | Expand type based on information that was not available at
-- type-checking time (the structure of abstract types).
evalType :: Env -> StructType -> StructType
evalType _ (Scalar (Prim pt)) = Scalar $ Prim pt
evalType env (Scalar (Record fs)) = Scalar $ Record $ fmap (evalType env) fs
evalType env (Scalar (Arrow () p t1 (RetType dims t2))) =
  Scalar $ Arrow () p (evalType env t1) (RetType dims (evalType env t2))
evalType env t@(Array _ u _ shape) =
  let et = stripArray (shapeRank shape) t
      et' = evalType env et
      shape' = fmap evalDim shape
   in arrayOf et' shape' u
  where
    evalDim (NamedDim qn)
      | Just (TermValue _ (ValuePrim (SignedValue (Int64Value x)))) <-
          lookupVar qn env =
        ConstDim $ fromIntegral x
    evalDim d = d
evalType env t@(Scalar (TypeVar () _ tn args)) =
  case lookupType (qualNameFromTypeName tn) env of
    Just (T.TypeAbbr _ ps (RetType _ t')) ->
      let (substs, types) = mconcat $ zipWith matchPtoA ps args
          onDim (NamedDim v) = fromMaybe (NamedDim v) $ M.lookup (qualLeaf v) substs
          onDim d = d
       in if null ps
            then first onDim t'
            else evalType (Env mempty types mempty <> env) $ first onDim t'
    Nothing -> t
  where
    matchPtoA (TypeParamDim p _) (TypeArgDim (NamedDim qv) _) =
      (M.singleton p $ NamedDim qv, mempty)
    matchPtoA (TypeParamDim p _) (TypeArgDim (ConstDim k) _) =
      (M.singleton p $ ConstDim k, mempty)
    matchPtoA (TypeParamType l p _) (TypeArgType t' _) =
      let t'' = evalType env t'
       in (mempty, M.singleton p $ T.TypeAbbr l [] $ RetType [] t'')
    matchPtoA _ _ = mempty
evalType env (Scalar (Sum cs)) = Scalar $ Sum $ (fmap . fmap) (evalType env) cs

evalTermVar :: Env -> QualName VName -> StructType -> EvalM Value
evalTermVar env qv t =
  case lookupVar qv env of
    Just (TermPoly _ v) -> do
      size_env <- extSizeEnv
      v $ evalType (size_env <> env) t
    Just (TermValue _ v) -> return v
    _ -> error $ "`" <> pretty qv <> "` is not bound to a value."

typeValueShape :: Env -> StructType -> EvalM ValueShape
typeValueShape env t = do
  size_env <- extSizeEnv
  let t' = evalType (size_env <> env) t
  case traverse dim $ typeShape mempty t' of
    Nothing -> error $ "typeValueShape: failed to fully evaluate type " ++ pretty t'
    Just shape -> return shape
  where
    dim (ConstDim x) = Just $ fromIntegral x
    dim _ = Nothing

evalFunction :: Env -> [VName] -> [Pattern] -> Exp -> StructType -> EvalM Value
-- We treat zero-parameter lambdas as simply an expression to
-- evaluate immediately.  Note that this is *not* the same as a lambda
-- that takes an empty tuple '()' as argument!  Zero-parameter lambdas
-- can never occur in a well-formed Futhark program, but they are
-- convenient in the interpreter.
evalFunction env _ [] body rettype =
  -- Eta-expand the rest to make any sizes visible.
  etaExpand [] env rettype
  where
    etaExpand vs env' (Scalar (Arrow _ _ pt (RetType _ rt))) =
      return $
        ValueFun $ \v -> do
          env'' <- matchPattern env' (Wildcard (Info $ fromStruct pt) noLoc) v
          etaExpand (v : vs) env'' rt
    etaExpand vs env' _ = do
      f <- eval env' body
      foldM (apply noLoc mempty) f $ reverse vs
evalFunction env missing_sizes (p : ps) body rettype =
  return $
    ValueFun $ \v -> do
      env' <- matchPattern env p v
      -- Fix up the last sizes, if any.
      let p_t = evalType env $ patternStructType p
          env''
            | null missing_sizes = env'
            | otherwise =
              env' <> i64Env (resolveExistentials missing_sizes p_t (valueShape v))
      evalFunction env'' missing_sizes ps body rettype

evalFunctionBinding ::
  Env ->
  [TypeParam] ->
  [Pattern] ->
  StructType ->
  [VName] ->
  Exp ->
  EvalM TermBinding
evalFunctionBinding env tparams ps ret retext fbody = do
  let ret' = evalType env ret
      arrow (xp, xt) yt = Scalar $ Arrow () xp xt $ RetType [] yt
      ftype = foldr (arrow . patternParam) ret' ps

  -- Distinguish polymorphic and non-polymorphic bindings here.
  if null tparams
    then
      TermValue (Just $ T.BoundV [] ftype)
        <$> (returned env ret retext =<< evalFunction env [] ps fbody ret')
    else return $
      TermPoly (Just $ T.BoundV [] ftype) $ \ftype' -> do
        let tparam_names = map typeParamName tparams
            env' = resolveTypeParams tparam_names ftype ftype' <> env

            -- In some cases (abstract lifted types) there may be
            -- missing sizes that were not fixed by the type
            -- instantiation.  These will have to be set by looking
            -- at the actual function arguments.
            missing_sizes =
              filter (`M.notMember` envTerm env') $
                map typeParamName (filter isSizeParam tparams)
        returned env ret retext =<< evalFunction env' missing_sizes ps fbody ret'

evalArg :: Env -> Exp -> Maybe VName -> EvalM Value
evalArg env e ext = do
  v <- eval env e
  case ext of
    Just ext' -> putExtSize ext' $ asInt64 v
    Nothing -> return ()
  return v

returned :: Env -> TypeBase (DimDecl VName) als -> [VName] -> Value -> EvalM Value
returned _ _ [] v = return v
returned env ret retext v = do
  mapM_ (uncurry putExtSize) $
    M.toList $
      resolveExistentials retext (evalType env $ toStruct ret) $ valueShape v
  return v

evalAppExp :: Env -> AppExp -> EvalM Value
evalAppExp env (Range start maybe_second end loc) = do
  start' <- asInteger <$> eval env start
  maybe_second' <- traverse (fmap asInteger . eval env) maybe_second
  end' <- traverse (fmap asInteger . eval env) end

  let (end_adj, step, ok) =
        case (end', maybe_second') of
          (DownToExclusive end'', Nothing) ->
            (end'' + 1, -1, start' >= end'')
          (DownToExclusive end'', Just second') ->
            (end'' + 1, second' - start', start' >= end'' && second' < start')
          (ToInclusive end'', Nothing) ->
            (end'', 1, start' <= end'')
          (ToInclusive end'', Just second')
            | second' > start' ->
              (end'', second' - start', start' <= end'')
            | otherwise ->
              (end'', second' - start', start' >= end'' && second' /= start')
          (UpToExclusive x, Nothing) ->
            (x -1, 1, start' <= x)
          (UpToExclusive x, Just second') ->
            (x -1, second' - start', start' <= x && second' > start')

  if ok
    then pure $ toArray' ShapeLeaf $ map toInt [start', start' + step .. end_adj]
    else bad loc env $ badRange start' maybe_second' end'
  where
    toInt =
      case typeOf start of
        Scalar (Prim (Signed t')) ->
          ValuePrim . SignedValue . intValue t'
        Scalar (Prim (Unsigned t')) ->
          ValuePrim . UnsignedValue . intValue t'
        t -> error $ "Nonsensical range type: " ++ show t

    badRange start' maybe_second' end' =
      "Range " ++ pretty start'
        ++ ( case maybe_second' of
               Nothing -> ""
               Just second' -> ".." ++ pretty second'
           )
        ++ ( case end' of
               DownToExclusive x -> "..>" ++ pretty x
               ToInclusive x -> "..." ++ pretty x
               UpToExclusive x -> "..<" ++ pretty x
           )
        ++ " is invalid."
evalAppExp env (Coerce e td loc) = do
  v <- eval env e
  let t = evalType env $ unInfo $ expandedType td
  case checkShape (structTypeShape (envShapes env) t) (valueShape v) of
    Just _ -> return v
    Nothing ->
      bad loc env $
        "Value `" <> pretty v <> "` of shape `" ++ pretty (valueShape v)
          ++ "` cannot match shape of type `"
          <> pretty (declaredType td)
          <> "` (`"
          <> pretty t
          <> "`)"
evalAppExp env (LetPat sizes p e body _) = do
  v <- eval env e
  env' <- matchPattern env p v
  let p_t = evalType env $ patternStructType p
      v_s = valueShape v
      env'' = env' <> i64Env (resolveExistentials (map sizeName sizes) p_t v_s)
  eval env'' body
evalAppExp env (LetFun f (tparams, ps, _, Info (RetType _ ret), fbody) body _) = do
  binding <- evalFunctionBinding env tparams ps ret [] fbody
  eval (env {envTerm = M.insert f binding $ envTerm env}) body
evalAppExp
  env
  (BinOp (op, _) op_t (x, Info (_, xext)) (y, Info (_, yext)) loc)
    | baseString (qualLeaf op) == "&&" = do
      x' <- asBool <$> eval env x
      if x'
        then eval env y
        else return $ ValuePrim $ BoolValue False
    | baseString (qualLeaf op) == "||" = do
      x' <- asBool <$> eval env x
      if x'
        then return $ ValuePrim $ BoolValue True
        else eval env y
    | otherwise = do
      op' <- eval env $ Var op op_t loc
      x' <- evalArg env x xext
      y' <- evalArg env y yext
      apply2 loc env op' x' y'
evalAppExp env (If cond e1 e2 _) = do
  cond' <- asBool <$> eval env cond
  if cond' then eval env e1 else eval env e2
evalAppExp env (Apply f x (Info (_, ext)) loc) = do
  -- It is important that 'x' is evaluated first in order to bring any
  -- sizes into scope that may be used in the type of 'f'.
  x' <- evalArg env x ext
  f' <- eval env f
  apply loc env f' x'
evalAppExp env (Index e is loc) = do
  is' <- mapM (evalDimIndex env) is
  arr <- eval env e
  evalIndex loc env is' arr
evalAppExp env (LetWith dest src is v body loc) = do
  let Ident src_vn (Info src_t) _ = src
  dest' <-
    maybe oob return
      =<< updateArray <$> mapM (evalDimIndex env) is
      <*> evalTermVar env (qualName src_vn) (toStruct src_t)
      <*> eval env v
  let t = T.BoundV [] $ toStruct $ unInfo $ identType dest
  eval (valEnv (M.singleton (identName dest) (Just t, dest')) <> env) body
  where
    oob = bad loc env "Bad update"
evalAppExp env (DoLoop sparams pat init_e form body _) = do
  init_v <- eval env init_e
  case form of
    For iv bound -> do
      bound' <- asSigned <$> eval env bound
      forLoop (identName iv) bound' (zero bound') init_v
    ForIn in_pat in_e -> do
      (_, in_vs) <- fromArray <$> eval env in_e
      foldM (forInLoop in_pat) init_v in_vs
    While cond ->
      whileLoop cond init_v
  where
    withLoopParams v =
      let sparams' =
            resolveExistentials
              sparams
              (patternStructType pat)
              (valueShape v)
       in matchPattern (i64Env sparams' <> env) pat v

    inc = (`P.doAdd` Int64Value 1)
    zero = (`P.doMul` Int64Value 0)

    forLoop iv bound i v
      | i >= bound = return v
      | otherwise = do
        env' <- withLoopParams v
        forLoop iv bound (inc i)
          =<< eval
            ( valEnv
                ( M.singleton
                    iv
                    ( Just $ T.BoundV [] $ Scalar $ Prim $ Signed Int64,
                      ValuePrim (SignedValue i)
                    )
                )
                <> env'
            )
            body

    whileLoop cond v = do
      env' <- withLoopParams v
      continue <- asBool <$> eval env' cond
      if continue
        then whileLoop cond =<< eval env' body
        else return v

    forInLoop in_pat v in_v = do
      env' <- withLoopParams v
      env'' <- matchPattern env' in_pat in_v
      eval env'' body
evalAppExp env (Match e cs _) = do
  v <- eval env e
  match v (NE.toList cs)
  where
    match _ [] =
      error "Pattern match failure."
    match v (c : cs') = do
      c' <- evalCase v env c
      case c' of
        Just v' -> return v'
        Nothing -> match v cs'

eval :: Env -> Exp -> EvalM Value
eval _ (Literal v _) = return $ ValuePrim v
eval env (Parens e _) = eval env e
eval env (QualParens (qv, _) e loc) = do
  m <- evalModuleVar env qv
  case m of
    ModuleFun {} -> error $ "Local open of module function at " ++ locStr loc
    Module m' -> eval (m' <> env) e
eval env (TupLit vs _) = toTuple <$> mapM (eval env) vs
eval env (RecordLit fields _) =
  ValueRecord . M.fromList <$> mapM evalField fields
  where
    evalField (RecordFieldExplicit k e _) = do
      v <- eval env e
      return (k, v)
    evalField (RecordFieldImplicit k t loc) = do
      v <- eval env $ Var (qualName k) t loc
      return (baseName k, v)
eval _ (StringLit vs _) =
  return $
    toArray' ShapeLeaf $
      map (ValuePrim . UnsignedValue . Int8Value . fromIntegral) vs
eval env (ArrayLit [] (Info t) _) = do
  t' <- typeValueShape env $ toStruct t
  return $ toArray t' []
eval env (ArrayLit (v : vs) _ _) = do
  v' <- eval env v
  vs' <- mapM (eval env) vs
  return $ toArray' (valueShape v') (v' : vs')
eval env (AppExp e (Info (AppRes t retext))) =
  returned env t retext =<< evalAppExp env e
eval env (Var qv (Info t) _) = evalTermVar env qv (toStruct t)
eval env (Ascript e _ _) = eval env e
eval _ (IntLit v (Info t) _) =
  case t of
    Scalar (Prim (Signed it)) ->
      return $ ValuePrim $ SignedValue $ intValue it v
    Scalar (Prim (Unsigned it)) ->
      return $ ValuePrim $ UnsignedValue $ intValue it v
    Scalar (Prim (FloatType ft)) ->
      return $ ValuePrim $ FloatValue $ floatValue ft v
    _ -> error $ "eval: nonsensical type for integer literal: " ++ pretty t
eval _ (FloatLit v (Info t) _) =
  case t of
    Scalar (Prim (FloatType ft)) ->
      return $ ValuePrim $ FloatValue $ floatValue ft v
    _ -> error $ "eval: nonsensical type for float literal: " ++ pretty t
eval env (Negate e _) = do
  ev <- eval env e
  ValuePrim <$> case ev of
    ValuePrim (SignedValue (Int8Value v)) -> return $ SignedValue $ Int8Value (- v)
    ValuePrim (SignedValue (Int16Value v)) -> return $ SignedValue $ Int16Value (- v)
    ValuePrim (SignedValue (Int32Value v)) -> return $ SignedValue $ Int32Value (- v)
    ValuePrim (SignedValue (Int64Value v)) -> return $ SignedValue $ Int64Value (- v)
    ValuePrim (UnsignedValue (Int8Value v)) -> return $ UnsignedValue $ Int8Value (- v)
    ValuePrim (UnsignedValue (Int16Value v)) -> return $ UnsignedValue $ Int16Value (- v)
    ValuePrim (UnsignedValue (Int32Value v)) -> return $ UnsignedValue $ Int32Value (- v)
    ValuePrim (UnsignedValue (Int64Value v)) -> return $ UnsignedValue $ Int64Value (- v)
    ValuePrim (FloatValue (Float32Value v)) -> return $ FloatValue $ Float32Value (- v)
    ValuePrim (FloatValue (Float64Value v)) -> return $ FloatValue $ Float64Value (- v)
    _ -> error $ "Cannot negate " ++ pretty ev
eval env (Update src is v loc) =
  maybe oob return
    =<< updateArray <$> mapM (evalDimIndex env) is <*> eval env src <*> eval env v
  where
    oob = bad loc env "Bad update"
eval env (RecordUpdate src all_fs v _ _) =
  update <$> eval env src <*> pure all_fs <*> eval env v
  where
    update _ [] v' = v'
    update (ValueRecord src') (f : fs) v'
      | Just f_v <- M.lookup f src' =
        ValueRecord $ M.insert f (update f_v fs v') src'
    update _ _ _ = error "eval RecordUpdate: invalid value."
-- We treat zero-parameter lambdas as simply an expression to
-- evaluate immediately.  Note that this is *not* the same as a lambda
-- that takes an empty tuple '()' as argument!  Zero-parameter lambdas
-- can never occur in a well-formed Futhark program, but they are
-- convenient in the interpreter.
eval env (Lambda ps body _ (Info (_, RetType _ rt)) _) =
  evalFunction env [] ps body rt
eval env (OpSection qv (Info t) _) = evalTermVar env qv $ toStruct t
eval env (OpSectionLeft qv _ e (Info (_, _, argext), _) (Info (RetType _ t)) loc) = do
  v <- evalArg env e argext
  f <- evalTermVar env qv (toStruct t)
  apply loc env f v
eval env (OpSectionRight qv _ e (Info _, Info (_, _, argext)) (Info (RetType _ t)) loc) = do
  y <- evalArg env e argext
  return $
    ValueFun $ \x -> do
      f <- evalTermVar env qv $ toStruct t
      apply2 loc env f x y
eval env (IndexSection is _ loc) = do
  is' <- mapM (evalDimIndex env) is
  return $ ValueFun $ evalIndex loc env is'
eval _ (ProjectSection ks _ _) =
  return $ ValueFun $ flip (foldM walk) ks
  where
    walk (ValueRecord fs) f
      | Just v' <- M.lookup f fs = return v'
    walk _ _ = error "Value does not have expected field."
eval env (Project f e _ _) = do
  v <- eval env e
  case v of
    ValueRecord fs | Just v' <- M.lookup f fs -> return v'
    _ -> error "Value does not have expected field."
eval env (Assert what e (Info s) loc) = do
  cond <- asBool <$> eval env what
  unless cond $ bad loc env s
  eval env e
eval env (Constr c es (Info t) _) = do
  vs <- mapM (eval env) es
  shape <- typeValueShape env $ toStruct t
  return $ ValueSum shape c vs
eval env (Attr _ e _) = eval env e

evalCase ::
  Value ->
  Env ->
  CaseBase Info VName ->
  EvalM (Maybe Value)
evalCase v env (CasePat p cExp _) = runMaybeT $ do
  env' <- patternMatch env p v
  lift $ eval env' cExp

-- We hackily do multiple substitutions in modules, because otherwise
-- we would lose in cases where the parameter substitutions are [a->x,
-- b->x] when we reverse. (See issue #1250.)
reverseSubstitutions :: M.Map VName VName -> M.Map VName [VName]
reverseSubstitutions =
  M.fromListWith (<>) . map (second pure . uncurry (flip (,))) . M.toList

substituteInModule :: M.Map VName VName -> Module -> Module
substituteInModule substs = onModule
  where
    rev_substs = reverseSubstitutions substs
    replace v = fromMaybe [v] $ M.lookup v rev_substs
    replaceQ v = maybe v qualName $ maybeHead =<< M.lookup (qualLeaf v) rev_substs
    replaceM f m = M.fromList $ do
      (k, v) <- M.toList m
      k' <- replace k
      return (k', f v)
    onModule (Module (Env terms types _)) =
      Module $ Env (replaceM onTerm terms) (replaceM onType types) mempty
    onModule (ModuleFun f) =
      ModuleFun $ \m -> onModule <$> f (substituteInModule (M.mapMaybe maybeHead rev_substs) m)
    onTerm (TermValue t v) = TermValue t v
    onTerm (TermPoly t v) = TermPoly t v
    onTerm (TermModule m) = TermModule $ onModule m
    onType (T.TypeAbbr l ps t) = T.TypeAbbr l ps $ first onDim t
    onDim (NamedDim v) = NamedDim $ replaceQ v
    onDim (ConstDim x) = ConstDim x

evalModuleVar :: Env -> QualName VName -> EvalM Module
evalModuleVar env qv =
  case lookupVar qv env of
    Just (TermModule m) -> return m
    _ -> error $ quote (pretty qv) <> " is not bound to a module."

evalModExp :: Env -> ModExp -> EvalM Module
evalModExp _ (ModImport _ (Info f) _) = do
  f' <- lookupImport f
  case f' of
    Nothing -> error $ "Unknown import " ++ show f
    Just m -> return $ Module m
evalModExp env (ModDecs ds _) = do
  Env terms types _ <- foldM evalDec env ds
  -- Remove everything that was present in the original Env.
  return $
    Module $
      Env
        (terms `M.difference` envTerm env)
        (types `M.difference` envType env)
        mempty
evalModExp env (ModVar qv _) =
  evalModuleVar env qv
evalModExp env (ModAscript me _ (Info substs) _) =
  substituteInModule substs <$> evalModExp env me
evalModExp env (ModParens me _) = evalModExp env me
evalModExp env (ModLambda p ret e loc) =
  return $
    ModuleFun $ \am -> do
      let env' = env {envTerm = M.insert (modParamName p) (TermModule am) $ envTerm env}
      evalModExp env' $ case ret of
        Nothing -> e
        Just (se, rsubsts) -> ModAscript e se rsubsts loc
evalModExp env (ModApply f e (Info psubst) (Info rsubst) _) = do
  f' <- evalModExp env f
  case f' of
    ModuleFun f'' -> do
      e' <- evalModExp env e
      substituteInModule rsubst <$> f'' (substituteInModule psubst e')
    _ -> error "Expected ModuleFun."

evalDec :: Env -> Dec -> EvalM Env
evalDec env (ValDec (ValBind _ v _ (Info (RetType _ ret, retext)) tparams ps fbody _ _ _)) = do
  binding <- evalFunctionBinding env tparams ps ret retext fbody
  return $ env {envTerm = M.insert v binding $ envTerm env}
evalDec env (OpenDec me _) = do
  me' <- evalModExp env me
  case me' of
    Module me'' -> return $ me'' <> env
    _ -> error "Expected Module"
evalDec env (ImportDec name name' loc) =
  evalDec env $ LocalDec (OpenDec (ModImport name name' loc) loc) loc
evalDec env (LocalDec d _) = evalDec env d
evalDec env SigDec {} = return env
evalDec env (TypeDec (TypeBind v l ps _ (Info (RetType dims t)) _ _)) = do
  let abbr = T.TypeAbbr l ps . RetType dims $ evalType env t
  return env {envType = M.insert v abbr $ envType env}
evalDec env (ModDec (ModBind v ps ret body _ loc)) = do
  mod <- evalModExp env $ wrapInLambda ps
  return $ modEnv (M.singleton v mod) <> env
  where
    wrapInLambda [] = case ret of
      Just (se, substs) -> ModAscript body se substs loc
      Nothing -> body
    wrapInLambda [p] = ModLambda p ret body loc
    wrapInLambda (p : ps') = ModLambda p Nothing (wrapInLambda ps') loc

-- | The interpreter context.  All evaluation takes place with respect
-- to a context, and it can be extended with more definitions, which
-- is how the REPL works.
data Ctx = Ctx
  { ctxEnv :: Env,
    ctxImports :: M.Map FilePath Env
  }

nanValue :: PrimValue -> Bool
nanValue (FloatValue v) =
  case v of
    Float32Value x -> isNaN x
    Float64Value x -> isNaN x
nanValue _ = False

breakOnNaN :: [PrimValue] -> PrimValue -> EvalM ()
breakOnNaN inputs result
  | not (any nanValue inputs) && nanValue result = do
    backtrace <- asks fst
    case NE.nonEmpty backtrace of
      Nothing -> return ()
      Just backtrace' -> liftF $ ExtOpBreak BreakNaN backtrace' ()
breakOnNaN _ _ =
  return ()

-- | The initial environment contains definitions of the various intrinsic functions.
initialCtx :: Ctx
initialCtx =
  Ctx
    ( Env
        ( M.insert
            (VName (nameFromString "intrinsics") 0)
            (TermModule (Module $ Env terms types mempty))
            terms
        )
        types
        mempty
    )
    mempty
  where
    terms = M.mapMaybeWithKey (const . def . baseString) intrinsics
    types = M.mapMaybeWithKey (const . tdef . baseString) intrinsics

    sintOp f =
      [ (getS, putS, P.doBinOp (f Int8)),
        (getS, putS, P.doBinOp (f Int16)),
        (getS, putS, P.doBinOp (f Int32)),
        (getS, putS, P.doBinOp (f Int64))
      ]
    uintOp f =
      [ (getU, putU, P.doBinOp (f Int8)),
        (getU, putU, P.doBinOp (f Int16)),
        (getU, putU, P.doBinOp (f Int32)),
        (getU, putU, P.doBinOp (f Int64))
      ]
    intOp f = sintOp f ++ uintOp f
    floatOp f =
      [ (getF, putF, P.doBinOp (f Float32)),
        (getF, putF, P.doBinOp (f Float64))
      ]
    arithOp f g = Just $ bopDef $ intOp f ++ floatOp g

    flipCmps = map (\(f, g, h) -> (f, g, flip h))
    sintCmp f =
      [ (getS, Just . BoolValue, P.doCmpOp (f Int8)),
        (getS, Just . BoolValue, P.doCmpOp (f Int16)),
        (getS, Just . BoolValue, P.doCmpOp (f Int32)),
        (getS, Just . BoolValue, P.doCmpOp (f Int64))
      ]
    uintCmp f =
      [ (getU, Just . BoolValue, P.doCmpOp (f Int8)),
        (getU, Just . BoolValue, P.doCmpOp (f Int16)),
        (getU, Just . BoolValue, P.doCmpOp (f Int32)),
        (getU, Just . BoolValue, P.doCmpOp (f Int64))
      ]
    floatCmp f =
      [ (getF, Just . BoolValue, P.doCmpOp (f Float32)),
        (getF, Just . BoolValue, P.doCmpOp (f Float64))
      ]
    boolCmp f = [(getB, Just . BoolValue, P.doCmpOp f)]

    getV (SignedValue x) = Just $ P.IntValue x
    getV (UnsignedValue x) = Just $ P.IntValue x
    getV (FloatValue x) = Just $ P.FloatValue x
    getV (BoolValue x) = Just $ P.BoolValue x
    putV (P.IntValue x) = SignedValue x
    putV (P.FloatValue x) = FloatValue x
    putV (P.BoolValue x) = BoolValue x
    putV P.UnitValue = BoolValue True

    getS (SignedValue x) = Just $ P.IntValue x
    getS _ = Nothing
    putS (P.IntValue x) = Just $ SignedValue x
    putS _ = Nothing

    getU (UnsignedValue x) = Just $ P.IntValue x
    getU _ = Nothing
    putU (P.IntValue x) = Just $ UnsignedValue x
    putU _ = Nothing

    getF (FloatValue x) = Just $ P.FloatValue x
    getF _ = Nothing
    putF (P.FloatValue x) = Just $ FloatValue x
    putF _ = Nothing

    getB (BoolValue x) = Just $ P.BoolValue x
    getB _ = Nothing
    putB (P.BoolValue x) = Just $ BoolValue x
    putB _ = Nothing

    fun1 f =
      TermValue Nothing $ ValueFun $ \x -> f x
    fun2 f =
      TermValue Nothing $
        ValueFun $ \x ->
          return $ ValueFun $ \y -> f x y
    fun2t f =
      TermValue Nothing $
        ValueFun $ \v ->
          case fromTuple v of
            Just [x, y] -> f x y
            _ -> error $ "Expected pair; got: " ++ pretty v
    fun3t f =
      TermValue Nothing $
        ValueFun $ \v ->
          case fromTuple v of
            Just [x, y, z] -> f x y z
            _ -> error $ "Expected triple; got: " ++ pretty v

    fun5t f =
      TermValue Nothing $
        ValueFun $ \v ->
          case fromTuple v of
            Just [x, y, z, a, b] -> f x y z a b
            _ -> error $ "Expected pentuple; got: " ++ pretty v

    fun6t f =
      TermValue Nothing $
        ValueFun $ \v ->
          case fromTuple v of
            Just [x, y, z, a, b, c] -> f x y z a b c
            _ -> error $ "Expected sextuple; got: " ++ pretty v

    bopDef fs = fun2 $ \x y ->
      case (x, y) of
        (ValuePrim x', ValuePrim y')
          | Just z <- msum $ map (`bopDef'` (x', y')) fs -> do
            breakOnNaN [x', y'] z
            return $ ValuePrim z
        _ ->
          bad noLoc mempty $
            "Cannot apply operator to arguments "
              <> quote (pretty x)
              <> " and "
              <> quote (pretty y)
              <> "."
      where
        bopDef' (valf, retf, op) (x, y) = do
          x' <- valf x
          y' <- valf y
          retf =<< op x' y'

    unopDef fs = fun1 $ \x ->
      case x of
        (ValuePrim x')
          | Just r <- msum $ map (`unopDef'` x') fs -> do
            breakOnNaN [x'] r
            return $ ValuePrim r
        _ ->
          bad noLoc mempty $
            "Cannot apply function to argument "
              <> quote (pretty x)
              <> "."
      where
        unopDef' (valf, retf, op) x = do
          x' <- valf x
          retf =<< op x'

    tbopDef f = fun1 $ \v ->
      case fromTuple v of
        Just [ValuePrim x, ValuePrim y]
          | Just x' <- getV x,
            Just y' <- getV y,
            Just z <- putV <$> f x' y' -> do
            breakOnNaN [x, y] z
            return $ ValuePrim z
        _ ->
          bad noLoc mempty $
            "Cannot apply operator to argument "
              <> quote (pretty v)
              <> "."

    def "!" =
      Just $
        unopDef
          [ (getS, putS, P.doUnOp $ P.Complement Int8),
            (getS, putS, P.doUnOp $ P.Complement Int16),
            (getS, putS, P.doUnOp $ P.Complement Int32),
            (getS, putS, P.doUnOp $ P.Complement Int64),
            (getU, putU, P.doUnOp $ P.Complement Int8),
            (getU, putU, P.doUnOp $ P.Complement Int16),
            (getU, putU, P.doUnOp $ P.Complement Int32),
            (getU, putU, P.doUnOp $ P.Complement Int64),
            (getB, putB, P.doUnOp P.Not)
          ]
    def "+" = arithOp (`P.Add` P.OverflowWrap) P.FAdd
    def "-" = arithOp (`P.Sub` P.OverflowWrap) P.FSub
    def "*" = arithOp (`P.Mul` P.OverflowWrap) P.FMul
    def "**" = arithOp P.Pow P.FPow
    def "/" =
      Just $
        bopDef $
          sintOp (`P.SDiv` P.Unsafe)
            ++ uintOp (`P.UDiv` P.Unsafe)
            ++ floatOp P.FDiv
    def "%" =
      Just $
        bopDef $
          sintOp (`P.SMod` P.Unsafe)
            ++ uintOp (`P.UMod` P.Unsafe)
            ++ floatOp P.FMod
    def "//" =
      Just $
        bopDef $
          sintOp (`P.SQuot` P.Unsafe)
            ++ uintOp (`P.UDiv` P.Unsafe)
    def "%%" =
      Just $
        bopDef $
          sintOp (`P.SRem` P.Unsafe)
            ++ uintOp (`P.UMod` P.Unsafe)
    def "^" = Just $ bopDef $ intOp P.Xor
    def "&" = Just $ bopDef $ intOp P.And
    def "|" = Just $ bopDef $ intOp P.Or
    def ">>" = Just $ bopDef $ sintOp P.AShr ++ uintOp P.LShr
    def "<<" = Just $ bopDef $ intOp P.Shl
    def ">>>" = Just $ bopDef $ sintOp P.LShr ++ uintOp P.LShr
    def "==" = Just $
      fun2 $
        \xs ys -> return $ ValuePrim $ BoolValue $ xs == ys
    def "!=" = Just $
      fun2 $
        \xs ys -> return $ ValuePrim $ BoolValue $ xs /= ys
    -- The short-circuiting is handled directly in 'eval'; these cases
    -- are only used when partially applying and such.
    def "&&" = Just $
      fun2 $ \x y ->
        return $ ValuePrim $ BoolValue $ asBool x && asBool y
    def "||" = Just $
      fun2 $ \x y ->
        return $ ValuePrim $ BoolValue $ asBool x || asBool y
    def "<" =
      Just $
        bopDef $
          sintCmp P.CmpSlt ++ uintCmp P.CmpUlt
            ++ floatCmp P.FCmpLt
            ++ boolCmp P.CmpLlt
    def ">" =
      Just $
        bopDef $
          flipCmps $
            sintCmp P.CmpSlt ++ uintCmp P.CmpUlt
              ++ floatCmp P.FCmpLt
              ++ boolCmp P.CmpLlt
    def "<=" =
      Just $
        bopDef $
          sintCmp P.CmpSle ++ uintCmp P.CmpUle
            ++ floatCmp P.FCmpLe
            ++ boolCmp P.CmpLle
    def ">=" =
      Just $
        bopDef $
          flipCmps $
            sintCmp P.CmpSle ++ uintCmp P.CmpUle
              ++ floatCmp P.FCmpLe
              ++ boolCmp P.CmpLle
    def s
      | Just bop <- find ((s ==) . pretty) P.allBinOps =
        Just $ tbopDef $ P.doBinOp bop
      | Just unop <- find ((s ==) . pretty) P.allCmpOps =
        Just $ tbopDef $ \x y -> P.BoolValue <$> P.doCmpOp unop x y
      | Just cop <- find ((s ==) . pretty) P.allConvOps =
        Just $ unopDef [(getV, Just . putV, P.doConvOp cop)]
      | Just unop <- find ((s ==) . pretty) P.allUnOps =
        Just $ unopDef [(getV, Just . putV, P.doUnOp unop)]
      | Just (pts, _, f) <- M.lookup s P.primFuns =
        case length pts of
          1 -> Just $ unopDef [(getV, Just . putV, f . pure)]
          _ -> Just $
            fun1 $ \x -> do
              let getV' (ValuePrim v) = Just v
                  getV' _ = Nothing
              case mapM getV' =<< fromTuple x of
                Just vs
                  | Just res <- fmap putV . f =<< mapM getV vs -> do
                    breakOnNaN vs res
                    return $ ValuePrim res
                _ ->
                  error $ "Cannot apply " ++ pretty s ++ " to " ++ pretty x
      | "sign_" `isPrefixOf` s =
        Just $
          fun1 $ \x ->
            case x of
              (ValuePrim (UnsignedValue x')) ->
                return $ ValuePrim $ SignedValue x'
              _ -> error $ "Cannot sign: " ++ pretty x
      | "unsign_" `isPrefixOf` s =
        Just $
          fun1 $ \x ->
            case x of
              (ValuePrim (SignedValue x')) ->
                return $ ValuePrim $ UnsignedValue x'
              _ -> error $ "Cannot unsign: " ++ pretty x
    def s
      | "map_stream" `isPrefixOf` s =
        Just $ fun2t stream
    def s | "reduce_stream" `isPrefixOf` s =
      Just $ fun3t $ \_ f arg -> stream f arg
    def "map" = Just $
      TermPoly Nothing $ \t -> return $
        ValueFun $ \v ->
          case (fromTuple v, unfoldFunType t) of
            (Just [f, xs], ([_], ret_t))
              | Just rowshape <- typeRowShape ret_t ->
                toArray' rowshape <$> mapM (apply noLoc mempty f) (snd $ fromArray xs)
              | otherwise ->
                error $ "Bad return type: " ++ pretty ret_t
            _ ->
              error $
                "Invalid arguments to map intrinsic:\n"
                  ++ unlines [pretty t, pretty v]
      where
        typeRowShape = sequenceA . structTypeShape mempty . stripArray 1
    def s | "reduce" `isPrefixOf` s = Just $
      fun3t $ \f ne xs ->
        foldM (apply2 noLoc mempty f) ne $ snd $ fromArray xs
    def "scan" = Just $
      fun3t $ \f ne xs -> do
        let next (out, acc) x = do
              x' <- apply2 noLoc mempty f acc x
              return (x' : out, x')
        toArray' (valueShape ne) . reverse . fst
          <$> foldM next ([], ne) (snd $ fromArray xs)
    def "scatter" = Just $
      fun3t $ \arr is vs ->
        case arr of
          ValueArray shape arr' ->
            return $
              ValueArray shape $
                foldl' update arr' $
                  zip (map asInt $ snd $ fromArray is) (snd $ fromArray vs)
          _ ->
            error $ "scatter expects array, but got: " ++ pretty arr
      where
        update arr' (i, v) =
          if i >= 0 && i < arrayLength arr'
            then arr' // [(i, v)]
            else arr'
    def "scatter_2d" = Just $
      fun3t $ \arr is vs ->
        case arr of
          ValueArray _ _ ->
            return $
              foldl' update arr $
                zip (map fromTuple $ snd $ fromArray is) (snd $ fromArray vs)
          _ ->
            error $ "scatter_2d expects array, but got: " ++ pretty arr
      where
        update :: Value -> (Maybe [Value], Value) -> Value
        update arr (Just idxs@[_, _], v) =
          fromMaybe arr $ updateArray (map (IndexingFix . asInt64) idxs) arr v
        update _ _ =
          error "scatter_2d expects 2-dimensional indices"
    def "scatter_3d" = Just $
      fun3t $ \arr is vs ->
        case arr of
          ValueArray _ _ ->
            return $
              foldl' update arr $
                zip (map fromTuple $ snd $ fromArray is) (snd $ fromArray vs)
          _ ->
            error $ "scatter_3d expects array, but got: " ++ pretty arr
      where
        update :: Value -> (Maybe [Value], Value) -> Value
        update arr (Just idxs@[_, _, _], v) =
          fromMaybe arr $ updateArray (map (IndexingFix . asInt64) idxs) arr v
        update _ _ =
          error "scatter_3d expects 3-dimensional indices"
    def "hist" = Just $
      fun6t $ \_ arr fun _ is vs ->
        case arr of
          ValueArray shape arr' ->
            ValueArray shape
              <$> foldM
                (update fun)
                arr'
                (zip (map asInt $ snd $ fromArray is) (snd $ fromArray vs))
          _ ->
            error $ "hist expects array, but got: " ++ pretty arr
      where
        update fun arr' (i, v) =
          if i >= 0 && i < arrayLength arr'
            then do
              v' <- apply2 noLoc mempty fun (arr' ! i) v
              return $ arr' // [(i, v')]
            else return arr'
    def "partition" = Just $
      fun3t $ \k f xs -> do
        let (ShapeDim _ rowshape, xs') = fromArray xs

            next outs x = do
              i <- asInt <$> apply noLoc mempty f x
              return $ insertAt i x outs
            pack parts =
              toTuple
                [ toArray' rowshape $ concat parts,
                  toArray' rowshape $
                    map (ValuePrim . SignedValue . Int64Value . genericLength) parts
                ]

        pack . map reverse
          <$> foldM next (replicate (asInt k) []) xs'
      where
        insertAt 0 x (l : ls) = (x : l) : ls
        insertAt i x (l : ls) = l : insertAt (i -1) x ls
        insertAt _ _ ls = ls
    def "scatter_stream" = Just $
      fun3t $ \dest f vs ->
        case (dest, vs) of
          ( ValueArray dest_shape dest_arr,
            ValueArray _ vs_arr
            ) -> do
              let acc = ValueAcc (\_ x -> pure x) dest_arr
              acc' <- foldM (apply2 noLoc mempty f) acc vs_arr
              case acc' of
                ValueAcc _ dest_arr' ->
                  return $ ValueArray dest_shape dest_arr'
                _ ->
                  error $ "scatter_stream produced: " ++ pretty acc'
          _ ->
            error $ "scatter_stream expects array, but got: " ++ pretty (dest, vs)
    def "hist_stream" = Just $
      fun5t $ \dest op _ne f vs ->
        case (dest, vs) of
          ( ValueArray dest_shape dest_arr,
            ValueArray _ vs_arr
            ) -> do
              let acc = ValueAcc (apply2 noLoc mempty op) dest_arr
              acc' <- foldM (apply2 noLoc mempty f) acc vs_arr
              case acc' of
                ValueAcc _ dest_arr' ->
                  return $ ValueArray dest_shape dest_arr'
                _ ->
                  error $ "hist_stream produced: " ++ pretty acc'
          _ ->
            error $ "hist_stream expects array, but got: " ++ pretty (dest, vs)
    def "acc_write" = Just $
      fun3t $ \acc i v ->
        case (acc, i) of
          ( ValueAcc op acc_arr,
            ValuePrim (SignedValue (Int64Value i'))
            ) ->
              if i' >= 0 && i' < arrayLength acc_arr
                then do
                  let x = acc_arr ! fromIntegral i'
                  res <- op x v
                  pure $ ValueAcc op $ acc_arr // [(fromIntegral i', res)]
                else pure acc
          _ ->
            error $ "acc_write invalid arguments: " ++ pretty (acc, i, v)
    def "unzip" = Just $
      fun1 $ \x -> do
        let ShapeDim _ (ShapeRecord fs) = valueShape x
            Just [xs_shape, ys_shape] = areTupleFields fs
            listPair (xs, ys) =
              [toArray' xs_shape xs, toArray' ys_shape ys]

        return $ toTuple $ listPair $ unzip $ map (fromPair . fromTuple) $ snd $ fromArray x
      where
        fromPair (Just [x, y]) = (x, y)
        fromPair l = error $ "Not a pair: " ++ pretty l
    def "zip" = Just $
      fun2t $ \xs ys -> do
        let ShapeDim _ xs_rowshape = valueShape xs
            ShapeDim _ ys_rowshape = valueShape ys
        return $
          toArray' (ShapeRecord (tupleFields [xs_rowshape, ys_rowshape])) $
            map toTuple $ transpose [snd $ fromArray xs, snd $ fromArray ys]
    def "concat" = Just $
      fun2t $ \xs ys -> do
        let (ShapeDim _ rowshape, xs') = fromArray xs
            (_, ys') = fromArray ys
        return $ toArray' rowshape $ xs' ++ ys'
    def "transpose" = Just $
      fun1 $ \xs -> do
        let (ShapeDim n (ShapeDim m shape), xs') = fromArray xs
        return $
          toArray (ShapeDim m (ShapeDim n shape)) $
            map (toArray (ShapeDim n shape)) $ transpose $ map (snd . fromArray) xs'
    def "rotate" = Just $
      fun2t $ \i xs -> do
        let (shape, xs') = fromArray xs
        return $
          let idx = if null xs' then 0 else rem (asInt i) (length xs')
           in if idx > 0
                then
                  let (bef, aft) = splitAt idx xs'
                   in toArray shape $ aft ++ bef
                else
                  let (bef, aft) = splitFromEnd (- idx) xs'
                   in toArray shape $ aft ++ bef
    def "flatten" = Just $
      fun1 $ \xs -> do
        let (ShapeDim n (ShapeDim m shape), xs') = fromArray xs
        return $ toArray (ShapeDim (n * m) shape) $ concatMap (snd . fromArray) xs'
    def "unflatten" = Just $
      fun3t $ \n m xs -> do
        let (ShapeDim _ innershape, xs') = fromArray xs
            rowshape = ShapeDim (asInt64 m) innershape
            shape = ShapeDim (asInt64 n) rowshape
        return $ toArray shape $ map (toArray rowshape) $ chunk (asInt m) xs'
    def "opaque" = Just $ fun1 return
    def "trace" = Just $ fun1 $ \v -> trace v >> return v
    def "break" = Just $
      fun1 $ \v -> do
        break
        return v
    def "acc" = Nothing
    def s | nameFromString s `M.member` namesToPrimTypes = Nothing
    def s = error $ "Missing intrinsic: " ++ s

    tdef s = do
      t <- nameFromString s `M.lookup` namesToPrimTypes
      return $ T.TypeAbbr Unlifted [] $ RetType [] $ Scalar $ Prim t

    stream f arg@(ValueArray _ xs) =
      let n = ValuePrim $ SignedValue $ Int64Value $ arrayLength xs
       in apply2 noLoc mempty f n arg
    stream _ arg = error $ "Cannot stream: " ++ pretty arg

interpretExp :: Ctx -> Exp -> F ExtOp Value
interpretExp ctx e = runEvalM (ctxImports ctx) $ eval (ctxEnv ctx) e

interpretDec :: Ctx -> Dec -> F ExtOp Ctx
interpretDec ctx d = do
  env <- runEvalM (ctxImports ctx) $ do
    env <- evalDec (ctxEnv ctx) d
    -- We need to extract any new existential sizes and add them as
    -- ordinary bindings to the context, or we will not be able to
    -- look up their values later.
    sizes <- extSizeEnv
    pure $ env <> sizes
  return ctx {ctxEnv = env}

interpretImport :: Ctx -> (FilePath, Prog) -> F ExtOp Ctx
interpretImport ctx (fp, prog) = do
  env <- runEvalM (ctxImports ctx) $ foldM evalDec (ctxEnv ctx) $ progDecs prog
  return ctx {ctxImports = M.insert fp env $ ctxImports ctx}

checkEntryArgs :: VName -> [F.Value] -> StructType -> Either String ()
checkEntryArgs entry args entry_t
  | args_ts == param_ts =
    return ()
  | otherwise =
    Left $
      pretty $
        expected
          </> "Got input of types"
          </> indent 2 (stack (map ppr args_ts))
  where
    (param_ts, _) = unfoldFunType entry_t
    args_ts = map (valueStructType . valueType) args
    expected
      | null param_ts =
        "Entry point " <> pquote (pprName entry) <> " is not a function."
      | otherwise =
        "Entry point " <> pquote (pprName entry) <> " expects input of type(s)"
          </> indent 2 (stack (map ppr param_ts))

-- | Execute the named function on the given arguments; may fail
-- horribly if these are ill-typed.
interpretFunction :: Ctx -> VName -> [F.Value] -> Either String (F ExtOp Value)
interpretFunction ctx fname vs = do
  ft <- case lookupVar (qualName fname) $ ctxEnv ctx of
    Just (TermValue (Just (T.BoundV _ t)) _) ->
      updateType (map valueType vs) t
    Just (TermPoly (Just (T.BoundV _ t)) _) ->
      updateType (map valueType vs) t
    _ ->
      Left $ "Unknown function `" <> prettyName fname <> "`."

  vs' <- case mapM convertValue vs of
    Just vs' -> Right vs'
    Nothing -> Left "Invalid input: irregular array."

  checkEntryArgs fname vs ft

  Right $
    runEvalM (ctxImports ctx) $ do
      f <- evalTermVar (ctxEnv ctx) (qualName fname) ft
      foldM (apply noLoc mempty) f vs'
  where
    updateType (vt : vts) (Scalar (Arrow als u pt (RetType dims rt))) = do
      checkInput vt pt
      Scalar . Arrow als u (valueStructType vt) . RetType dims <$> updateType vts rt
    updateType _ t =
      Right t

    -- FIXME: we don't check array sizes.
    checkInput :: ValueType -> StructType -> Either String ()
    checkInput (Scalar (Prim vt)) (Scalar (Prim pt))
      | vt /= pt = badPrim vt pt
    checkInput (Array _ _ (Prim vt) _) (Array _ _ (Prim pt) _)
      | vt /= pt = badPrim vt pt
    checkInput _ _ =
      Right ()

    badPrim vt pt =
      Left . pretty $
        "Invalid argument type."
          </> "Expected:" <+> align (ppr pt)
          </> "Got:     " <+> align (ppr vt)

    convertValue (F.PrimValue p) = Just $ ValuePrim p
    convertValue (F.ArrayValue arr t) = mkArray t =<< mapM convertValue (elems arr)
