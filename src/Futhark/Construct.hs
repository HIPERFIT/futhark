{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

-- | = Constructing Futhark ASTs
--
-- This module re-exports and defines a bunch of building blocks for
-- constructing fragments of Futhark ASTs.  More importantly, it also
-- contains a basic introduction on how to use them.
--
-- The "Futhark.IR.Syntax" module contains the core
-- AST definition.  One important invariant is that all bound names in
-- a Futhark program must be /globally/ unique.  In principle, you
-- could use the facilities from "Futhark.MonadFreshNames" (or your
-- own bespoke source of unique names) to manually construct
-- expressions, statements, and entire ASTs.  In practice, this would
-- be very tedious.  Instead, we have defined a collection of building
-- blocks (centered around the 'MonadBinder' type class) that permits
-- a more abstract way of generating code.
--
-- Constructing ASTs with these building blocks requires you to ensure
-- that all free variables are in scope.  See
-- "Futhark.IR.Prop.Scope".
--
-- == 'MonadBinder'
--
-- A monad that implements 'MonadBinder' tracks the statements added
-- so far, the current names in scope, and allows you to add
-- additional statements with 'addStm'.  Any monad that implements
-- 'MonadBinder' also implements the t'REp' type family, which
-- indicates which rep it works with.  Inside a 'MonadBinder' we can
-- use 'collectStms' to gather up the 'Stms' added with 'addStm' in
-- some nested computation.
--
-- The 'BinderT' monad (and its convenient 'Binder' version) provides
-- the simplest implementation of 'MonadBinder'.
--
-- == Higher-level building blocks
--
-- On top of the raw facilities provided by 'MonadBinder', we have
-- more convenient facilities.  For example, 'letSubExp' lets us
-- conveniently create a 'Stm' for an 'Exp' that produces a /single/
-- value, and returns the (fresh) name for the resulting variable:
--
-- @
-- z <- letExp "z" $ BasicOp $ BinOp (Add Int32) (Var x) (Var y)
-- @
--
-- == Examples
--
-- The "Futhark.Transform.FirstOrderTransform" module is a
-- (relatively) simple example of how to use these components.  As are
-- some of the high-level building blocks in this very module.
module Futhark.Construct
  ( letSubExp,
    letSubExps,
    letExp,
    letTupExp,
    letTupExp',
    letInPlace,
    eSubExp,
    eIf,
    eIf',
    eBinOp,
    eCmpOp,
    eConvOp,
    eSignum,
    eCopy,
    eBody,
    eLambda,
    eRoundToMultipleOf,
    eSliceArray,
    eBlank,
    eAll,
    eOutOfBounds,
    eWriteArray,
    asIntZ,
    asIntS,
    resultBody,
    resultBodyM,
    insertStmsM,
    buildBody,
    buildBody_,
    mapResult,
    foldBinOp,
    binOpLambda,
    cmpOpLambda,
    mkLambda,
    sliceDim,
    fullSlice,
    fullSliceNum,
    isFullSlice,
    sliceAt,
    ifCommon,
    module Futhark.Binder,

    -- * Result types
    instantiateShapes,
    instantiateShapes',
    removeExistentials,

    -- * Convenience
    simpleMkLetNames,
    ToExp (..),
    toSubExp,
  )
where

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor (second)
import Data.List (sortOn)
import qualified Data.Map.Strict as M
import Futhark.Binder
import Futhark.IR

letSubExp ::
  MonadBinder m =>
  String ->
  Exp (Rep m) ->
  m SubExp
letSubExp _ (BasicOp (SubExp se)) = return se
letSubExp desc e = Var <$> letExp desc e

letExp ::
  MonadBinder m =>
  String ->
  Exp (Rep m) ->
  m VName
letExp _ (BasicOp (SubExp (Var v))) =
  return v
letExp desc e = do
  n <- length <$> expExtType e
  vs <- replicateM n $ newVName desc
  letBindNames vs e
  case vs of
    [v] -> return v
    _ -> error $ "letExp: tuple-typed expression given:\n" ++ pretty e

letInPlace ::
  MonadBinder m =>
  String ->
  VName ->
  Slice SubExp ->
  Exp (Rep m) ->
  m VName
letInPlace desc src slice e = do
  tmp <- letSubExp (desc ++ "_tmp") e
  letExp desc $ BasicOp $ Update src slice tmp

letSubExps ::
  MonadBinder m =>
  String ->
  [Exp (Rep m)] ->
  m [SubExp]
letSubExps desc = mapM $ letSubExp desc

letTupExp ::
  (MonadBinder m) =>
  String ->
  Exp (Rep m) ->
  m [VName]
letTupExp _ (BasicOp (SubExp (Var v))) =
  return [v]
letTupExp name e = do
  numValues <- length <$> expExtType e
  names <- replicateM numValues $ newVName name
  letBindNames names e
  return names

letTupExp' ::
  (MonadBinder m) =>
  String ->
  Exp (Rep m) ->
  m [SubExp]
letTupExp' _ (BasicOp (SubExp se)) = return [se]
letTupExp' name ses = map Var <$> letTupExp name ses

eSubExp ::
  MonadBinder m =>
  SubExp ->
  m (Exp (Rep m))
eSubExp = pure . BasicOp . SubExp

eIf ::
  (MonadBinder m, BranchType (Rep m) ~ ExtType) =>
  m (Exp (Rep m)) ->
  m (Body (Rep m)) ->
  m (Body (Rep m)) ->
  m (Exp (Rep m))
eIf ce te fe = eIf' ce te fe IfNormal

-- | As 'eIf', but an 'IfSort' can be given.
eIf' ::
  (MonadBinder m, BranchType (Rep m) ~ ExtType) =>
  m (Exp (Rep m)) ->
  m (Body (Rep m)) ->
  m (Body (Rep m)) ->
  IfSort ->
  m (Exp (Rep m))
eIf' ce te fe if_sort = do
  ce' <- letSubExp "cond" =<< ce
  te' <- insertStmsM te
  fe' <- insertStmsM fe
  -- We need to construct the context.
  ts <- generaliseExtTypes <$> bodyExtType te' <*> bodyExtType fe'
  te'' <- addContextForBranch ts te'
  fe'' <- addContextForBranch ts fe'
  return $ If ce' te'' fe'' $ IfDec ts if_sort
  where
    addContextForBranch ts (Body _ stms val_res) = do
      body_ts <- extendedScope (traverse subExpType val_res) stmsscope
      let ctx_res =
            map snd $
              sortOn fst $
                M.toList $ shapeExtMapping ts body_ts
      mkBodyM stms $ ctx_res ++ val_res
      where
        stmsscope = scopeOf stms

-- The type of a body.  Watch out: this only works for the degenerate
-- case where the body does not already return its context.
bodyExtType :: (HasScope rep m, Monad m) => Body rep -> m [ExtType]
bodyExtType (Body _ stms res) =
  existentialiseExtTypes (M.keys stmsscope) . staticShapes
    <$> extendedScope (traverse subExpType res) stmsscope
  where
    stmsscope = scopeOf stms

eBinOp ::
  MonadBinder m =>
  BinOp ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m))
eBinOp op x y = do
  x' <- letSubExp "x" =<< x
  y' <- letSubExp "y" =<< y
  return $ BasicOp $ BinOp op x' y'

eCmpOp ::
  MonadBinder m =>
  CmpOp ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m))
eCmpOp op x y = do
  x' <- letSubExp "x" =<< x
  y' <- letSubExp "y" =<< y
  return $ BasicOp $ CmpOp op x' y'

eConvOp ::
  MonadBinder m =>
  ConvOp ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m))
eConvOp op x = do
  x' <- letSubExp "x" =<< x
  return $ BasicOp $ ConvOp op x'

eSignum ::
  MonadBinder m =>
  m (Exp (Rep m)) ->
  m (Exp (Rep m))
eSignum em = do
  e <- em
  e' <- letSubExp "signum_arg" e
  t <- subExpType e'
  case t of
    Prim (IntType int_t) ->
      return $ BasicOp $ UnOp (SSignum int_t) e'
    _ ->
      error $ "eSignum: operand " ++ pretty e ++ " has invalid type."

eCopy ::
  MonadBinder m =>
  m (Exp (Rep m)) ->
  m (Exp (Rep m))
eCopy e = BasicOp . Copy <$> (letExp "copy_arg" =<< e)

eBody ::
  (MonadBinder m) =>
  [m (Exp (Rep m))] ->
  m (Body (Rep m))
eBody es = buildBody_ $ do
  es' <- sequence es
  xs <- mapM (letTupExp "x") es'
  pure $ map Var $ concat xs

eLambda ::
  MonadBinder m =>
  Lambda (Rep m) ->
  [m (Exp (Rep m))] ->
  m [SubExp]
eLambda lam args = do
  zipWithM_ bindParam (lambdaParams lam) args
  bodyBind $ lambdaBody lam
  where
    bindParam param arg = letBindNames [paramName param] =<< arg

eRoundToMultipleOf ::
  MonadBinder m =>
  IntType ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m))
eRoundToMultipleOf t x d =
  ePlus x (eMod (eMinus d (eMod x d)) d)
  where
    eMod = eBinOp (SMod t Unsafe)
    eMinus = eBinOp (Sub t OverflowWrap)
    ePlus = eBinOp (Add t OverflowWrap)

-- | Construct an 'Index' expressions that slices an array with unit stride.
eSliceArray ::
  MonadBinder m =>
  Int ->
  VName ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m))
eSliceArray d arr i n = do
  arr_t <- lookupType arr
  let skips = map (slice (constant (0 :: Int64))) $ take d $ arrayDims arr_t
  i' <- letSubExp "slice_i" =<< i
  n' <- letSubExp "slice_n" =<< n
  return $ BasicOp $ Index arr $ fullSlice arr_t $ skips ++ [slice i' n']
  where
    slice j m = DimSlice j m (constant (1 :: Int64))

-- | Are these indexes out-of-bounds for the array?
eOutOfBounds ::
  MonadBinder m =>
  VName ->
  [m (Exp (Rep m))] ->
  m (Exp (Rep m))
eOutOfBounds arr is = do
  arr_t <- lookupType arr
  let ws = arrayDims arr_t
  is' <- mapM (letSubExp "write_i") =<< sequence is
  let checkDim w i = do
        less_than_zero <-
          letSubExp "less_than_zero" $
            BasicOp $ CmpOp (CmpSlt Int64) i (constant (0 :: Int64))
        greater_than_size <-
          letSubExp "greater_than_size" $
            BasicOp $ CmpOp (CmpSle Int64) w i
        letSubExp "outside_bounds_dim" $
          BasicOp $ BinOp LogOr less_than_zero greater_than_size
  foldBinOp LogOr (constant False) =<< zipWithM checkDim ws is'

-- | Write to an index of the array, if within bounds.  Otherwise,
-- nothing.  Produces the updated array.
eWriteArray ::
  (MonadBinder m, BranchType (Rep m) ~ ExtType) =>
  VName ->
  [m (Exp (Rep m))] ->
  m (Exp (Rep m)) ->
  m (Exp (Rep m))
eWriteArray arr is v = do
  arr_t <- lookupType arr
  is' <- mapM (letSubExp "write_i") =<< sequence is
  v' <- letSubExp "write_v" =<< v

  outside_bounds <- letSubExp "outside_bounds" =<< eOutOfBounds arr is

  outside_bounds_branch <- buildBody_ $ pure [Var arr]

  in_bounds_branch <-
    buildBody_ . fmap (pure . Var) $
      letInPlace
        "write_out_inside_bounds"
        arr
        (fullSlice arr_t (map DimFix is'))
        (BasicOp $ SubExp v')

  return $
    If outside_bounds outside_bounds_branch in_bounds_branch $
      ifCommon [arr_t]

-- | Construct an unspecified value of the given type.
eBlank :: MonadBinder m => Type -> m (Exp (Rep m))
eBlank (Prim t) = return $ BasicOp $ SubExp $ Constant $ blankPrimValue t
eBlank (Array t shape _) = return $ BasicOp $ Scratch t $ shapeDims shape
eBlank Acc {} = error "eBlank: cannot create blank accumulator"
eBlank Mem {} = error "eBlank: cannot create blank memory"

-- | Sign-extend to the given integer type.
asIntS :: MonadBinder m => IntType -> SubExp -> m SubExp
asIntS = asInt SExt

-- | Zero-extend to the given integer type.
asIntZ :: MonadBinder m => IntType -> SubExp -> m SubExp
asIntZ = asInt ZExt

asInt ::
  MonadBinder m =>
  (IntType -> IntType -> ConvOp) ->
  IntType ->
  SubExp ->
  m SubExp
asInt ext to_it e = do
  e_t <- subExpType e
  case e_t of
    Prim (IntType from_it)
      | to_it == from_it -> return e
      | otherwise -> letSubExp s $ BasicOp $ ConvOp (ext from_it to_it) e
    _ -> error "asInt: wrong type"
  where
    s = case e of
      Var v -> baseString v
      _ -> "to_" ++ pretty to_it

-- | Apply a binary operator to several subexpressions.  A left-fold.
foldBinOp ::
  MonadBinder m =>
  BinOp ->
  SubExp ->
  [SubExp] ->
  m (Exp (Rep m))
foldBinOp _ ne [] =
  return $ BasicOp $ SubExp ne
foldBinOp bop ne (e : es) =
  eBinOp bop (pure $ BasicOp $ SubExp e) (foldBinOp bop ne es)

-- | True if all operands are true.
eAll :: MonadBinder m => [SubExp] -> m (Exp (Rep m))
eAll [] = pure $ BasicOp $ SubExp $ constant True
eAll (x : xs) = foldBinOp LogAnd x xs

-- | Create a two-parameter lambda whose body applies the given binary
-- operation to its arguments.  It is assumed that both argument and
-- result types are the same.  (This assumption should be fixed at
-- some point.)
binOpLambda ::
  (MonadBinder m, Bindable (Rep m)) =>
  BinOp ->
  PrimType ->
  m (Lambda (Rep m))
binOpLambda bop t = binLambda (BinOp bop) t t

-- | As 'binOpLambda', but for t'CmpOp's.
cmpOpLambda ::
  (MonadBinder m, Bindable (Rep m)) =>
  CmpOp ->
  m (Lambda (Rep m))
cmpOpLambda cop = binLambda (CmpOp cop) (cmpOpType cop) Bool

binLambda ::
  (MonadBinder m, Bindable (Rep m)) =>
  (SubExp -> SubExp -> BasicOp) ->
  PrimType ->
  PrimType ->
  m (Lambda (Rep m))
binLambda bop arg_t ret_t = do
  x <- newVName "x"
  y <- newVName "y"
  body <-
    buildBody_ . fmap pure $
      letSubExp "binlam_res" $ BasicOp $ bop (Var x) (Var y)
  return
    Lambda
      { lambdaParams =
          [ Param x (Prim arg_t),
            Param y (Prim arg_t)
          ],
        lambdaReturnType = [Prim ret_t],
        lambdaBody = body
      }

-- | Easily construct a 'Lambda' within a 'MonadBinder'.
mkLambda ::
  MonadBinder m =>
  [LParam (Rep m)] ->
  m Result ->
  m (Lambda (Rep m))
mkLambda params m = do
  (body, ret) <- buildBody . localScope (scopeOfLParams params) $ do
    res <- m
    ret <- mapM subExpType res
    pure (res, ret)
  pure $ Lambda params body ret

-- | Slice a full dimension of the given size.
sliceDim :: SubExp -> DimIndex SubExp
sliceDim d = DimSlice (constant (0 :: Int64)) d (constant (1 :: Int64))

-- | @fullSlice t slice@ returns @slice@, but with 'DimSlice's of
-- entire dimensions appended to the full dimensionality of @t@.  This
-- function is used to turn incomplete indexing complete, as required
-- by 'Index'.
fullSlice :: Type -> [DimIndex SubExp] -> Slice SubExp
fullSlice t slice =
  slice ++ map sliceDim (drop (length slice) $ arrayDims t)

-- | @ sliceAt t n slice@ returns @slice@ but with 'DimSlice's of the
-- outer @n@ dimensions prepended, and as many appended as to make it
-- a full slice.  This is a generalisation of 'fullSlice'.
sliceAt :: Type -> Int -> [DimIndex SubExp] -> Slice SubExp
sliceAt t n slice =
  fullSlice t $ map sliceDim (take n $ arrayDims t) ++ slice

-- | Like 'fullSlice', but the dimensions are simply numeric.
fullSliceNum :: Num d => [d] -> [DimIndex d] -> Slice d
fullSliceNum dims slice =
  slice ++ map (\d -> DimSlice 0 d 1) (drop (length slice) dims)

-- | Does the slice describe the full size of the array?  The most
-- obvious such slice is one that 'DimSlice's the full span of every
-- dimension, but also one that fixes all unit dimensions.
isFullSlice :: Shape -> Slice SubExp -> Bool
isFullSlice shape slice = and $ zipWith allOfIt (shapeDims shape) slice
  where
    allOfIt (Constant v) DimFix {} = oneIsh v
    allOfIt d (DimSlice _ n _) = d == n
    allOfIt _ _ = False

ifCommon :: [Type] -> IfDec ExtType
ifCommon ts = IfDec (staticShapes ts) IfNormal

-- | Conveniently construct a body that contains no bindings.
resultBody :: Bindable rep => [SubExp] -> Body rep
resultBody = mkBody mempty

-- | Conveniently construct a body that contains no bindings - but
-- this time, monadically!
resultBodyM ::
  MonadBinder m =>
  [SubExp] ->
  m (Body (Rep m))
resultBodyM = mkBodyM mempty

-- | Evaluate the action, producing a body, then wrap it in all the
-- bindings it created using 'addStm'.
insertStmsM ::
  (MonadBinder m) =>
  m (Body (Rep m)) ->
  m (Body (Rep m))
insertStmsM m = do
  (Body _ bnds res, otherbnds) <- collectStms m
  mkBodyM (otherbnds <> bnds) res

-- | Evaluate an action that produces a 'Result' and an auxiliary
-- value, then return the body constructed from the 'Result' and any
-- statements added during the action, along the auxiliary value.
buildBody ::
  MonadBinder m =>
  m (Result, a) ->
  m (Body (Rep m), a)
buildBody m = do
  ((res, v), stms) <- collectStms m
  body <- mkBodyM stms res
  pure (body, v)

-- | As 'buildBody', but there is no auxiliary value.
buildBody_ ::
  MonadBinder m =>
  m Result ->
  m (Body (Rep m))
buildBody_ m = fst <$> buildBody ((,()) <$> m)

-- | Change that result where evaluation of the body would stop.  Also
-- change type annotations at branches.
mapResult ::
  Bindable rep =>
  (Result -> Body rep) ->
  Body rep ->
  Body rep
mapResult f (Body _ bnds res) =
  let Body _ bnds2 newres = f res
   in mkBody (bnds <> bnds2) newres

-- | Instantiate all existential parts dimensions of the given
-- type, using a monadic action to create the necessary t'SubExp's.
-- You should call this function within some monad that allows you to
-- collect the actions performed (say, 'Writer').
instantiateShapes ::
  Monad m =>
  (Int -> m SubExp) ->
  [TypeBase ExtShape u] ->
  m [TypeBase Shape u]
instantiateShapes f ts = evalStateT (mapM instantiate ts) M.empty
  where
    instantiate t = do
      shape <- mapM instantiate' $ shapeDims $ arrayShape t
      return $ t `setArrayShape` Shape shape
    instantiate' (Ext x) = do
      m <- get
      case M.lookup x m of
        Just se -> return se
        Nothing -> do
          se <- lift $ f x
          put $ M.insert x se m
          return se
    instantiate' (Free se) = return se

instantiateShapes' ::
  MonadFreshNames m =>
  [TypeBase ExtShape u] ->
  m ([TypeBase Shape u], [Ident])
instantiateShapes' ts =
  -- Carefully ensure that the order of idents we produce corresponds
  -- to their existential index.
  second (map snd . sortOn fst)
    <$> runWriterT (instantiateShapes instantiate ts)
  where
    instantiate x = do
      v <- lift $ newIdent "size" $ Prim int64
      tell [(x, v)]
      return $ Var $ identName v

removeExistentials :: ExtType -> Type -> Type
removeExistentials t1 t2 =
  t1
    `setArrayDims` zipWith
      nonExistential
      (shapeDims $ arrayShape t1)
      (arrayDims t2)
  where
    nonExistential (Ext _) dim = dim
    nonExistential (Free dim) _ = dim

-- | Can be used as the definition of 'mkLetNames' for a 'Bindable'
-- instance for simple representations.
simpleMkLetNames ::
  ( ExpDec rep ~ (),
    LetDec rep ~ Type,
    MonadFreshNames m,
    TypedOp (Op rep),
    HasScope rep m
  ) =>
  [VName] ->
  Exp rep ->
  m (Stm rep)
simpleMkLetNames names e = do
  et <- expExtType e
  (ts, shapes) <- instantiateShapes' et
  let shapeElems = [PatElem shape shapet | Ident shape shapet <- shapes]
  let valElems = zipWith PatElem names ts
  return $ Let (Pattern shapeElems valElems) (defAux ()) e

-- | Instances of this class can be converted to Futhark expressions
-- within a 'MonadBinder'.
class ToExp a where
  toExp :: MonadBinder m => a -> m (Exp (Rep m))

instance ToExp SubExp where
  toExp = return . BasicOp . SubExp

instance ToExp VName where
  toExp = return . BasicOp . SubExp . Var

-- | A convenient composition of 'letSubExp' and 'toExp'.
toSubExp :: (MonadBinder m, ToExp a) => String -> a -> m SubExp
toSubExp s e = letSubExp s =<< toExp e
