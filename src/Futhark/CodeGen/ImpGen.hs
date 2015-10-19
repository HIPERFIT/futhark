{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts, LambdaCase #-}
module Futhark.CodeGen.ImpGen
  ( -- * Entry Points
    compileProg
  , compileProgSimply

    -- * Pluggable Compiler
  , ExpCompiler
  , ExpCompilerResult (..)
  , CopyCompiler
  , Operations (..)
  , defaultOperations
  , Destination (..)
  , ValueDestination (..)
  , ArrayMemoryDestination (..)
  , MemLocation (..)
  , MemEntry (..)
  , ScalarEntry (..)

    -- * Monadic Compiler Interface
  , ImpM
  , Env (envVtable, envDefaultSpace)
  , subImpM
  , subImpM_
  , emit
  , collect
  , comment
  , VarEntry (..)

    -- * Lookups
  , lookupArray
  , arrayLocation
  , lookupMemory

    -- * Building Blocks
  , compileSubExp
  , compileResultSubExp
  , subExpToDimSize
  , sizeToExp
  , sizeToScalExp
  , declaringLParams
  , declaringVarEntry
  , withParams
  , declaringBasicVar
  , withBasicVar
  , compileBody
  , compileBindings
  , writeExp
  , indexArray
  , fullyIndexArray
  , fullyIndexArray'
  , varIndex
  , basicScalarSize
  , scalExpToImpExp
  , dimSizeToExp
  , destinationFromParam
  , destinationFromParams
  , copyElementWise

  )
  where

import Control.Applicative
import Control.Monad.RWS    hiding (mapM, forM)
import Control.Monad.State  hiding (mapM, forM)
import Control.Monad.Writer hiding (mapM, forM)
import Control.Monad.Except hiding (mapM, forM)
import Data.Either
import Data.Traversable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe
import Data.List

import qualified Futhark.Analysis.AlgSimplify as AlgSimplify

import Prelude hiding (div, quot, mod, rem, mapM)

import Futhark.Analysis.ScalExp as SE
import qualified Futhark.CodeGen.ImpCode as Imp
import Futhark.CodeGen.ImpCode
  (Count (..),
   Bytes, Elements,
   bytes, elements,
   withElemType)
import Futhark.Representation.ExplicitMemory
import qualified Futhark.Representation.ExplicitMemory.IndexFunction.Unsafe as IxFun
import Futhark.MonadFreshNames
import Futhark.Util
import Futhark.Util.IntegralExp

-- | A substitute expression compiler, tried before the main
-- expression compilation function.
type ExpCompiler op = Destination -> Exp -> ImpM op (ExpCompilerResult op)

-- | The result of the substitute expression compiler.
data ExpCompilerResult op =
      CompileBindings [Binding]
    -- ^ New bindings.  Note that the bound expressions will
    -- themselves be compiled using the expression compiler.
    | CompileExp Exp
    -- ^ A new expression (or possibly the same as the input) - this
    -- will not be passed back to the expression compiler, but instead
    -- processed with the default action.
    | Done
    -- ^ Some code was added via the monadic interface.

type CopyCompiler op = BasicType
                       -> MemLocation
                       -> MemLocation
                       -> Count Elements -- ^ Number of elements of the source.
                       -> ImpM op ()

data Operations op = Operations { opsExpCompiler :: ExpCompiler op
                                , opsCopyCompiler :: CopyCompiler op
                                }

-- | An operations set for which the expression compiler always
-- returns 'CompileExp'.
defaultOperations :: Operations op
defaultOperations = Operations { opsExpCompiler = const $ return . CompileExp
                               , opsCopyCompiler = defaultCopy
                               }

-- | When an array is declared, this is where it is stored.
data MemLocation = MemLocation VName [Imp.DimSize] IxFun.IxFun
                   deriving (Show)

data ArrayEntry = ArrayEntry {
    entryArrayLocation :: MemLocation
  , entryArrayElemType :: BasicType
  , entryArrayShape    :: [Imp.DimSize]
  }

data MemEntry = MemEntry {
      entryMemSize  :: Imp.MemSize
    , entryMemSpace :: Imp.Space
  }

data ScalarEntry = ScalarEntry {
    entryScalarType    :: BasicType
  }

-- | Every non-scalar variable must be associated with an entry.
data VarEntry = ArrayVar ArrayEntry
              | ScalarVar ScalarEntry
              | MemVar MemEntry

-- | When compiling a body, this is a description of where the result
-- should end up.
newtype Destination = Destination { valueDestinations :: [ValueDestination] }
                    deriving (Show)

data ValueDestination = ScalarDestination VName
                      | ArrayElemDestination VName BasicType Imp.Space (Count Bytes)
                      | MemoryDestination VName (Maybe VName)
                      | ArrayDestination ArrayMemoryDestination [Maybe VName]
                      deriving (Show)

-- | If the given value destination if a 'ScalarDestination', return
-- the variable name.  Otherwise, 'Nothing'.
fromScalarDestination :: ValueDestination -> Maybe VName
fromScalarDestination (ScalarDestination name) = Just name
fromScalarDestination _                        = Nothing

data ArrayMemoryDestination = SetMemory VName (Maybe VName)
                            | CopyIntoMemory MemLocation
                            deriving (Show)

data Env op = Env {
    envVtable :: HM.HashMap VName VarEntry
  , envExpCompiler :: ExpCompiler op
  , envCopyCompiler :: CopyCompiler op
  , envDefaultSpace :: Imp.Space
  }

newEnv :: Operations op -> Imp.Space -> Env op
newEnv ops ds = Env { envVtable = HM.empty
                    , envExpCompiler = opsExpCompiler ops
                    , envCopyCompiler = opsCopyCompiler ops
                    , envDefaultSpace = ds
                    }

newtype ImpM op a = ImpM (RWST (Env op) (Imp.Code op) VNameSource (Either String) a)
  deriving (Functor, Applicative, Monad,
            MonadState VNameSource,
            MonadReader (Env op),
            MonadWriter (Imp.Code op),
            MonadError String)

instance MonadFreshNames (ImpM op) where
  getNameSource = get
  putNameSource = put

instance HasTypeEnv (ImpM op) where
  askTypeEnv = HM.map entryType <$> asks envVtable
    where entryType (MemVar memEntry) =
            Mem (dimSizeToSubExp $ entryMemSize memEntry) (entryMemSpace memEntry)
          entryType (ArrayVar arrayEntry) =
            Array
            (entryArrayElemType arrayEntry)
            (Shape $ map dimSizeToSubExp $ entryArrayShape arrayEntry)
            Nonunique -- Arbitrary
          entryType (ScalarVar scalarEntry) =
            Basic $ entryScalarType scalarEntry

          dimSizeToSubExp (Imp.ConstSize n) =
            Constant $ IntVal $ fromIntegral n
          dimSizeToSubExp (Imp.VarSize v) =
            Var v

runImpM :: ImpM op a
        -> Operations op -> Imp.Space -> VNameSource
        -> Either String (a, VNameSource, Imp.Code op)
runImpM (ImpM m) comp = runRWST m . newEnv comp

subImpM_ :: Operations op' -> ImpM op' a
         -> ImpM op (Imp.Code op')
subImpM_ ops m = snd <$> subImpM ops m

subImpM :: Operations op' -> ImpM op' a
        -> ImpM op (a, Imp.Code op')
subImpM ops (ImpM m) = do
  env <- ask
  src <- getNameSource
  case runRWST m env { envExpCompiler = opsExpCompiler ops
                     , envCopyCompiler = opsCopyCompiler ops }
       src of
    Left err -> throwError err
    Right (x, src', code) -> do
      putNameSource src'
      return (x, code)

-- | Execute a code generation action, returning the code that was
-- emitted.
collect :: ImpM op () -> ImpM op (Imp.Code op)
collect m = pass $ do
  ((), code) <- listen m
  return (code, const mempty)

-- | Execute a code generation action, wrapping the generated code
-- within a 'Imp.Comment' with the given description.
comment :: String -> ImpM op () -> ImpM op ()
comment desc m = do code <- collect m
                    emit $ Imp.Comment desc code

-- | Emit some generated imperative code.
emit :: Imp.Code op -> ImpM op ()
emit = tell

compileProg :: Operations op -> Imp.Space
            -> Prog -> Either String (Imp.Program op)
compileProg ops ds prog =
  Imp.Program <$> snd <$> mapAccumLM (compileFunDec ops ds) src (progFunctions prog)
  where src = newNameSourceForProg prog

-- | 'compileProg' with 'defaultOperations' and 'DefaultSpace'.
compileProgSimply :: Prog -> Either String (Imp.Program ())
compileProgSimply = compileProg defaultOperations Imp.DefaultSpace

compileInParam :: FParam -> ImpM op (Either Imp.Param ArrayDecl)
compileInParam fparam = case t of
  Basic bt ->
    return $ Left $ Imp.ScalarParam name bt
  Mem size space ->
    Left <$> (Imp.MemParam name <$> subExpToDimSize size <*> pure space)
  Array bt shape _ -> do
    shape' <- mapM subExpToDimSize $ shapeDims shape
    return $ Right $ ArrayDecl name bt shape' $
      MemLocation mem shape' ixfun
  where name = paramName fparam
        t    = paramType fparam
        MemSummary mem ixfun = paramLore fparam

data ArrayDecl = ArrayDecl VName BasicType [Imp.DimSize] MemLocation

fparamSizes :: FParam -> HS.HashSet VName
fparamSizes fparam
  | Mem (Var size) _ <- paramType fparam = HS.singleton size
  | otherwise = HS.fromList $ mapMaybe name $ arrayDims $ paramType fparam
  where name (Var v) = Just v
        name _       = Nothing

compileInParams :: [FParam]
                -> ImpM op ([Imp.Param], [ArrayDecl], [Imp.ValueDecl])
compileInParams params = do
  (inparams, arraydecls) <- liftM partitionEithers $ mapM compileInParam params
  let findArray x = find (isArrayDecl x) arraydecls
      sizes = mconcat $ map fparamSizes params
      mkArg fparam =
        case (findArray $ paramName fparam, paramType fparam) of
          (Just (ArrayDecl _ bt shape (MemLocation mem _ _)), _) ->
            Just $ Imp.ArrayValue mem bt shape
          (_, Basic bt)
            | paramName fparam `HS.member` sizes ->
              Nothing
            | otherwise ->
              Just $ Imp.ScalarValue bt $ paramName fparam
          _ ->
            Nothing
      args = mapMaybe mkArg params
  return (inparams, arraydecls, args)
  where isArrayDecl x (ArrayDecl y _ _ _) = x == y

compileOutParams :: RetType
                 -> ImpM op ([Imp.ValueDecl], [Imp.Param], Destination)
compileOutParams rts = do
  ((valdecls, dests), outparams) <-
    runWriterT $ evalStateT (mapAndUnzipM mkParam rts) (HM.empty, HM.empty)
  return (valdecls, outparams, Destination dests)
  where imp = lift . lift

        mkParam (ReturnsMemory {}) =
          throwError "Functions may not explicitly return memory blocks."
        mkParam (ReturnsScalar t) = do
          out <- imp $ newVName "scalar_out"
          tell [Imp.ScalarParam out t]
          return (Imp.ScalarValue t out, ScalarDestination out)
        mkParam (ReturnsArray t shape _ lore) = do
          space <- asks envDefaultSpace
          (memout, memdestf) <- case lore of
            ReturnsNewBlock x -> do
              memout <- imp $ newVName "out_mem"
              (sizeout, destmemsize) <- ensureMemSizeOut x
              tell [Imp.MemParam memout (Imp.VarSize sizeout) space]
              return (memout, const $ SetMemory memout destmemsize)
            ReturnsInBlock memout ixfun ->
              return (memout,
                      \resultshape ->
                      CopyIntoMemory $
                      MemLocation memout resultshape ixfun)
          (resultshape, destresultshape) <-
            mapAndUnzipM inspectExtDimSize $ extShapeDims shape
          let memdest = memdestf resultshape
          return (Imp.ArrayValue memout t resultshape,
                  ArrayDestination memdest destresultshape)

        inspectExtDimSize (Ext x) = do
          (memseen,arrseen) <- get
          case HM.lookup x arrseen of
            Nothing -> do
              out <- imp $ newVName "out_arrsize"
              tell [Imp.ScalarParam out Int]
              put (memseen, HM.insert x out arrseen)
              return (Imp.VarSize out, Just out)
            Just out ->
              return (Imp.VarSize out, Nothing)
        inspectExtDimSize (Free se) = do
          se' <- imp $ subExpToDimSize se
          return (se', Nothing)

        -- | Return the name of the out-parameter for the memory size
        -- 'x', creating it if it does not already exist.
        ensureMemSizeOut x = do
          (memseen, arrseen) <- get
          case HM.lookup x memseen of
            Nothing      -> do sizeout <- imp $ newVName "out_memsize"
                               tell [Imp.ScalarParam sizeout Int]
                               put (HM.insert x sizeout memseen, arrseen)
                               return (sizeout, Just sizeout)
            Just sizeout -> return (sizeout, Nothing)

compileFunDec :: Operations op -> Imp.Space
              -> VNameSource
              -> FunDec
              -> Either String (VNameSource, (Name, Imp.Function op))
compileFunDec ops ds src (FunDec fname rettype params body) = do
  ((outparams, inparams, results, args), src', body') <-
    runImpM compile ops ds src
  return (src',
          (fname,
           Imp.Function outparams inparams body' results args))
  where compile = do
          (inparams, arraydecls, args) <- compileInParams params
          (results, outparams, dests) <- compileOutParams rettype
          withParams inparams $
            withArrays arraydecls $
            compileBody dests body
          return (outparams, inparams, results, args)

compileBody :: Destination -> Body -> ImpM op ()
compileBody (Destination dest) (Body _ bnds ses) =
  compileBindings bnds $ zipWithM_ compileResultSubExp dest ses

compileLoopBody :: [VName] -> Body -> ImpM op (Imp.Code op)
compileLoopBody mergenames (Body _ bnds ses) = do
  -- We cannot write the results to the merge parameters immediately,
  -- as some of the results may actually *be* merge parameters, and
  -- would thus be clobbered.  Therefore, we first copy to new
  -- variables mirroring the merge parameters, and then copy this
  -- buffer to the merge parameters.  This is efficient, because the
  -- operations are all scalar operations.
  tmpnames <- mapM (newVName . (++"_tmp") . baseString) mergenames
  collect $ compileBindings bnds $ do
    copy_to_merge_params <- forM (zip3 mergenames tmpnames ses) $ \(d,tmp,se) ->
      subExpType se >>= \case
        Basic bt  -> do
          emit $ Imp.DeclareScalar tmp bt
          emit $ Imp.SetScalar tmp $ compileSubExp se
          return $ emit $ Imp.SetScalar d $ Imp.ScalarVar tmp
        Mem _ space | Var v <- se -> do
          emit $ Imp.DeclareMem tmp space
          emit $ Imp.SetMem tmp v
          return $ emit $ Imp.SetMem d tmp
        _ -> return $ return ()
    sequence_ copy_to_merge_params

compileBindings :: [Binding] -> ImpM op a -> ImpM op a
compileBindings []     m = m
compileBindings (Let pat _ e:bs) m =
  declaringVars (patternElements pat) $ do
    dest <- destinationFromPattern pat
    compileExp dest e $ compileBindings bs m

compileExp :: Destination -> Exp -> ImpM op a -> ImpM op a
compileExp targets e m = do
  ec <- asks envExpCompiler
  res <- ec targets e
  case res of
    CompileBindings bnds -> compileBindings bnds m
    CompileExp e'        -> do defCompileExp targets e'
                               m
    Done                 -> m

defCompileExp :: Destination -> Exp -> ImpM op ()

defCompileExp dest (If cond tbranch fbranch _) = do
  tcode <- collect $ compileBody dest tbranch
  fcode <- collect $ compileBody dest fbranch
  emit $ Imp.If (compileSubExp cond) tcode fcode

defCompileExp dest (Apply fname args _) = do
  targets <- funcallTargets dest
  emit =<<
    (Imp.Call targets fname <$>
     map compileSubExp <$>
     filterM subExpNotArray (map fst args))

defCompileExp targets (PrimOp op) = defCompilePrimOp targets op

defCompileExp targets (LoopOp op) = defCompileLoopOp targets op

defCompileExp _ (SegOp op) =
  throwError $
  "ImpGen called on Segmented Operator, this is not supported. " ++
  pretty (SegOp op)

defCompilePrimOp :: Destination -> PrimOp -> ImpM op ()

defCompilePrimOp (Destination [target]) (SubExp se) =
  compileResultSubExp target se

defCompilePrimOp (Destination [target]) (Not e) =
  writeExp target $ Imp.UnOp Imp.Not $ compileSubExp e

defCompilePrimOp (Destination [target]) (Complement e) =
  writeExp target $ Imp.UnOp Imp.Complement $ compileSubExp e

defCompilePrimOp (Destination [target]) (Negate e) =
  writeExp target $ Imp.UnOp Imp.Negate $ compileSubExp e

defCompilePrimOp (Destination [target]) (Abs e) =
  writeExp target $ Imp.UnOp Imp.Abs $ compileSubExp e

defCompilePrimOp (Destination [target]) (Signum e) =
  writeExp target $ Imp.UnOp Imp.Signum $ compileSubExp e

defCompilePrimOp (Destination [target]) (BinOp bop x y _) =
  writeExp target $ Imp.BinOp bop (compileSubExp x) (compileSubExp y)

defCompilePrimOp (Destination [_]) (Assert e loc) =
  emit $ Imp.Assert (compileSubExp e) loc

defCompilePrimOp (Destination [MemoryDestination mem size]) (Alloc e space) = do
  emit $ Imp.Allocate mem (bytes e') space
  case size of Just size' -> emit $ Imp.SetScalar size' e'
               Nothing    -> return ()
  where e' = compileSubExp e

defCompilePrimOp (Destination [target]) (Index _ src idxs) = do
  t <- lookupType src
  when (length idxs == arrayRank t) $ do
    (srcmem, space, srcoffset) <-
      fullyIndexArray src $ map (`SE.subExpToScalExp` Int) idxs
    writeExp target $ Imp.Index srcmem srcoffset (elemType t) space

defCompilePrimOp
  (Destination [ArrayDestination (CopyIntoMemory destlocation) _])
  (Replicate n se) = do
    set <- subExpType se
    let elemt = elemType set
    i <- newVName "i"
    declaringLoopVar i $
      if basicType set then do
        (targetmem, space, targetoffset) <-
          fullyIndexArray' destlocation [varIndex i] $ elemType set
        emit $ Imp.For i (compileSubExp n) $
          Imp.Write targetmem targetoffset (elemType set) space $ compileSubExp se
        else case se of
        Constant {} ->
          throwError "Array value in replicate cannot be constant."
        Var v -> do
          targetloc <-
            indexArray destlocation [varIndex i]
          src_array <- lookupArray v
          let src_elements = arrayOuterSize src_array
              src_loc = entryArrayLocation src_array
          emit =<< (Imp.For i (compileSubExp n) <$>
            collect (copy elemt targetloc src_loc src_elements))

defCompilePrimOp (Destination [_]) (Scratch {}) =
  return ()

defCompilePrimOp
  (Destination [ArrayDestination (CopyIntoMemory memlocation) _])
  (Iota n) = do
    i <- newVName "i"
    declaringLoopVar i $ do
      (targetmem, space, targetoffset) <-
        fullyIndexArray' memlocation [varIndex i] Int
      emit $ Imp.For i (compileSubExp n) $
        Imp.Write targetmem targetoffset Int space $ Imp.ScalarVar i

defCompilePrimOp (Destination [target]) (Copy src) =
  compileResultSubExp target $ Var src

defCompilePrimOp _ (Split {}) =
  return () -- Yes, really.

defCompilePrimOp
  (Destination [ArrayDestination (CopyIntoMemory (MemLocation destmem destshape destixfun)) _])
  (Concat _ x ys _) = do
    et <- elemType <$> lookupType x
    offs_glb <- newVName "tmp_offs"
    withBasicVar offs_glb Int $ do
      emit $ Imp.DeclareScalar offs_glb Int
      emit $ Imp.SetScalar offs_glb $ Imp.Constant $ IntVal 0
      let destloc = MemLocation destmem destshape
                    (IxFun.offsetIndex destixfun $ SE.Id offs_glb Int)

      forM_ (x:ys) $ \y -> do
          yentry <- lookupArray y
          let srcloc = entryArrayLocation yentry
              rows = case entryArrayShape yentry of
                      []  -> error $ "defCompilePrimOp Concat: empty array shape for " ++ pretty y
                      r:_ -> innerExp $ dimSizeToExp r
          copy et destloc srcloc (arrayOuterSize yentry)
          emit $ Imp.SetScalar offs_glb $ Imp.ScalarVar offs_glb + rows

defCompilePrimOp
  (Destination [ArrayDestination (CopyIntoMemory memlocation) _])
  (ArrayLit es rt) = do
    let rowshape = map (elements . compileSubExp) $ arrayDims rt
        elements_per_row = product $ take 1 rowshape
    forM_ (zip [0..] es) $ \(i,e) ->
      if basicType rt then do
        (targetmem, space, targetoffset) <-
          fullyIndexArray' memlocation [constIndex i] $ elemType rt
        emit $ Imp.Write targetmem targetoffset et space $ compileSubExp e
      else case e of
        Constant {} ->
          throwError "defCompilePrimOp ArrayLit: Cannot have array constants."
        Var v -> do
          targetloc <- indexArray memlocation [SE.Val $ IntVal $ fromIntegral i]
          srcloc <- arrayLocation v
          copy et targetloc srcloc elements_per_row
  where et = elemType rt

defCompilePrimOp _ (Rearrange {}) =
  return ()

defCompilePrimOp _ (Reshape {}) =
  return ()

defCompilePrimOp _ (Stripe {}) =
  return ()

defCompilePrimOp _ (Unstripe {}) =
  return ()

defCompilePrimOp (Destination dests) (Partition _ n flags value_arrs)
  | (sizedests, arrdest) <- splitAt n dests,
    Just sizenames <- mapM fromScalarDestination sizedests,
    Just destlocs <- mapM arrDestLoc arrdest = do
  i <- newVName "i"
  declaringLoopVar i $ do
    outer_dim <- compileSubExp <$> arraySize 0 <$> lookupType flags
    -- We will use 'i' to index the flag array and the value array.
    -- Note that they have the same outer size ('outer_dim').
    (flagmem, space, flagoffset) <- fullyIndexArray flags [varIndex i]

    -- First, for each of the 'n' output arrays, we compute the final
    -- size.  This is done by iterating through the flag array, but
    -- first we declare scalars to hold the size.  We do this by
    -- creating a mapping from equivalence classes to the name of the
    -- scalar holding the size.
    let sizes = HM.fromList $ zip [0..n-1] sizenames

    -- We initialise ecah size to zero.
    forM_ sizenames $ \sizename ->
      emit $ Imp.SetScalar sizename 0

    -- Now iterate across the flag array, storing each element in
    -- 'eqclass', then comparing it to the known classes and increasing
    -- the appropriate size variable.
    eqclass <- newVName "eqclass"
    emit $ Imp.DeclareScalar eqclass Int
    let mkSizeLoopBody code c sizevar =
          Imp.If (Imp.BinOp Equal (Imp.ScalarVar eqclass) (fromIntegral c))
          (Imp.SetScalar sizevar $ Imp.ScalarVar sizevar + 1)
          code
        sizeLoopBody = HM.foldlWithKey' mkSizeLoopBody Imp.Skip sizes
    emit $ Imp.For i outer_dim $
      Imp.SetScalar eqclass (Imp.Index flagmem flagoffset Int space) <>
      sizeLoopBody

    -- We can now compute the starting offsets of each of the
    -- partitions, creating a map from equivalence class to its
    -- corresponding offset.
    offsets <- flip evalStateT (Imp.Constant $ IntVal 0) $ forM sizes $ \size -> do
      cur_offset <- get
      partition_offset <- lift $ newVName "partition_offset"
      lift $ emit $ Imp.DeclareScalar partition_offset Int
      lift $ emit $ Imp.SetScalar partition_offset cur_offset
      put $ Imp.ScalarVar partition_offset + Imp.ScalarVar size
      return partition_offset

    -- We create the memory location we use when writing a result
    -- element.  This is basically the index function of 'destloc', but
    -- with a dynamic offset, stored in 'partition_cur_offset'.
    partition_cur_offset <- newVName "partition_cur_offset"
    emit $ Imp.DeclareScalar partition_cur_offset Int

    -- Finally, we iterate through the data array and flag array in
    -- parallel, and put each element where it is supposed to go.  Note
    -- that after writing to a partition, we increase the corresponding
    -- offset.
    ets <- mapM (fmap elemType . lookupType) value_arrs
    srclocs <- mapM arrayLocation value_arrs
    copy_elements <- forM (zip3 destlocs ets srclocs) $ \(destloc,et,srcloc) ->
      copyElem et
      destloc [varIndex partition_cur_offset]
      srcloc [varIndex i]
    let mkWriteLoopBody code c offsetvar =
          Imp.If (Imp.BinOp Equal (Imp.ScalarVar eqclass) (fromIntegral c))
          (Imp.SetScalar partition_cur_offset
             (Imp.ScalarVar offsetvar)
           <>
           mconcat copy_elements
           <>
           Imp.SetScalar offsetvar
             (Imp.ScalarVar offsetvar + 1))
          code
        writeLoopBody = HM.foldlWithKey' mkWriteLoopBody Imp.Skip offsets
    emit $ Imp.For i outer_dim $
      Imp.SetScalar eqclass (Imp.Index flagmem flagoffset Int space) <>
      writeLoopBody
    return ()
  where arrDestLoc (ArrayDestination (CopyIntoMemory destloc) _) =
          Just destloc
        arrDestLoc _ =
          Nothing

defCompilePrimOp (Destination []) _ = return () -- No arms, no cake.

defCompilePrimOp target e =
  throwError $ "ImpGen.defCompilePrimOp: Invalid target\n  " ++
  show target ++ "\nfor expression\n  " ++ pretty e

defCompileLoopOp :: Destination -> LoopOp -> ImpM op ()

defCompileLoopOp (Destination dest) (DoLoop res merge form body) =
  declaringFParams mergepat $ do
    forM_ merge $ \(p, se) -> do
      na <- subExpNotArray se
      when na $
        compileScalarSubExpTo (ScalarDestination $ paramName p) se
    let (bindForm, emitForm) =
          case form of
            ForLoop i bound ->
              (declaringLoopVar i,
               emit . Imp.For i (compileSubExp bound))
            WhileLoop cond ->
              (id,
               emit . Imp.While (Imp.ScalarVar cond))

    bindForm $ do
      body' <- compileLoopBody mergenames body
      emitForm body'
    zipWithM_ compileResultSubExp dest $ map Var res
    where mergepat = map fst merge
          mergenames = map paramName mergepat

defCompileLoopOp _ (Map {}) = soacError

defCompileLoopOp _ (ConcatMap {}) = soacError

defCompileLoopOp _ (Scan {}) = soacError

defCompileLoopOp _ (Redomap {}) = soacError

defCompileLoopOp _ (Stream {}) = soacError

defCompileLoopOp _ (Reduce {}) = soacError

defCompileLoopOp _ (Kernel {}) = soacError

defCompileLoopOp _ (ReduceKernel {}) = soacError

soacError :: ImpM op a
soacError = throwError "SOAC encountered in code generator; should have been removed by first-order transform."

writeExp :: ValueDestination -> Imp.Exp -> ImpM op ()
writeExp (ScalarDestination target) e =
  emit $ Imp.SetScalar target e
writeExp (ArrayElemDestination destmem bt space elemoffset) e =
  emit $ Imp.Write destmem elemoffset bt space e
writeExp target e =
  throwError $ "Cannot write " ++ pretty e ++ " to " ++ show target

insertInVtable :: VName -> VarEntry -> Env op -> Env op
insertInVtable name entry env =
  env { envVtable = HM.insert name entry $ envVtable env }

withArray :: ArrayDecl -> ImpM op a -> ImpM op a
withArray (ArrayDecl name bt shape location) m = do
  let entry = ArrayVar ArrayEntry {
          entryArrayLocation = location
        , entryArrayElemType = bt
        , entryArrayShape    = shape
        }
  local (insertInVtable name entry) m

withArrays :: [ArrayDecl] -> ImpM op a -> ImpM op a
withArrays = flip $ foldr withArray

withParams :: [Imp.Param] -> ImpM op a -> ImpM op a
withParams = flip $ foldr withParam

withParam :: Imp.Param -> ImpM op a -> ImpM op a
withParam (Imp.MemParam name memsize space) =
  let entry = MemVar MemEntry {
          entryMemSize = memsize
        , entryMemSpace = space
        }
  in local $ insertInVtable name entry
withParam (Imp.ScalarParam name bt) =
  let entry = ScalarVar ScalarEntry { entryScalarType = bt
                                    }
  in local $ insertInVtable name entry

declaringVars :: [PatElem] -> ImpM op a -> ImpM op a
declaringVars = flip $ foldr declaringVar

declaringFParams :: [FParam] -> ImpM op a -> ImpM op a
declaringFParams = flip $ foldr $ declaringVar . toPatElem
  where toPatElem fparam = PatElem (paramIdent fparam) BindVar (paramLore fparam)

declaringLParams :: [LParam] -> ImpM op a -> ImpM op a
declaringLParams = flip $ foldr $ declaringVar . toPatElem
  where toPatElem fparam = PatElem (paramIdent fparam) BindVar (paramLore fparam)

declaringVarEntry :: VName -> VarEntry -> ImpM op a -> ImpM op a
declaringVarEntry name entry m = do
  case entry of
    MemVar entry' ->
      emit $ Imp.DeclareMem name $ entryMemSpace entry'
    ScalarVar entry' ->
      emit $ Imp.DeclareScalar name $ entryScalarType entry'
    ArrayVar _ ->
      return ()
  local (insertInVtable name entry) m

declaringVar :: PatElem -> ImpM op a -> ImpM op a
declaringVar patElem m =
  case patElemType patElem of
    Basic bt -> do
      let entry = ScalarVar ScalarEntry { entryScalarType    = bt
                                        }
      declaringVarEntry name entry m
    Mem size space -> do
      size' <- subExpToDimSize size
      let entry = MemVar MemEntry {
              entryMemSize = size'
            , entryMemSpace = space
            }
      declaringVarEntry name entry m
    Array bt shape _ -> do
      shape' <- mapM subExpToDimSize $ shapeDims shape
      let MemSummary mem ixfun = patElemLore patElem
          location = MemLocation mem shape' ixfun
          entry = ArrayVar ArrayEntry {
              entryArrayLocation = location
            , entryArrayElemType = bt
            , entryArrayShape    = shape'
            }
      declaringVarEntry name entry m
  where name = patElemName patElem

declaringBasicVar :: VName -> BasicType -> ImpM op a -> ImpM op a
declaringBasicVar name bt =
  declaringVarEntry name $ ScalarVar $ ScalarEntry bt

withBasicVar :: VName -> BasicType -> ImpM op a -> ImpM op a
withBasicVar name bt =
  local (insertInVtable name $ ScalarVar $ ScalarEntry bt)

declaringLoopVars :: [VName] -> ImpM op a -> ImpM op a
declaringLoopVars = flip $ foldr declaringLoopVar

declaringLoopVar :: VName -> ImpM op a -> ImpM op a
declaringLoopVar name =
  withBasicVar name Int

-- | Remove the array targets.
funcallTargets :: Destination -> ImpM op [VName]
funcallTargets (Destination dests) =
  liftM concat $ mapM funcallTarget dests
  where funcallTarget (ScalarDestination name) =
          return [name]
        funcallTarget (ArrayElemDestination {}) =
          throwError "Cannot put scalar function return in-place yet." -- FIXME
        funcallTarget (ArrayDestination (CopyIntoMemory _) shape) =
          return $ catMaybes shape
        funcallTarget (ArrayDestination (SetMemory mem memsize) shape) =
          return $ maybeToList memsize ++ [mem] ++ catMaybes shape
        funcallTarget (MemoryDestination name size) =
          return $ maybeToList size ++ [name]

subExpToDimSize :: SubExp -> ImpM op Imp.DimSize
subExpToDimSize (Var v) =
  return $ Imp.VarSize v
subExpToDimSize (Constant (IntVal i)) =
  return $ Imp.ConstSize $ fromIntegral i
subExpToDimSize (Constant {}) =
  throwError "Size subexp is not a non-integer constant."

dimSizeToExp :: Imp.DimSize -> Count Elements
dimSizeToExp = elements . sizeToExp

memSizeToExp :: Imp.MemSize -> Count Bytes
memSizeToExp = bytes . sizeToExp

sizeToExp :: Imp.Size -> Imp.Exp
sizeToExp (Imp.VarSize v)   = Imp.ScalarVar v
sizeToExp (Imp.ConstSize x) = Imp.Constant $ IntVal $ fromIntegral x

sizeToScalExp :: Imp.Size -> SE.ScalExp
sizeToScalExp (Imp.VarSize v)   = SE.Id v Int
sizeToScalExp (Imp.ConstSize x) = SE.Val $ IntVal x

compileResultSubExp :: ValueDestination -> SubExp -> ImpM op ()

compileResultSubExp (ScalarDestination name) se =
  compileScalarSubExpTo (ScalarDestination name) se

compileResultSubExp (ArrayElemDestination destmem bt space elemoffset) se =
  emit $ Imp.Write destmem elemoffset bt space $ compileSubExp se

compileResultSubExp (MemoryDestination mem memsizetarget) (Var v) = do
  MemEntry memsize _ <- lookupMemory v
  emit $ Imp.SetMem mem v
  case memsizetarget of
    Nothing ->
      return ()
    Just memsizetarget' ->
      emit $ Imp.SetScalar memsizetarget' $
      innerExp $ dimSizeToExp memsize

compileResultSubExp (MemoryDestination {}) (Constant {}) =
  throwError "Memory destination result subexpression cannot be a constant."

compileResultSubExp (ArrayDestination memdest shape) (Var v) = do
  et <- elemType <$> lookupType v
  arr <- lookupArray v
  let MemLocation srcmem srcshape srcixfun = entryArrayLocation arr
      elements_to_copy = arrayOuterSize arr
  srcmemsize <- entryMemSize <$> lookupMemory srcmem
  case memdest of
    CopyIntoMemory (MemLocation destmem destshape destixfun)
      | destmem == srcmem && destixfun == srcixfun ->
        return ()
      | otherwise ->
          copy et
          (MemLocation destmem destshape destixfun)
          (MemLocation srcmem srcshape srcixfun)
          elements_to_copy
    SetMemory mem memsize -> do
      emit $ Imp.SetMem mem srcmem
      case memsize of Nothing -> return ()
                      Just memsize' -> emit $ Imp.SetScalar memsize' $
                                       innerExp $ memSizeToExp srcmemsize
  zipWithM_ maybeSetShape shape $ entryArrayShape arr
  where maybeSetShape Nothing _ =
          return ()
        maybeSetShape (Just dim) size =
          emit $ Imp.SetScalar dim $ innerExp $ dimSizeToExp size

compileResultSubExp (ArrayDestination {}) (Constant {}) =
  throwError "Array destination result subexpression cannot be a constant."

compileScalarSubExpTo :: ValueDestination -> SubExp -> ImpM op ()

compileScalarSubExpTo target se =
  writeExp target $ compileSubExp se

compileSubExp :: SubExp -> Imp.Exp
compileSubExp (Constant v) =
  Imp.Constant v
compileSubExp (Var v) =
  Imp.ScalarVar v

varIndex :: VName -> SE.ScalExp
varIndex name = SE.Id name Int

constIndex :: Int -> SE.ScalExp
constIndex = SE.Val . IntVal . fromIntegral

lookupArray :: VName -> ImpM op ArrayEntry
lookupArray name = do
  res <- asks $ HM.lookup name . envVtable
  case res of
    Just (ArrayVar entry) -> return entry
    _                    -> throwError $ "Unknown array: " ++ textual name

arrayLocation :: VName -> ImpM op MemLocation
arrayLocation name = entryArrayLocation <$> lookupArray name

lookupMemory :: VName -> ImpM op MemEntry
lookupMemory name = do
  res <- asks $ HM.lookup name . envVtable
  case res of
    Just (MemVar entry) -> return entry
    _                   -> throwError $ "Unknown memory block: " ++ textual name

destinationFromParam :: Param MemSummary -> ImpM op ValueDestination
destinationFromParam param
  | MemSummary mem ixfun <- paramLore param = do
      let dims = arrayDims $ paramType param
      memloc <- MemLocation mem <$> mapM subExpToDimSize dims <*> pure ixfun
      return $
        ArrayDestination (CopyIntoMemory memloc)
        (map (const Nothing) dims)
  | otherwise =
      return $ ScalarDestination $ paramName param

destinationFromParams :: [Param MemSummary] -> ImpM op Destination
destinationFromParams = liftM Destination . mapM destinationFromParam

destinationFromPattern :: Pattern -> ImpM op Destination
destinationFromPattern (Pattern ctxElems valElems) =
  Destination <$> mapM inspect valElems
  where ctxNames = map patElemName ctxElems
        isctx = (`elem` ctxNames)
        inspect patElem = do
          let name = patElemName patElem
          entry <- asks $ HM.lookup name . envVtable
          case entry of
            Just (ArrayVar (ArrayEntry (MemLocation mem _ ixfun) bt shape)) ->
              case patElemBindage patElem of
                BindVar -> do
                  let nullifyFreeDim (Imp.ConstSize _) = Nothing
                      nullifyFreeDim (Imp.VarSize v)
                        | isctx v   = Just v
                        | otherwise = Nothing
                  memsize <- entryMemSize <$> lookupMemory mem
                  let shape' = map nullifyFreeDim shape
                      memdest
                        | isctx mem = SetMemory mem $ nullifyFreeDim memsize
                        | otherwise = CopyIntoMemory $ MemLocation mem shape ixfun
                  return $ ArrayDestination memdest shape'
                BindInPlace _ _ is ->
                  case patElemRequires patElem of
                    Basic _ -> do
                      (_, space, elemOffset) <-
                        fullyIndexArray'
                        (MemLocation mem shape ixfun)
                        (map (`SE.subExpToScalExp` Int) is)
                        bt
                      return $ ArrayElemDestination mem bt space elemOffset
                    Array _ shape' _ ->
                      let memdest = sliceArray (MemLocation mem shape ixfun) $
                                    map (`SE.subExpToScalExp` Int) is
                      in return $
                         ArrayDestination (CopyIntoMemory memdest) $
                         replicate (shapeRank shape') Nothing
                    Mem {} ->
                      throwError "destinationFromPattern: cannot do an in-place bind of a memory block."

            Just (MemVar (MemEntry memsize _))
              | Imp.VarSize memsize' <- memsize, isctx memsize' ->
                return $ MemoryDestination name $ Just memsize'
              | otherwise ->
                return $ MemoryDestination name Nothing

            Just (ScalarVar (ScalarEntry _)) ->
              return $ ScalarDestination name

            Nothing ->
              throwError $ "destinationFromPattern: unknown target " ++ pretty name

fullyIndexArray :: VName -> [ScalExp]
                -> ImpM op (VName, Imp.Space, Count Bytes)
fullyIndexArray name indices = do
  arr <- lookupArray name
  fullyIndexArray' (entryArrayLocation arr) indices $ entryArrayElemType arr

fullyIndexArray' :: MemLocation -> [ScalExp] -> BasicType
                 -> ImpM op (VName, Imp.Space, Count Bytes)
fullyIndexArray' (MemLocation mem _ ixfun) indices bt = do
  space <- entryMemSpace <$> lookupMemory mem
  case scalExpToImpExp $ IxFun.index ixfun indices $ basicScalarSize bt of
    Nothing -> throwError "fullyIndexArray': Cannot turn scalexp into impexp"
    Just e -> return (mem, space, bytes e)

indexArray :: MemLocation -> [ScalExp]
           -> ImpM op MemLocation
indexArray (MemLocation arrmem dims ixfun) indices =
  return (MemLocation arrmem (drop (length indices) dims) $
          IxFun.applyInd ixfun indices)

sliceArray :: MemLocation
           -> [SE.ScalExp]
           -> MemLocation
sliceArray (MemLocation mem shape ixfun) indices =
  MemLocation mem (drop (length indices) shape) $
  IxFun.applyInd ixfun indices

subExpNotArray :: SubExp -> ImpM op Bool
subExpNotArray se = subExpType se >>= \case
  Array {} -> return False
  _        -> return True

arrayOuterSize :: ArrayEntry -> Count Elements
arrayOuterSize =
  product . map dimSizeToExp . take 1 . entryArrayShape

-- More complicated read/write operations that use index functions.

copy :: CopyCompiler op
copy bt dest src n = do
  cc <- asks envCopyCompiler
  cc bt dest src n

-- | Use an 'Imp.Copy' if possible, otherwise 'copyElementWise'.
defaultCopy :: CopyCompiler op
defaultCopy bt dest src n
  | Just destoffset <-
      scalExpToImpExp =<<
      IxFun.linearWithOffset destIxFun bt_size,
    Just srcoffset  <-
      scalExpToImpExp =<<
      IxFun.linearWithOffset srcIxFun bt_size = do
        srcspace <- entryMemSpace <$> lookupMemory srcmem
        destspace <- entryMemSpace <$> lookupMemory destmem
        emit $ Imp.Copy
          destmem (bytes destoffset) destspace
          srcmem (bytes srcoffset) srcspace $
          (n * row_size) `withElemType` bt
  | otherwise =
      copyElementWise bt dest src n
  where bt_size = basicScalarSize bt
        row_size = product $ map dimSizeToExp $ drop 1 srcshape
        MemLocation destmem _ destIxFun = dest
        MemLocation srcmem srcshape srcIxFun = src

copyElementWise :: CopyCompiler op
copyElementWise bt (MemLocation destmem destshape destIxFun) (MemLocation srcmem _ srcIxFun) n = do
    is <- replicateM (IxFun.rank destIxFun) (newVName "i")
    declaringLoopVars is $ do
      let ivars = map varIndex is
          destidx = simplifyScalExp $ IxFun.index destIxFun ivars bt_size
          srcidx = simplifyScalExp $ IxFun.index srcIxFun ivars bt_size
          bounds = map innerExp $ n : drop 1 (map dimSizeToExp destshape)
      srcspace <- entryMemSpace <$> lookupMemory srcmem
      destspace <- entryMemSpace <$> lookupMemory destmem
      emit $ foldl (.) id (zipWith Imp.For is bounds) $
        Imp.Write destmem (bytes $ fromJust $ scalExpToImpExp destidx) bt destspace $
        Imp.Index srcmem (bytes $ fromJust $ scalExpToImpExp srcidx) bt srcspace
  where bt_size = basicScalarSize bt

copyElem :: BasicType
         -> MemLocation -> [SE.ScalExp]
         -> MemLocation -> [SE.ScalExp]
         -> ImpM op (Imp.Code op)
copyElem bt
  destlocation@(MemLocation _ destshape _) destis
  srclocation@(MemLocation _ srcshape _) srcis

  | length srcis == length srcshape, length destis == length destshape = do
  (targetmem, destspace, targetoffset) <-
    fullyIndexArray' destlocation destis bt
  (srcmem, srcspace, srcoffset) <-
    fullyIndexArray' srclocation srcis bt
  return $ Imp.Write targetmem targetoffset bt destspace $
    Imp.Index srcmem srcoffset bt srcspace

  | otherwise = do
  destlocation' <- indexArray destlocation destis
  srclocation'  <- indexArray srclocation  srcis
  collect $ copy bt destlocation' srclocation' $
    product $ map dimSizeToExp $ drop (length srcis) srcshape

scalExpToImpExp :: ScalExp -> Maybe Imp.Exp
scalExpToImpExp (SE.Val x) =
  Just $ Imp.Constant x
scalExpToImpExp (SE.Id v _) =
  Just $ Imp.ScalarVar v
scalExpToImpExp (SE.SPlus e1 e2) =
  (+) <$> scalExpToImpExp e1 <*> scalExpToImpExp e2
scalExpToImpExp (SE.SMinus e1 e2) =
  (-) <$> scalExpToImpExp e1 <*> scalExpToImpExp e2
scalExpToImpExp (SE.STimes e1 e2) =
  (*) <$> scalExpToImpExp e1 <*> scalExpToImpExp e2
scalExpToImpExp (SE.SDiv e1 e2) =
  div <$> scalExpToImpExp e1 <*> scalExpToImpExp e2
scalExpToImpExp (SE.SQuot e1 e2) =
  quot <$> scalExpToImpExp e1 <*> scalExpToImpExp e2
scalExpToImpExp (SE.SMod e1 e2) =
  mod <$> scalExpToImpExp e1 <*> scalExpToImpExp e2
scalExpToImpExp (SE.SRem e1 e2) =
  rem <$> scalExpToImpExp e1 <*> scalExpToImpExp e2
scalExpToImpExp (SE.SSignum e) =
  signum <$> scalExpToImpExp e
scalExpToImpExp (SE.SAbs e) =
  abs <$> scalExpToImpExp e
scalExpToImpExp (SE.SNeg e) =
  (0-) <$> scalExpToImpExp e
scalExpToImpExp (SE.SOneIfZero e) =
  oneIfZero <$> scalExpToImpExp e
scalExpToImpExp (SE.SIfZero c t f) =
  ifZero <$>
  scalExpToImpExp c <*>
  scalExpToImpExp t <*>
  scalExpToImpExp f
scalExpToImpExp (SE.SIfLessThan a b t f) =
  ifLessThan <$>
  scalExpToImpExp a <*>
  scalExpToImpExp b <*>
  scalExpToImpExp t <*>
  scalExpToImpExp f
scalExpToImpExp _ =
  Nothing

simplifyScalExp :: ScalExp -> ScalExp
simplifyScalExp se = AlgSimplify.simplify se mempty

basicScalarSize :: BasicType -> ScalExp
basicScalarSize = SE.Val . IntVal . basicSize
