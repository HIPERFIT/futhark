{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}
-- | The type checker checks whether the program is type-consistent.
-- Whether type annotations are already present is irrelevant, but if
-- they are, the type checker will signal an error if they are wrong.
-- The program does not need to have any particular properties for the
-- type checker to function; in particular it does not need unique
-- names.
module Language.Futhark.TypeChecker
  ( checkProg
  , TypeError(..))
  where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.RWS
import Data.Array
import Data.List
import Data.Loc
import Data.Maybe
import Data.Either

import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS

import Prelude

import Language.Futhark
import Language.Futhark.Renamer
  (tagProg', untagPattern)
import Futhark.FreshNames hiding (newName)
import qualified Futhark.FreshNames
import Futhark.Util.Pretty

-- | Information about an error during type checking.  The 'Show'
-- instance for this type produces a human-readable description.
-- | Information about an error during type checking.  The 'Show'
-- instance for this type produces a human-readable description.
data TypeError =
    TypeError SrcLoc String
  -- ^ A general error happened at the given position and
  -- for the given reason.
  | UnifyError SrcLoc (TypeBase Rank NoInfo ()) SrcLoc (TypeBase Rank NoInfo ())
  -- ^ Types of two expressions failed to unify.
  | UnexpectedType SrcLoc
    (TypeBase Rank NoInfo ()) [TypeBase Rank NoInfo ()]
  -- ^ Expression of type was not one of the expected
  -- types.
  | ReturnTypeError SrcLoc Name (TypeBase Rank NoInfo ()) (TypeBase Rank NoInfo ())
  -- ^ The body of a function definition has a different
  -- type than its declaration.
  | DupDefinitionError Name SrcLoc SrcLoc
  -- ^ Two functions have been defined with the same name.
  | DupParamError Name Name SrcLoc
  -- ^ Two function parameters share the same name.
  | DupPatternError Name SrcLoc SrcLoc
  -- ^ Two pattern variables share the same name.
  | InvalidPatternError (PatternBase NoInfo Name)
    (TypeBase Rank NoInfo ()) (Maybe String) SrcLoc
  -- ^ The pattern is not compatible with the type or is otherwise
  -- inconsistent.
  | UnknownVariableError Name SrcLoc
  -- ^ Unknown variable of the given name referenced at the given spot.
  | UnknownFunctionError Name SrcLoc
  -- ^ Unknown function of the given name called at the given spot.
  | ParameterMismatch (Maybe Name) SrcLoc
    (Either Int [TypeBase Rank NoInfo ()]) [TypeBase Rank NoInfo ()]
  -- ^ A function (possibly anonymous) was called with
  -- invalid arguments.  The third argument is either the
  -- number of parameters, or the specific types of
  -- parameters accepted (sometimes, only the former can
  -- be determined).
  | UseAfterConsume Name SrcLoc SrcLoc
  -- ^ A variable was attempted used after being
  -- consumed.  The last location is the point of
  -- consumption.
  | IndexingError Int Int SrcLoc
  -- ^ Too many indices provided.  The first integer is
  -- the number of dimensions in the array being
  -- indexed.
  | BadAnnotation SrcLoc String
    (TypeBase Rank NoInfo ()) (TypeBase Rank NoInfo ())
  -- ^ One of the type annotations fails to match with the
  -- derived type.  The string is a description of the
  -- role of the type.  The last type is the new derivation.
  | BadTupleAnnotation SrcLoc String
    [Maybe (TypeBase Rank NoInfo ())] [TypeBase Rank NoInfo ()]
  -- ^ One of the tuple type annotations fails to
  -- match with the derived type.  The string is a
  -- description of the role of the type.  The last
  -- type is the elemens of the new derivation.
  | CurriedConsumption Name SrcLoc
  -- ^ A function is being curried with an argument to be consumed.
  | BadLetWithValue SrcLoc
  -- ^ The new value for an array slice in let-with is aliased to the source.
  | ReturnAliased Name Name SrcLoc
  -- ^ The unique return value of the function aliases
  -- one of the function parameters.
  | UniqueReturnAliased Name SrcLoc
  -- ^ A unique element of the tuple returned by the
  -- function aliases some other element of the tuple.
  | NotAnArray SrcLoc (ExpBase CompTypeBase Name) (TypeBase Rank NoInfo ())
  | PermutationError SrcLoc [Int] Int (Maybe Name)
  -- ^ The permutation is not valid.
  | DimensionNotInteger SrcLoc Name
  -- ^ A dimension annotation was a non-integer variable.
  | CyclicalTypeDefinition SrcLoc Name
  -- ^ Type alias has been defined cyclically.
  | UndefinedAlias SrcLoc Name
  -- ^ Type alias is referenced, but not defined
  | DupTypeAlias SrcLoc Name
  -- ^ Type alias has been defined twice
  | UndefinedAlias' Name
  -- ^ Type alias is referenced, but not defined. SrcLoc not available.

instance Show TypeError where
  show (TypeError pos msg) =
    "Type error at " ++ locStr pos ++ ":\n" ++ msg
  show (UnifyError e1loc t1 e2loc t2) =
    "Cannot unify type " ++ pretty t1 ++
    " of expression at " ++ locStr e1loc ++
    "\nwith type " ++ pretty t2 ++
    " of expression at " ++ locStr e2loc
  show (UnexpectedType loc _ []) =
    "Type of expression at " ++ locStr loc ++
    "cannot have any type - possibly a bug in the type checker."
  show (UnexpectedType loc t ts) =
    "Type of expression at " ++ locStr loc ++ " must be one of " ++
    intercalate ", " (map pretty ts) ++ ", but is " ++
    pretty t ++ "."
  show (ReturnTypeError pos fname rettype bodytype) =
    "Declaration of function " ++ nameToString fname ++ " at " ++ locStr pos ++
    " declares return type " ++ pretty rettype ++ ", but body has type " ++
    pretty bodytype
  show (DupDefinitionError name pos1 pos2) =
    "Duplicate definition of function " ++ nameToString name ++ ".  Defined at " ++
    locStr pos1 ++ " and " ++ locStr pos2 ++ "."
  show (DupParamError funname paramname pos) =
    "Parameter " ++ pretty paramname ++
    " mentioned multiple times in argument list of function " ++
    nameToString funname ++ " at " ++ locStr pos ++ "."
  show (DupPatternError name pos1 pos2) =
    "Variable " ++ pretty name ++ " bound twice in tuple pattern; at " ++
    locStr pos1 ++ " and " ++ locStr pos2 ++ "."
  show (InvalidPatternError pat t desc loc) =
    "Pattern " ++ pretty pat ++
    " cannot match value of type " ++ pretty t ++ " at " ++ locStr loc ++ end
    where end = case desc of Nothing -> "."
                             Just desc' -> ":\n" ++ desc'
  show (UnknownVariableError name pos) =
    "Unknown variable " ++ pretty name ++ " referenced at " ++ locStr pos ++ "."
  show (UnknownFunctionError fname pos) =
    "Unknown function " ++ nameToString fname ++ " called at " ++ locStr pos ++ "."
  show (ParameterMismatch fname pos expected got) =
    "In call of " ++ fname' ++ " at position " ++ locStr pos ++ ":\n" ++
    "expecting " ++ show nexpected ++ " argument(s) of type(s) " ++
     expected' ++ ", but got " ++ show ngot ++
    " arguments of types " ++ intercalate ", " (map pretty got) ++ "."
    where (nexpected, expected') =
            case expected of
              Left i -> (i, "(polymorphic)")
              Right ts -> (length ts, intercalate ", " $ map pretty ts)
          ngot = length got
          fname' = maybe "anonymous function" (("function "++) . nameToString) fname
  show (UseAfterConsume name rloc wloc) =
    "Variable " ++ pretty name ++ " used at " ++ locStr rloc ++
    ", but it was consumed at " ++ locStr wloc ++ ".  (Possibly through aliasing)"
  show (IndexingError dims got pos) =
    show got ++ " indices given at " ++ locStr pos ++
    ", but type of indexee  has " ++ show dims ++ " dimension(s)."
  show (BadAnnotation loc desc expected got) =
    "Annotation of \"" ++ desc ++ "\" type of expression at " ++
    locStr loc ++ " is " ++ pretty expected ++
    ", but derived to be " ++ pretty got ++ "."
  show (BadTupleAnnotation loc desc expected got) =
    "Annotation of \"" ++ desc ++ "\" type of expression at " ++
    locStr loc ++ " is a tuple {" ++
    intercalate ", " (map (maybe "(unspecified)" pretty) expected) ++
    "}, but derived to be " ++ prettyTuple got ++ "."
  show (CurriedConsumption fname loc) =
    "Function " ++ nameToString fname ++
    " curried over a consuming parameter at " ++ locStr loc ++ "."
  show (BadLetWithValue loc) =
    "New value for elements in let-with shares data with source array at " ++
    locStr loc ++ ".  This is illegal, as it prevents in-place modification."
  show (ReturnAliased fname name loc) =
    "Unique return value of function " ++ nameToString fname ++ " at " ++
    locStr loc ++ " is aliased to " ++ pretty name ++ ", which is not consumed."
  show (UniqueReturnAliased fname loc) =
    "A unique tuple element of return value of function " ++
    nameToString fname ++ " at " ++ locStr loc ++
    " is aliased to some other tuple component."
  show (NotAnArray loc _ t) =
    "The expression at " ++ locStr loc ++
    " is expected to be an array, but is " ++ pretty t ++ "."
  show (PermutationError loc perm rank name) =
    "The permutation (" ++ intercalate ", " (map show perm) ++
    ") is not valid for array " ++ name' ++ "of rank " ++ show rank ++ " at " ++
    locStr loc ++ "."
    where name' = maybe "" ((++" ") . pretty) name
  show (DimensionNotInteger loc name) =
    "Dimension declaration " ++ pretty name ++ " at " ++ locStr loc ++
    " should be an integer."
  show (CyclicalTypeDefinition loc name) =
    "Type alias " ++ pretty name ++ " at " ++ locStr loc ++
    " is cyclically defined."
-- | A tuple of a return type and a list of argument types.
type FunBinding = (StructTypeBase VName, [StructTypeBase VName])

data Binding = Bound Type
             | WasConsumed SrcLoc

data Usage = Consumed SrcLoc
           | Observed SrcLoc
             deriving (Eq, Ord, Show)

data Occurence = Occurence { observed :: Names VName
                           , consumed :: Names VName
                           , location :: SrcLoc
                           }
             deriving (Eq, Show)

instance Located Occurence where
  locOf = locOf . location

observation :: Names VName -> SrcLoc -> Occurence
observation = flip Occurence HS.empty

consumption :: Names VName -> SrcLoc -> Occurence
consumption = Occurence HS.empty

nullOccurence :: Occurence -> Bool
nullOccurence occ = HS.null (observed occ) && HS.null (consumed occ)

type Occurences = [Occurence]

type UsageMap = HM.HashMap VName [Usage]

type TypeAliasMap = HM.HashMap Name (StructTypeBase ())
type AliasMap shape vn = HM.HashMap Name (UserType shape vn)

usageMap :: Occurences -> UsageMap
usageMap = foldl comb HM.empty
  where comb m (Occurence obs cons loc) =
          let m' = HS.foldl' (ins $ Observed loc) m obs
          in HS.foldl' (ins $ Consumed loc) m' cons
        ins v m k = HM.insertWith (++) k [v] m

combineOccurences :: VName -> Usage -> Usage -> Either TypeError Usage
combineOccurences _ (Observed loc) (Observed _) = Right $ Observed loc
combineOccurences name (Consumed wloc) (Observed rloc) =
  Left $ UseAfterConsume (baseName name) rloc wloc
combineOccurences name (Observed rloc) (Consumed wloc) =
  Left $ UseAfterConsume (baseName name) rloc wloc
combineOccurences name (Consumed loc1) (Consumed loc2) =
  Left $ UseAfterConsume (baseName name) (max loc1 loc2) (min loc1 loc2)

checkOccurences :: Occurences -> Either TypeError ()
checkOccurences = void . HM.traverseWithKey comb . usageMap
  where comb _    []     = Right ()
        comb name (u:us) = foldM_ (combineOccurences name) u us

allConsumed :: Occurences -> Names VName
allConsumed = HS.unions . map consumed

seqOccurences :: Occurences -> Occurences -> Occurences
seqOccurences occurs1 occurs2 =
  filter (not . nullOccurence) $ map filt occurs1 ++ occurs2
  where filt occ =
          occ { observed = observed occ `HS.difference` postcons }
        postcons = allConsumed occurs2

altOccurences :: Occurences -> Occurences -> Occurences
altOccurences occurs1 occurs2 =
  filter (not . nullOccurence) $ map filt occurs1 ++ occurs2
  where filt occ =
          occ { consumed = consumed occ `HS.difference` postcons
              , observed = observed occ `HS.difference` postcons }
        postcons = allConsumed occurs2

-- | The 'VarUsage' data structure is used to keep track of which
-- variables have been referenced inside an expression, as well as
-- which variables the resulting expression may possibly alias.
data Dataflow = Dataflow {
    usageOccurences :: Occurences
  } deriving (Show)

instance Monoid Dataflow where
  mempty = Dataflow mempty
  Dataflow o1 `mappend` Dataflow o2 =
    Dataflow (o1 ++ o2)

-- | A pair of a variable table and a function table.  Type checking
-- happens with access to this environment.  The function table is
-- only initialised at the very beginning, but the variable table will
-- be extended during type-checking when let-expressions are
-- encountered.
data Scope  = Scope { envVtable :: HM.HashMap VName Binding
                    , envFtable :: HM.HashMap Name FunBinding
                    , envTAtable :: HM.HashMap Name (StructTypeBase ())
                    , envCheckOccurences :: Bool
                    }

-- | The type checker runs in this monad.  The 'Either' monad is used
-- for error handling.
newtype TypeM a = TypeM (RWST
                         Scope       -- Reader
                         Dataflow    -- Writer
                         VNameSource -- State
                         (Either TypeError) -- Inner monad
                         a)
  deriving (Monad, Functor, Applicative,
            MonadReader Scope,
            MonadWriter Dataflow,
            MonadState VNameSource)

runTypeM :: Scope -> VNameSource -> TypeM a
         -> Either TypeError (a, VNameSource)
runTypeM env src (TypeM m) = do
  (x, src', _) <- runRWST m env src
  return (x, src')

bad :: TypeError -> TypeM a
bad = TypeM . lift . Left

newName :: VName -> TypeM VName
newName s = do src <- get
               let (s', src') = Futhark.FreshNames.newName src s
               put src'
               return s'

newID :: Name -> TypeM VName
newID s = newName $ ID (s, 0)

newIDFromString :: String -> TypeM VName
newIDFromString = newID . nameFromString

newIdent :: String -> Type -> SrcLoc -> TypeM Ident
newIdent s t loc = do
  s' <- newID $ nameFromString s
  return $ Ident s' (Info t) loc

newParam :: String -> Type -> SrcLoc -> TypeM (ParamBase NoInfo VName)
newParam s t loc = do
  s' <- newIDFromString s
  return $ Param s' (TypeDecl (vacuousShapeAnnotations $ toStruct t) NoInfo) loc

liftEither :: Either TypeError a -> TypeM a
liftEither = either bad return

occur :: Occurences -> TypeM ()
occur occurs = tell Dataflow { usageOccurences = occurs }

-- | Proclaim that we have made read-only use of the given variable.
-- No-op unless the variable is array-typed.
observe :: Ident -> TypeM ()
observe (Ident nm (Info t) loc)
  | primType t = return ()
  | otherwise   = let als = nm `HS.insert` aliases t
                  in occur [observation als loc]

-- | Proclaim that we have written to the given variable.
consume :: SrcLoc -> Names VName -> TypeM ()
consume loc als = occur [consumption als loc]

-- | Proclaim that we have written to the given variable, and mark
-- accesses to it and all of its aliases as invalid inside the given
-- computation.
consuming :: Ident -> TypeM a -> TypeM a
consuming (Ident name (Info t) loc) m = do
  consume loc $ aliases t
  local consume' m
  where consume' env =
          env { envVtable = HM.insert name (WasConsumed loc) $ envVtable env }

collectDataflow :: TypeM a -> TypeM (a, Dataflow)
collectDataflow m = pass $ do
  (x, dataflow) <- listen m
  return ((x, dataflow), const mempty)

noDataflow :: TypeM a -> TypeM a
noDataflow = censor $ const mempty

maybeCheckOccurences :: Occurences -> TypeM ()
maybeCheckOccurences us = do
  check <- asks envCheckOccurences
  when check $ liftEither $ checkOccurences us

alternative :: TypeM a -> TypeM b -> TypeM (a,b)
alternative m1 m2 = pass $ do
  (x, Dataflow occurs1) <- listen m1
  (y, Dataflow occurs2) <- listen m2
  maybeCheckOccurences occurs1
  maybeCheckOccurences occurs2
  let usage = Dataflow $ occurs1 `altOccurences` occurs2
  return ((x, y), const usage)

-- | Make all bindings nonunique.
noUnique :: TypeM a -> TypeM a
noUnique = local (\env -> env { envVtable = HM.map f $ envVtable env})
  where f (Bound t)         = Bound $ t `setUniqueness` Nonunique
        f (WasConsumed loc) = WasConsumed loc

binding :: [Ident] -> TypeM a -> TypeM a
binding bnds = check . local (`bindVars` bnds)
  where bindVars :: Scope -> [Ident] -> Scope
        bindVars = foldl bindVar

        bindVar :: Scope -> Ident -> Scope
        bindVar env (Ident name (Info tp) _) =
          let inedges = HS.toList $ aliases tp
              update (Bound tp')
              -- If 'name' is tuple-typed, don't alias the components
              -- to 'name', because tuples have no identity beyond
              -- their components.
                | Tuple _ <- tp = Bound tp'
                | otherwise     = Bound (tp' `addAliases` HS.insert name)
              update b = b
          in env { envVtable = HM.insert name (Bound tp) $
                               adjustSeveral update inedges $
                               envVtable env }

        adjustSeveral f = flip $ foldl $ flip $ HM.adjust f

        -- Check whether the bound variables have been used correctly
        -- within their scope.
        check m = do
          (a, usages) <- collectOccurences m
          maybeCheckOccurences usages
          return a

        -- Collect and remove all occurences in @bnds@.  This relies
        -- on the fact that no variables shadow any other.
        collectOccurences m = pass $ do
          (x, usage) <- listen m
          let (relevant, rest) = split $ usageOccurences usage
          return ((x, relevant), const $ usage { usageOccurences = rest })
          where split = unzip .
                        map (\occ ->
                             let (obs1, obs2) = divide $ observed occ
                                 (con1, con2) = divide $ consumed occ
                             in (occ { observed = obs1, consumed = con1 },
                                 occ { observed = obs2, consumed = con2 }))
                names = HS.fromList $ map identName bnds
                divide s = (s `HS.intersection` names, s `HS.difference` names)

bindingParams :: [Parameter] -> TypeM a -> TypeM a
bindingParams params m =
  -- We need to bind both the identifiers themselves, as well as any
  -- presently non-bound shape annotations.
  binding (map fromParam params) $
  -- Figure out the not already bound shape annotations.
  binding (concat [ mapMaybe (inspectDim $ srclocOf param) $
                    nestedDims $ paramDeclaredType param
                  | param <- params ])
  m
  where inspectDim _ AnyDim =
          Nothing
        inspectDim _ (ConstDim _) =
          Nothing
        inspectDim loc (NamedDim name) =
          Just $ Ident name (Info $ Prim $ Signed Int32) loc

lookupVar :: VName -> SrcLoc -> TypeM Type
lookupVar name pos = do
  bnd <- asks $ HM.lookup name . envVtable
  case bnd of
    Nothing -> bad $ UnknownVariableError (baseName name) pos
    Just (Bound t) -> return t
    Just (WasConsumed wloc) -> bad $ UseAfterConsume (baseName name) pos wloc

-- | @t1 `unifyTypes` t2@ attempts to unify @t2@ and @t2@.  If
-- unification cannot happen, 'Nothing' is returned, otherwise a type
-- that combines the aliasing of @t1@ and @t2@ is returned.  The
-- uniqueness of the resulting type will be the least of the
-- uniqueness of @t1@ and @t2@.
unifyTypes :: Monoid (as vn) =>
              TypeBase Rank as vn
           -> TypeBase Rank as vn
           -> Maybe (TypeBase Rank as vn)
unifyTypes (Prim t1) (Prim t2)
  | t1 == t2  = Just $ Prim t1
  | otherwise = Nothing
unifyTypes (Array at1) (Array at2) =
  Array <$> unifyArrayTypes at1 at2
unifyTypes (Tuple ts1) (Tuple ts2)
  | length ts1 == length ts2 =
    Tuple <$> zipWithM unifyTypes ts1 ts2
unifyTypes _ _ = Nothing

unifyArrayTypes :: Monoid (as vn) =>
                   ArrayTypeBase Rank as vn
                -> ArrayTypeBase Rank as vn
                -> Maybe (ArrayTypeBase Rank as vn)
unifyArrayTypes (PrimArray bt1 shape1 u1 als1) (PrimArray bt2 shape2 u2 als2)
  | shapeRank shape1 == shapeRank shape2, bt1 == bt2 =
    Just $ PrimArray bt1 shape1 (u1 <> u2) (als1 <> als2)
unifyArrayTypes (TupleArray et1 shape1 u1) (TupleArray et2 shape2 u2)
  | shapeRank shape1 == shapeRank shape2 =
    TupleArray <$> zipWithM unifyTupleArrayElemTypes et1 et2 <*>
    pure shape1 <*> pure (u1 <> u2)
unifyArrayTypes _ _ =
  Nothing

unifyTupleArrayElemTypes :: Monoid (as vn) =>
                            TupleArrayElemTypeBase Rank as vn
                         -> TupleArrayElemTypeBase Rank as vn
                         -> Maybe (TupleArrayElemTypeBase Rank as vn)
unifyTupleArrayElemTypes (PrimArrayElem bt1 als1) (PrimArrayElem bt2 als2)
  | bt1 == bt2 = Just $ PrimArrayElem bt1 $ als1 <> als2
  | otherwise  = Nothing
unifyTupleArrayElemTypes (ArrayArrayElem at1) (ArrayArrayElem at2) =
  ArrayArrayElem <$> unifyArrayTypes at1 at2
unifyTupleArrayElemTypes (TupleArrayElem ts1) (TupleArrayElem ts2) =
  TupleArrayElem <$> zipWithM unifyTupleArrayElemTypes ts1 ts2
unifyTupleArrayElemTypes _ _ =
  Nothing

-- | Determine if two types are identical, ignoring uniqueness.
-- Causes a 'TypeError' if they fail to match, and otherwise returns
-- one of them.
unifyExpTypes :: Exp -> Exp -> TypeM Type
unifyExpTypes e1 e2 =
  maybe (bad $ UnifyError
         (srclocOf e1) (toStructural t1)
         (srclocOf e2) (toStructural t2)) return $
  unifyTypes (typeOf e1) (typeOf e2)
  where t1 = typeOf e1
        t2 = typeOf e2

anySignedType :: [Type]
anySignedType = map (Prim . Signed) [minBound .. maxBound]

anyUnsignedType :: [Type]
anyUnsignedType = map (Prim . Unsigned) [minBound .. maxBound]

anyIntType :: [Type]
anyIntType = anySignedType ++ anyUnsignedType

anyFloatType :: [Type]
anyFloatType = map (Prim . FloatType) [minBound .. maxBound]

anyNumberType :: [Type]
anyNumberType = anyIntType ++ anyFloatType

-- | @require ts e@ causes a 'TypeError' if @typeOf e@ does not unify
-- with one of the types in @ts@.  Otherwise, simply returns @e@.
-- This function is very useful in 'checkExp'.
require :: [Type] -> Exp -> TypeM Exp
require ts e
  | any (typeOf e `similarTo`) ts = return e
  | otherwise = bad $ UnexpectedType (srclocOf e)
                      (toStructural $ typeOf e) $
                      map toStructural ts

rowTypeM :: Exp -> TypeM Type
rowTypeM e = maybe wrong return $ peelArray 1 $ typeOf e
  where wrong = bad $ TypeError (srclocOf e) $ "Type of expression is not array, but " ++ ppType (typeOf e) ++ "."

-- | Type check a program containing arbitrary no information,
-- yielding either a type error or a program with complete type
-- information.
checkProg :: UncheckedProg -> Either TypeError (Prog, VNameSource)
checkProg prog = do
-- | Her vil vi gerne checke vores medbragte typer
  ftable <- buildFtable
  ttable <- buildTypeAliasTable
  let typeenv = Scope { envVtable = HM.empty
                      , envFtable = ftable
                      , envTAtable = ttable
                      , envCheckOccurences = True
                      }
  runTypeM typeenv src $
    (Prog []) <$> mapM (noDataflow . checkFun) (progFunctions prog')
  where
    -- split prog into TypeDefs and FunDefs
    -- compute aliastable
    -- replace all aliases with actual types in FunDefs
    -- set prog'
    buildTypeAliasTable = typeAliasTableFromProg prog
    (prog', src) = tagProg' blankNameSource prog

    -- To build the ftable we loop through the list of function
    -- definitions.  In addition to the normal ftable information
    -- (name, return type, argument types), we also keep track of
    -- position information, in order to report both locations of
    -- duplicate function definitions.  The position information is
    -- removed at the end.
    buildFtable = HM.map rmLoc <$>
                  foldM expand (HM.map addLoc initialFtable)
                  (progFunctions prog')
    expand ftable (FunDef _ name (TypeDecl ret NoInfo) args _ pos)
      | Just (_,_,pos2) <- HM.lookup name ftable =
        Left $ DupDefinitionError name pos pos2
      | otherwise =
        let argtypes = map (toStruct . paramDeclaredType) args -- Throw away argument names.
        in Right $ HM.insert name (ret,argtypes,pos) ftable
    rmLoc (ret,args,_) = (ret,args)
    addLoc (t, ts) = (t, ts, noLoc)

initialFtable :: HM.HashMap Name FunBinding
initialFtable = HM.map addBuiltin builtInFunctions
  where addBuiltin (t, ts) = (Prim t, map Prim ts)

checkFun :: FunDefBase NoInfo VName -> TypeM FunDef
checkFun (FunDef entry fname (TypeDecl rettype NoInfo) params body loc) = do
  params' <- checkParams
  body' <- bindingParams params' $ do
    checkRetType loc rettype
    checkExp body

  checkReturnAlias params' $ typeOf body'

  if toStructural (typeOf body') `subtypeOf` toStructural rettype then
    return $ FunDef entry fname (TypeDecl rettype $ Info rettype) params' body' loc
  else bad $ ReturnTypeError loc fname (toStructural rettype) $
             toStructural $ typeOf body'

  where checkParams = do
          -- First find all normal parameters (checking for duplicates).
          params' <- foldM checkNormParams [] params
          -- Then check shape annotations (where duplicates are OK, as
          -- long as it's not a duplicate of a normal parameter.)
          mapM_ checkDimDecls params'
          return $ reverse params'

        checkNormParams knownparams (Param pname (TypeDecl pt NoInfo) ploc)
          | pname `elem` map paramName knownparams =
            bad $ DupParamError fname (baseName pname) loc
          | otherwise =
            -- For now, the expanded type is the same as the declared type.
            return $ Param pname (TypeDecl pt $ Info pt) ploc : knownparams

        checkDimDecls param
          | Just name <- find (`elem` map paramName params) boundDims =
            bad $ DupParamError fname (baseName name) loc
          | otherwise =
            return ()
          where boundDims = mapMaybe boundDim $ nestedDims $ paramType param
                boundDim (NamedDim name) = Just name
                boundDim _ = Nothing

        notAliasingParam params' names =
          forM_ params' $ \p ->
            when (not (unique $ paramType p) &&
                  paramName p `HS.member` names) $
              bad $ ReturnAliased fname (baseName $ paramName p) loc

        -- | Check that unique return values do not alias a
        -- non-consumed parameter.
        checkReturnAlias params' =
          foldM_ (checkReturnAlias' params') HS.empty . returnAliasing rettype

        checkReturnAlias' params' seen (Unique, names)
          | any (`HS.member` HS.map snd seen) $ HS.toList names =
            bad $ UniqueReturnAliased fname loc
          | otherwise = do
            notAliasingParam params' names
            return $ seen `HS.union` tag Unique names
        checkReturnAlias' _ seen (Nonunique, names)
          | any (`HS.member` seen) $ HS.toList $ tag Unique names =
            bad $ UniqueReturnAliased fname loc
          | otherwise = return $ seen `HS.union` tag Nonunique names

        tag u = HS.map $ \name -> (u, name)

        returnAliasing (Tuple ets1) (Tuple ets2) =
          concat $ zipWith returnAliasing ets1 ets2
        returnAliasing expected got = [(uniqueness expected, aliases got)]

checkExp :: ExpBase NoInfo VName -> TypeM Exp

checkExp (Literal val pos) =
  Literal <$> checkLiteral pos val <*> pure pos

checkExp (TupLit es pos) = do
  es' <- mapM checkExp es
  let res = TupLit es' pos
  return $ fromMaybe res (Literal <$> expToValue res <*> pure pos)

checkExp (ArrayLit es _ loc) = do
  es' <- mapM checkExp es
  -- Find the universal type of the array arguments.
  et <- case es' of
          [] -> bad $ TypeError loc "Empty array literal"
          e:es'' ->
            let check elemt eleme
                  | Just elemt' <- elemt `unifyTypes` typeOf eleme =
                    return elemt'
                  | otherwise =
                    bad $ TypeError loc $ ppExp eleme ++ " is not of expected type " ++ ppType elemt ++ "."
            in foldM check (typeOf e) es''

  let lit = ArrayLit es' (Info et) loc
  return $ fromMaybe lit (Literal <$> expToValue lit <*> pure loc)

checkExp (BinOp op e1 e2 NoInfo pos) = checkBinOp op e1 e2 pos

checkExp (UnOp Not e pos) = do
  e' <- require [Prim Bool] =<< checkExp e
  return $ UnOp Not e' pos

checkExp (UnOp Complement e loc) = do
  e' <- require anyIntType =<< checkExp e
  return $ UnOp Complement e' loc

checkExp (UnOp Negate e loc) = do
  e' <- require anyNumberType =<< checkExp e
  return $ UnOp Negate e' loc

checkExp (UnOp Abs e loc) = do
  e' <- require anyIntType =<< checkExp e
  return $ UnOp Abs e' loc

checkExp (UnOp Signum e loc) = do
  e' <- require anyIntType =<< checkExp e
  return $ UnOp Signum e' loc

checkExp (UnOp (ToFloat t) e loc) = do
  e' <- require anyNumberType =<< checkExp e
  return $ UnOp (ToFloat t) e' loc

checkExp (UnOp (ToSigned t) e loc) = do
  e' <- require anyNumberType =<< checkExp e
  return $ UnOp (ToSigned t) e' loc

checkExp (UnOp (ToUnsigned t) e loc) = do
  e' <- require anyNumberType =<< checkExp e
  return $ UnOp (ToUnsigned t) e' loc

checkExp (If e1 e2 e3 _ pos) = do
  e1' <- require [Prim Bool] =<< checkExp e1
  ((e2', e3'), dflow) <- collectDataflow $ checkExp e2 `alternative` checkExp e3
  tell dflow
  brancht <- unifyExpTypes e2' e3'
  let t' = addAliases brancht
           (`HS.difference` allConsumed (usageOccurences dflow))
  return $ If e1' e2' e3' (Info t') pos

checkExp (Var ident) = do
  ident' <- checkIdent ident
  observe ident'
  return $ Var ident'

checkExp (Apply fname args _ loc) = do
  bnd <- asks $ HM.lookup fname . envFtable
  case bnd of
    Nothing -> bad $ UnknownFunctionError fname loc
    Just (ftype, paramtypes) -> do
      (args', argflows) <- unzip <$> mapM (checkArg . fst) args

      let rettype' = returnType (removeShapeAnnotations ftype)
                     (map diet paramtypes) (map typeOf args')

      checkFuncall (Just fname) loc paramtypes ftype argflows

      return $ Apply fname (zip args' $ map diet paramtypes) (Info rettype') loc

checkExp (LetPat pat e body pos) = do
  (e', dataflow) <- collectDataflow $ checkExp e
  (scope, pat') <- checkBinding pat (typeOf e') dataflow
  scope $ do
    body' <- checkExp body
    return $ LetPat pat' e' body' pos

checkExp (LetWith d@(Ident dest _ destpos) src idxes ve body pos) = do
  src' <- checkIdent src
  idxes' <- mapM (require [Prim $ Signed Int32] <=< checkExp) idxes
  let destt' = unInfo (identType src') `setAliases` HS.empty
      dest' = Ident dest (Info destt') destpos

  unless (unique $ unInfo $ identType src') $
    bad $ TypeError pos $ "Source '" ++ pretty (baseName $ identName src) ++
    "' has type " ++ ppType (unInfo $ identType src') ++ ", which is not unique"

  case peelArray (length idxes) (unInfo $ identType src') of
    Nothing -> bad $ IndexingError
                     (arrayRank $ unInfo $ identType src') (length idxes) (srclocOf src)
    Just elemt ->
      sequentially (require [elemt] =<< checkExp ve) $ \ve' _ -> do
        when (identName src `HS.member` aliases (typeOf ve')) $
          bad $ BadLetWithValue pos
        (scope, _) <- checkBinding (Id d) destt' mempty
        body' <- consuming src' $ scope $ checkExp body
        return $ LetWith dest' src' idxes' ve' body' pos

checkExp (Index e idxes pos) = do
  e' <- checkExp e
  let vt = typeOf e'
  when (arrayRank vt < length idxes) $
    bad $ IndexingError (arrayRank vt) (length idxes) pos
  idxes' <- mapM (require [Prim $ Signed Int32] <=< checkExp) idxes
  return $ Index e' idxes' pos

checkExp (Iota e pos) = do
  e' <- require [Prim $ Signed Int32] =<< checkExp e
  return $ Iota e' pos

checkExp (Size i e pos) = do
  e' <- checkExp e
  case typeOf e' of
    Array {}
      | i >= 0 && i < arrayRank (typeOf e') ->
        return $ Size i e' pos
      | otherwise ->
        bad $ TypeError pos $ "Type " ++ ppType (typeOf e') ++ " has no dimension " ++ show i ++ "."
    _        -> bad $ TypeError pos "Argument to size must be array."

checkExp (Replicate countexp valexp pos) = do
  countexp' <- require [Prim $ Signed Int32] =<< checkExp countexp
  valexp' <- checkExp valexp
  return $ Replicate countexp' valexp' pos

checkExp (Reshape shapeexps arrexp pos) = do
  shapeexps' <- mapM (require [Prim $ Signed Int32] <=< checkExp) shapeexps
  arrexp' <- checkExp arrexp
  return (Reshape shapeexps' arrexp' pos)

checkExp (Rearrange perm arrexp pos) = do
  arrexp' <- checkExp arrexp
  let rank = arrayRank $ typeOf arrexp'
  when (length perm /= rank || sort perm /= [0..rank-1]) $
    bad $ PermutationError pos perm rank name
  return $ Rearrange perm arrexp' pos
  where name = case arrexp of Var v -> Just $ baseName $ identName v
                              _     -> Nothing

checkExp (Transpose arrexp pos) = do
  arrexp' <- checkExp arrexp
  when (arrayRank (typeOf arrexp') /= 2) $
    bad $ TypeError pos "Argument to transpose is not two-dimensional array."
  return $ Transpose arrexp' pos

checkExp (Zip arrexps loc) = do
  arrexps' <- mapM (checkExp . fst) arrexps
  arrts <- forM arrexps' $ \arrexp -> do
    let arrt = typeOf arrexp
    when (arrayRank arrt < 1) $
      bad $ TypeError (srclocOf arrexp) $
      "Type of expression is not array, but " ++ ppType arrt ++ "."
    return arrt
  return $ Zip (zip arrexps' $ map Info arrts) loc

checkExp (Unzip e _ pos) = do
  e' <- checkExp e
  case typeOf e' of
    Array (TupleArray ets shape u) ->
      let componentType et =
            arrayOf (tupleArrayElemToType et) shape u
      in return $ Unzip e' (map (Info . componentType) ets) pos
    t ->
      bad $ TypeError pos $
      "Argument to unzip is not an array of tuples, but " ++
      ppType t ++ "."

checkExp (Unsafe e loc) =
  Unsafe <$> checkExp e <*> pure loc

checkExp (Map fun arrexp pos) = do
  (arrexp', arg) <- checkSOACArrayArg arrexp
  fun' <- checkLambda fun [arg]
  return (Map fun' arrexp' pos)

checkExp (Reduce comm fun startexp arrexp pos) = do
  (startexp', startarg) <- checkArg startexp
  (arrexp', arrarg@(inrowt, _, _)) <- checkSOACArrayArg arrexp
  fun' <- checkLambda fun [startarg, arrarg]
  let redtype = lambdaType fun' [typeOf startexp', typeOf arrexp']
  unless (typeOf startexp' `subtypeOf` redtype) $
    bad $ TypeError pos $ "Initial value is of type " ++ ppType (typeOf startexp') ++ ", but reduce function returns type " ++ ppType redtype ++ "."
  unless (inrowt `subtypeOf` redtype) $
    bad $ TypeError pos $ "Array element value is of type " ++ ppType inrowt ++ ", but reduce function returns type " ++ ppType redtype ++ "."
  return $ Reduce comm fun' startexp' arrexp' pos

checkExp (Scan fun startexp arrexp pos) = do
  (startexp', startarg) <- checkArg startexp
  (arrexp', arrarg@(inrowt, _, _)) <- checkSOACArrayArg arrexp
  fun' <- checkLambda fun [startarg, arrarg]
  let scantype = lambdaType fun' [typeOf startexp', typeOf arrexp']
  unless (typeOf startexp' `subtypeOf` scantype) $
    bad $ TypeError pos $ "Initial value is of type " ++ ppType (typeOf startexp') ++ ", but scan function returns type " ++ ppType scantype ++ "."
  unless (inrowt `subtypeOf` scantype) $
    bad $ TypeError pos $ "Array element value is of type " ++ ppType inrowt ++ ", but scan function returns type " ++ ppType scantype ++ "."
  return $ Scan fun' startexp' arrexp' pos

checkExp (Filter fun arrexp pos) = do
  (arrexp', (rowelemt, argflow, argloc)) <- checkSOACArrayArg arrexp
  let nonunique_arg = (rowelemt `setUniqueness` Nonunique,
                       argflow, argloc)
  fun' <- checkLambda fun [nonunique_arg]
  when (lambdaType fun' [rowelemt] /= Prim Bool) $
    bad $ TypeError pos "Filter function does not return bool."

  return $ Filter fun' arrexp' pos

checkExp (Partition funs arrexp pos) = do
  (arrexp', (rowelemt, argflow, argloc)) <- checkSOACArrayArg arrexp
  let nonunique_arg = (rowelemt `setUniqueness` Nonunique,
                       argflow, argloc)
  funs' <- forM funs $ \fun -> do
    fun' <- checkLambda fun [nonunique_arg]
    when (lambdaType fun' [rowelemt] /= Prim Bool) $
      bad $ TypeError (srclocOf fun') "Partition function does not return bool."
    return fun'

  return $ Partition funs' arrexp' pos

checkExp (Stream form lam@(AnonymFun lam_ps _ (TypeDecl lam_rtp NoInfo) _) arr pos) = do
  lam_ps' <- mapM checkParam lam_ps
  let isArrayType arrtp =
        case arrtp of
          Array _ -> True
          _       -> False
  let lit_int0 = Literal (PrimValue $ SignedValue $ Int32Value 0) pos
  [(_, intarg),(arr',arrarg)] <- mapM checkArg [lit_int0, arr]
  -- arr must have an array type
  unless (isArrayType $ typeOf arr') $
    bad $ TypeError pos "Stream with input array of non-array type."
  -- typecheck stream's lambdas
  (form', macctup) <-
    case form of
      MapLike o -> return (MapLike o, Nothing)
      RedLike o comm lam0 acc -> do
        (acc',accarg) <- checkArg acc
        lam0' <- checkLambda lam0 [accarg, accarg]
        let redtype = lambdaType lam0' [typeOf acc', typeOf acc']
        unless (typeOf acc' `subtypeOf` redtype) $
            bad $ TypeError pos $ "Stream's reduce fun: Initial value is of type " ++
                  ppType (typeOf acc') ++ ", but reduce fun returns type "++ppType redtype++"."
        return (RedLike o comm lam0' acc', Just(acc',accarg))
      Sequential acc -> do
        (acc',accarg) <- checkArg acc
        return (Sequential acc', Just(acc',accarg))
  -- (i) properly check the lambda on its parameter and
  --(ii) make some fake arguments, which do not alias `arr', and
  --     check that aliases of `arr' are not used inside lam.
  let fakearg = (fromStruct $ addNames $ removeNames $ typeOf arr', mempty, srclocOf pos)
      (aas,faas) = case macctup of
                    Nothing        -> ([intarg, arrarg],        [intarg,fakearg]         )
                    Just(_,accarg) -> ([intarg, accarg, arrarg],[intarg, accarg, fakearg])
  lam' <- checkLambda lam aas
  (_, dflow)<- collectDataflow $ checkLambda lam faas
  let arr_aliasses = HS.toList $ aliases $ typeOf arr'
  let usages = usageMap $ usageOccurences dflow
  when (any (`HM.member` usages) arr_aliasses) $
     bad $ TypeError pos "Stream with input array used inside lambda."
  -- check that the result type of lambda matches the accumulator part
  _ <- case macctup of
        Just (acc',_) -> do
            let rtp' = lambdaType lam' [Prim $ Signed Int32, typeOf acc', typeOf acc']
            case rtp' of
                Tuple (acctp:_) ->
                     unless (typeOf acc' `subtypeOf` removeShapeAnnotations acctp) $
                        bad $ TypeError pos ("Stream with accumulator-type missmatch"++
                                             "or result arrays of non-array type.")
                _ -> unless (typeOf acc' `subtypeOf` removeShapeAnnotations rtp') $
                        bad $ TypeError pos "Stream with accumulator-type missmatch."
        Nothing -> return ()
  -- check outerdim of Lambda's streamed-in array params are NOT specified,
  -- and that return type inner dimens are all specified but not as other
  -- lambda parameters!
  (chunk,lam_arr_tp)<- case macctup of
                         Just _ -> case lam_ps' of
                                     [ch,_,arrpar] -> return (paramName ch,
                                                              paramType arrpar)
                                     _ -> bad $ TypeError pos "Stream's lambda should have three args."
                         Nothing-> case lam_ps' of
                                     [ch,  arrpar] -> return (paramName ch,
                                                              paramType arrpar)
                                     _ -> bad $ TypeError pos "Stream's lambda should have three args."
  let outer_dims = arrayDims lam_arr_tp
  _ <- case head outer_dims of
        AnyDim      -> return ()
        NamedDim _  -> return ()
        ConstDim _  -> bad $ TypeError pos ("Stream: outer dimension of stream should NOT"++
                                            " be specified since it is "++pretty chunk++"by default.")
  _ <- case lam_rtp of
        Tuple res_tps -> do
            let res_arr_tps = tail res_tps
            if all isArrayType res_arr_tps
            then do let lam_params = HS.fromList $ map paramName lam_ps'
                        arr_iner_dims = concatMap (tail . arrayDims) res_arr_tps
                        boundDim (NamedDim name) = return $ Just name
                        boundDim (ConstDim _   ) = return Nothing
                        boundDim _               =
                            bad $ TypeError pos $ "Stream's lambda: inner dimensions of the"++
                                                  " streamed-result arrays MUST be specified!"
                    rtp_iner_syms <- catMaybes <$> mapM boundDim arr_iner_dims
                    case find (`HS.member` lam_params) rtp_iner_syms of
                      Just name -> bad $ TypeError pos $
                                          "Stream's lambda: " ++ pretty (baseName name) ++
                                          " cannot specify a variant inner result shape"
                      _ -> return ()
            else bad $ TypeError pos "Stream with result arrays of non-array type."
        _ -> return ()-- means that no array is streamed out!
  -- finally return type-checked stream!
  return $ Stream form' lam' arr' pos

checkExp (Stream _ _ _ pos) =
  bad $ TypeError pos "Stream with lambda NOT an anonymous function!!!!"

checkExp (Split splitexps arrexp pos) = do
  splitexps' <- mapM (require [Prim $ Signed Int32] <=< checkExp) splitexps
  arrexp' <- checkExp arrexp
  _ <- rowTypeM arrexp' -- Just check that it's an array.
  return $ Split splitexps' arrexp' pos

checkExp (Concat arr1exp arr2exps pos) = do
  arr1exp'  <- checkExp arr1exp
  arr2exps' <- mapM (require [typeOf arr1exp'] <=< checkExp) arr2exps
  mapM_ rowTypeM arr2exps' -- Just check that it's an array.
  return $ Concat arr1exp' arr2exps' pos

checkExp (Copy e pos) = do
  e' <- checkExp e
  return $ Copy e' pos

checkExp (DoLoop mergepat mergeexp form loopbody letbody loc) = do
  -- First we do a basic check of the loop body to figure out which of
  -- the merge parameters are being consumed.  For this, we first need
  -- to check the merge pattern, which requires the (initial) merge
  -- expression.
  ((mergeexp', bindExtra), mergeflow) <-
    collectDataflow $ do
      mergeexp' <- checkExp mergeexp
      return $
        case form of
          For _ _ (Ident loopvar _ _) _ ->
            let iparam = Ident loopvar (Info $ Prim $ Signed Int32) loc
            in (mergeexp', [iparam])
          While _ ->
            (mergeexp', [])

  -- Check the loop body.
  (firstscope, mergepat') <- checkBinding mergepat (typeOf mergeexp') mempty
  ((form', loopbody'), bodyflow) <-
    noUnique $ firstscope $ binding bindExtra $ collectDataflow $
    case form of
      For dir lboundexp (Ident loopvar _ loopvarloc) uboundexp -> do
        lboundexp' <- require [Prim $ Signed Int32] =<< checkExp lboundexp
        uboundexp' <- require [Prim $ Signed Int32] =<< checkExp uboundexp
        loopbody' <- checkExp loopbody
        return (For dir lboundexp' (Ident loopvar (Info $ Prim $ Signed Int32) loopvarloc) uboundexp',
                loopbody')
      While condexp -> do
        (condexp', condflow) <-
          collectDataflow $ require [Prim Bool] =<< checkExp condexp
        (loopbody', bodyflow) <-
          collectDataflow $ checkExp loopbody
        occur $ usageOccurences condflow `seqOccurences`
                usageOccurences bodyflow
        return (While condexp',
                loopbody')

  let consumed_merge = patNameSet mergepat' `HS.intersection`
                       allConsumed (usageOccurences bodyflow)
      uniquePat (Wildcard (Info t) wloc) =
        Wildcard (Info $ t `setUniqueness` Nonunique) wloc
      uniquePat (Id (Ident name (Info t) iloc))
        | name `HS.member` consumed_merge =
            Id $ Ident name (Info $ t `setUniqueness` Unique `setAliases` mempty) iloc
        | otherwise =
            let t' = case t of Tuple{} -> t
                               _       -> t `setUniqueness` Nonunique
            in Id $ Ident name (Info t') iloc
      uniquePat (TuplePattern pats ploc) =
        TuplePattern (map uniquePat pats) ploc

      -- Make the pattern unique where needed.
      mergepat'' = uniquePat mergepat'

  -- Now check that the loop returned the right type.
  unless (typeOf loopbody' `subtypeOf` patternType mergepat'') $
    bad $ UnexpectedType (srclocOf loopbody')
    (toStructural $ typeOf loopbody')
    [toStructural $ patternType mergepat'']

  -- Check that the new values of consumed merge parameters do not
  -- alias something bound outside the loop, AND that anything
  -- returned for a unique merge parameter does not alias anything
  -- else returned.
  bound_outside <- asks $ HS.fromList . HM.keys . envVtable
  let checkMergeReturn (Id ident) t
        | unique $ unInfo $ identType ident,
          v:_ <- HS.toList $ aliases t `HS.intersection` bound_outside =
            lift $ bad $ TypeError loc $ "Loop return value corresponding to merge parameter " ++
            pretty (identName ident) ++ " aliases " ++ pretty v ++ "."
        | otherwise = do
            (cons,obs) <- get
            unless (HS.null $ aliases t `HS.intersection` cons) $
              lift $ bad $ TypeError loc $ "Loop return value for merge parameter " ++
              pretty (identName ident) ++ " aliases other consumed merge parameter."
            when (unique (unInfo $ identType ident) &&
                  not (HS.null (aliases t `HS.intersection` (cons<>obs)))) $
              lift $ bad $ TypeError loc $ "Loop return value for consuming merge parameter " ++
              pretty (identName ident) ++ " aliases previously returned value." ++ show (aliases t, cons, obs)
            if unique (unInfo $ identType ident)
              then put (cons<>aliases t, obs)
              else put (cons, obs<>aliases t)
      checkMergeReturn (TuplePattern pats _) (Tuple ts) =
        zipWithM_ checkMergeReturn pats ts
      checkMergeReturn _ _ =
        return ()
  evalStateT (checkMergeReturn mergepat'' $ typeOf loopbody') (mempty, mempty)

  let consumeMerge (Id (Ident _ (Info pt) ploc)) mt
        | unique pt = consume ploc $ aliases mt
      consumeMerge (TuplePattern pats _) (Tuple ts) =
        zipWithM_ consumeMerge pats ts
      consumeMerge _ _ =
        return ()
  ((), merge_consume) <-
    collectDataflow $ consumeMerge mergepat'' $ typeOf mergeexp'

  occur $ usageOccurences mergeflow `seqOccurences`
          usageOccurences merge_consume

  binding (patIdents mergepat'') $ do
    letbody' <- checkExp letbody
    return $ DoLoop mergepat'' mergeexp'
                    form'
                    loopbody' letbody' loc

checkSOACArrayArg :: ExpBase NoInfo VName -> TypeM (Exp, Arg)
checkSOACArrayArg e = do
  (e', (t, dflow, argloc)) <- checkArg e
  case peelArray 1 t of
    Nothing -> bad $ TypeError argloc "SOAC argument is not an array"
    Just rt -> return (e', (rt, dflow, argloc))

checkLiteral :: SrcLoc -> Value -> TypeM Value
checkLiteral _ (PrimValue bv) = return $ PrimValue bv
checkLiteral loc (TupValue vals) = do
  vals' <- mapM (checkLiteral loc) vals
  return $ TupValue vals'
checkLiteral loc (ArrayValue arr rt) = do
  vals <- mapM (checkLiteral loc) (elems arr)
  case find ((/=rt) . removeNames . valueType) vals of
    Just wrong -> bad $ TypeError loc $ ppValue wrong ++ " is not of expected type " ++ ppType rt ++ "."
    _          -> return ()
  return $ ArrayValue (listArray (bounds arr) vals) rt

checkIdent :: IdentBase NoInfo VName -> TypeM Ident
checkIdent (Ident name _ pos) = do
  vt <- lookupVar name pos
  return $ Ident name (Info vt) pos

checkParam :: ParamBase NoInfo VName -> TypeM Parameter
checkParam (Param name (TypeDecl t NoInfo) loc) =
  return $ Param name (TypeDecl t $ Info t) loc

checkBinOp :: BinOp -> ExpBase NoInfo VName -> ExpBase NoInfo VName -> SrcLoc
           -> TypeM Exp
checkBinOp Plus e1 e2 pos = checkPolyBinOp Plus anyNumberType e1 e2 pos
checkBinOp Minus e1 e2 pos = checkPolyBinOp Minus anyNumberType e1 e2 pos
checkBinOp Pow e1 e2 pos = checkPolyBinOp Pow anyNumberType e1 e2 pos
checkBinOp Times e1 e2 pos = checkPolyBinOp Times anyNumberType e1 e2 pos
checkBinOp Divide e1 e2 pos = checkPolyBinOp Divide anyNumberType e1 e2 pos
checkBinOp Mod e1 e2 pos = checkPolyBinOp Mod anyIntType e1 e2 pos
checkBinOp Quot e1 e2 pos = checkPolyBinOp Quot anyIntType e1 e2 pos
checkBinOp Rem e1 e2 pos = checkPolyBinOp Rem anyIntType e1 e2 pos
checkBinOp ShiftR e1 e2 pos = checkPolyBinOp ShiftR anyIntType e1 e2 pos
checkBinOp ZShiftR e1 e2 pos = checkPolyBinOp ZShiftR anyIntType e1 e2 pos
checkBinOp ShiftL e1 e2 pos = checkPolyBinOp ShiftL anyIntType e1 e2 pos
checkBinOp Band e1 e2 pos = checkPolyBinOp Band anyIntType e1 e2 pos
checkBinOp Xor e1 e2 pos = checkPolyBinOp Xor anyIntType e1 e2 pos
checkBinOp Bor e1 e2 pos = checkPolyBinOp Bor anyIntType e1 e2 pos
checkBinOp LogAnd e1 e2 pos = checkPolyBinOp LogAnd [Prim Bool] e1 e2 pos
checkBinOp LogOr e1 e2 pos = checkPolyBinOp LogOr [Prim Bool] e1 e2 pos
checkBinOp Equal e1 e2 pos = checkRelOp Equal anyNumberType e1 e2 pos
checkBinOp NotEqual e1 e2 pos = checkRelOp NotEqual anyNumberType e1 e2 pos
checkBinOp Less e1 e2 pos = checkRelOp Less anyNumberType e1 e2 pos
checkBinOp Leq e1 e2 pos = checkRelOp Leq anyNumberType e1 e2 pos
checkBinOp Greater e1 e2 pos = checkRelOp Greater anyNumberType e1 e2 pos
checkBinOp Geq e1 e2 pos = checkRelOp Geq anyNumberType e1 e2 pos

checkRelOp :: BinOp -> [Type]
           -> ExpBase NoInfo VName -> ExpBase NoInfo VName -> SrcLoc
           -> TypeM Exp
checkRelOp op tl e1 e2 pos = do
  e1' <- require tl =<< checkExp e1
  e2' <- require tl =<< checkExp e2
  _ <- unifyExpTypes e1' e2'
  return $ BinOp op e1' e2' (Info $ Prim Bool) pos

checkPolyBinOp :: BinOp -> [Type]
               -> ExpBase NoInfo VName -> ExpBase NoInfo VName -> SrcLoc
               -> TypeM Exp
checkPolyBinOp op tl e1 e2 pos = do
  e1' <- require tl =<< checkExp e1
  e2' <- require tl =<< checkExp e2
  t' <- unifyExpTypes e1' e2'
  return $ BinOp op e1' e2' (Info t') pos

sequentially :: TypeM a -> (a -> Dataflow -> TypeM b) -> TypeM b
sequentially m1 m2 = do
  (a, m1flow) <- collectDataflow m1
  (b, m2flow) <- collectDataflow $ m2 a m1flow
  occur $ usageOccurences m1flow `seqOccurences`
          usageOccurences m2flow
  return b

checkBinding :: PatternBase NoInfo VName -> Type -> Dataflow
             -> TypeM (TypeM a -> TypeM a, Pattern)
checkBinding pat et dflow = do
  (pat', idds) <-
    runStateT (checkBinding' pat et) []
  return (\m -> sequentially (tell dflow) (const . const $ binding idds m), pat')
  where checkBinding' (Id (Ident name NoInfo pos)) t = do
          let t' = typeOf $ Var $ Ident name (Info t) pos
          add $ Ident name (Info t') pos
          return $ Id $ Ident name (Info t') pos
        checkBinding' (TuplePattern pats pos) (Tuple ts)
          | length pats == length ts = do
          pats' <- zipWithM checkBinding' pats ts
          return $ TuplePattern pats' pos
        checkBinding' (Wildcard NoInfo loc) t =
          return $ Wildcard (Info t) loc
        checkBinding' _ _ =
          lift $ bad $ InvalidPatternError
                       (untagPattern errpat) (toStructural et)
                       Nothing $ srclocOf pat

        add ident = do
          bnd <- gets $ find (==ident)
          case bnd of
            Nothing -> modify (ident:)
            Just (Ident name _ pos2) ->
              lift $ bad $ DupPatternError (baseName name) (srclocOf ident) pos2
        -- A pattern with known type box (NoInfo) for error messages.
        errpat = rmTypes pat
        rmTypes (Id (Ident name _ pos)) = Id $ Ident name NoInfo pos
        rmTypes (TuplePattern pats pos) = TuplePattern (map rmTypes pats) pos
        rmTypes (Wildcard _ loc) = Wildcard NoInfo loc

validApply :: [StructTypeBase VName] -> [Type] -> Bool
validApply expected got =
  length got == length expected &&
  and (zipWith subtypeOf (map toStructural got) (map toStructural expected))

type Arg = (Type, Dataflow, SrcLoc)

argType :: Arg -> Type
argType (t, _, _) = t

checkArg :: ExpBase NoInfo VName -> TypeM (Exp, Arg)
checkArg arg = do (arg', dflow) <- collectDataflow $ checkExp arg
                  return (arg', (typeOf arg', dflow, srclocOf arg'))

checkFuncall :: Maybe Name -> SrcLoc
             -> [StructType] -> StructType -> [Arg]
             -> TypeM ()
checkFuncall fname loc paramtypes _ args = do
  let argts = map argType args

  unless (validApply paramtypes argts) $
    bad $ ParameterMismatch fname loc
          (Right $ map toStructural paramtypes) (map toStructural argts)

  forM_ (zip (map diet paramtypes) args) $ \(d, (t, dflow, argloc)) -> do
    maybeCheckOccurences $ usageOccurences  dflow
    let occurs = consumeArg argloc t d
    occur $ usageOccurences dflow `seqOccurences` occurs

consumeArg :: SrcLoc -> Type -> Diet -> [Occurence]
consumeArg loc (Tuple ets) (TupleDiet ds) =
  concat $ zipWith (consumeArg loc) ets ds
consumeArg loc at Consume = [consumption (aliases at) loc]
consumeArg loc at _       = [observation (aliases at) loc]

checkLambda :: LambdaBase NoInfo VName -> [Arg]
            -> TypeM Lambda
checkLambda (AnonymFun params body ret pos) args = do
  params' <- mapM checkParam params
  case () of
    _ | length params == length args -> do
          FunDef _ _ ret' params'' body' _ <-
            noUnique $ checkFun $ FunDef False (nameFromString "<anonymous>") ret params body pos
          checkFuncall Nothing pos (map paramType params') (unInfo $ expandedType ret') args
          return $ AnonymFun params'' body' ret' pos
      | [(Tuple ets, _, _)] <- args,
        validApply (map paramType params') ets -> do
          -- The function expects N parameters, but the argument is a
          -- single N-tuple whose types match the parameters.
          -- Generate a shim to make it fit.
          FunDef _ _ ret' _ body' _ <-
            noUnique $ checkFun $ FunDef False (nameFromString "<anonymous>") ret params body pos
          tupident <- newIdent "tup_shim"
                      (Tuple $ map (fromStruct .
                                    removeShapeAnnotations .
                                    paramType) params')
                      pos
          let untype ident = ident { identType = NoInfo }
              paramtype = Tuple $ map paramDeclaredType params
              tupparam = Param (identName tupident) (TypeDecl paramtype NoInfo) $
                         srclocOf tupident
              tupfun = AnonymFun [tupparam] tuplet ret pos
              tuplet = LetPat (TuplePattern (map (Id . untype . fromParam) params') pos)
                              (Var $ untype tupident) body pos
          _ <- checkLambda tupfun args
          return $ AnonymFun params' body' ret' pos
      | otherwise -> bad $ TypeError pos $ "Anonymous function defined with " ++ show (length params') ++ " parameters, but expected to take " ++ show (length args) ++ " arguments."

checkLambda (CurryFun fname curryargexps _ pos) args = do
  (curryargexps', curryargs) <- unzip <$> mapM checkArg curryargexps
  bnd <- asks $ HM.lookup fname . envFtable
  case bnd of
    Nothing -> bad $ UnknownFunctionError fname pos
    Just (rt, paramtypes) -> do
      let rettype' = fromStruct $ removeShapeAnnotations rt
          paramtypes' = map (fromStruct . removeShapeAnnotations) paramtypes
      case () of
        _ | [(Tuple ets, _, _)] <- args,
            validApply paramtypes ets -> do
              -- Same shimming as in the case for anonymous functions.
              let mkparam i t = newIdent ("param_" ++ show i) t pos

              params <- zipWithM mkparam [(0::Int)..] paramtypes'
              paramname <- newIDFromString "x"

              let paramtype = Tuple paramtypes
                  tupparam = Param paramname (TypeDecl paramtype NoInfo) pos
                  tuplet = LetPat (TuplePattern (map (Id . untype) params) pos)
                           (Var $ Ident paramname NoInfo pos) body pos
                  tupfun = AnonymFun [tupparam] tuplet
                           (TypeDecl (vacuousShapeAnnotations rt) NoInfo) pos
                  body = Apply fname [(Var $ untype param, diet paramt) |
                                      (param, paramt) <- zip params paramtypes']
                         NoInfo pos
              checkLambda tupfun args
          | otherwise -> do
              case find (unique . snd) $ zip curryargexps paramtypes of
                Just (e, _) -> bad $ CurriedConsumption fname $ srclocOf e
                _           -> return ()
              let mkparam i t = newParam ("param_" ++ show i) t pos
                  asIdent p = Ident (paramName p) NoInfo $ srclocOf p
              params <- zipWithM mkparam [(0::Int)..] $
                        drop (length curryargs) paramtypes'
              let fun = AnonymFun params body
                        (TypeDecl (vacuousShapeAnnotations rt) NoInfo) pos
                  body = Apply fname (zip (curryargexps++map (Var . asIdent) params) $
                                      map diet paramtypes)
                         NoInfo pos
              _ <- checkLambda fun args
              return $ CurryFun fname curryargexps' (Info rettype') pos
    where untype ident = ident { identType = NoInfo }

checkLambda (UnOpFun unop NoInfo NoInfo loc) [arg] = do
  var <- newIdent "x" (argType arg) loc
  binding [var] $ do
    e <- checkExp $ UnOp unop (Var var { identType = NoInfo }) loc
    return $ UnOpFun unop (Info (argType arg)) (Info (typeOf e)) loc

checkLambda (UnOpFun unop NoInfo NoInfo loc) args =
  bad $ ParameterMismatch (Just $ nameFromString $ ppUnOp unop) loc (Left 1) $
  map (toStructural . argType) args

checkLambda (BinOpFun op NoInfo NoInfo NoInfo loc) args =
  checkPolyLambdaOp op [] args loc

checkLambda (CurryBinOpLeft binop x _ _ loc) [arg] = do
  x' <- checkExp x
  y <- newIdent "y" (argType arg) loc
  xvar <- newIdent "x" (typeOf x') loc
  binding [y, xvar] $ do
    e <- checkExp $ BinOp binop (Var $ untype xvar) (Var $ untype y) NoInfo loc
    return $ CurryBinOpLeft binop x' (Info $ argType arg) (Info $ typeOf e) loc
  where untype (Ident name _ varloc) = Ident name NoInfo varloc

checkLambda (CurryBinOpLeft binop _ _ _ loc) args =
  bad $ ParameterMismatch (Just $ nameFromString $ ppBinOp binop) loc (Left 1) $
  map (toStructural . argType) args

checkLambda (CurryBinOpRight binop x _ _ loc) [arg] = do
  x' <- checkExp x
  y <- newIdent "y" (argType arg) loc
  xvar <- newIdent "x" (typeOf x') loc
  binding [y, xvar] $ do
    e <- checkExp $ BinOp binop (Var $ untype y) (Var $ untype xvar) NoInfo loc
    return $ CurryBinOpRight binop x' (Info $ argType arg) (Info $ typeOf e) loc
  where untype (Ident name _ varloc) = Ident name NoInfo varloc

checkLambda (CurryBinOpRight binop _ _ _ loc) args =
  bad $ ParameterMismatch (Just $ nameFromString $ ppBinOp binop) loc (Left 1) $
  map (toStructural . argType) args

checkPolyLambdaOp :: BinOp -> [ExpBase NoInfo VName] -> [Arg] -> SrcLoc
                  -> TypeM Lambda
checkPolyLambdaOp op curryargexps args pos = do
  curryargexpts <- map typeOf <$> mapM checkExp curryargexps
  let argts = [ argt | (argt, _, _) <- args ]
  tp <- case curryargexpts ++ argts of
          [t1, t2] | t1 == t2 -> return t1
          [Tuple [t1,t2]] | t1 == t2 -> return t1 -- For autoshimming.
          l -> bad $ ParameterMismatch (Just fname) pos (Left 2) $ map toStructural l
  xname <- newIDFromString "x"
  yname <- newIDFromString "y"
  let xident t = Ident xname t pos
      yident t = Ident yname t pos
      untype p = p { paramTypeDecl = TypeDecl (paramDeclaredType p) NoInfo }
  (x,y,params) <- case curryargexps of
                    [] -> return (Var $ xident NoInfo,
                                  Var $ yident NoInfo,
                                  [xident $ Info tp, yident $ Info tp])
                    [e] -> return (e,
                                   Var $ yident NoInfo,
                                   [yident $ Info tp])
                    (e1:e2:_) -> return (e1, e2, [])
  body <- binding (map (fromParam . toParam) params) $ checkBinOp op x y pos
  checkLambda
    (AnonymFun (map (untype . toParam) params) (BinOp op x y NoInfo pos)
     (TypeDecl (vacuousShapeAnnotations $ toStruct $ typeOf body) NoInfo) pos)
    args
  where fname = nameFromString $ ppBinOp op

checkRetType :: SrcLoc -> StructType -> TypeM ()
checkRetType loc (Tuple ts) = mapM_ (checkRetType loc) ts
checkRetType _ (Prim _) = return ()
checkRetType loc (Array at) =
  checkArrayType loc at

checkArrayType :: SrcLoc
               -> DeclArrayTypeBase VName
               -> TypeM ()
checkArrayType loc (PrimArray _ ds _ _) =
  mapM_ (checkDim loc) $ shapeDims ds
checkArrayType loc (TupleArray cts ds _) = do
  mapM_ (checkDim loc) $ shapeDims ds
  mapM_ (checkTupleArrayElem loc) cts

checkTupleArrayElem :: SrcLoc
                    -> DeclTupleArrayElemTypeBase VName
                    -> TypeM ()
checkTupleArrayElem _ PrimArrayElem{} =
  return ()
checkTupleArrayElem loc (ArrayArrayElem at) =
  checkArrayType loc at
checkTupleArrayElem loc (TupleArrayElem cts) =
  mapM_ (checkTupleArrayElem loc) cts

checkDim :: SrcLoc -> DimDecl VName -> TypeM ()
checkDim _ AnyDim =
  return ()
checkDim _ (ConstDim _) =
  return ()
checkDim loc (NamedDim name) = do
  t <- lookupVar name loc
  case t of
    Prim (Signed Int32) -> return ()
    _                   -> bad $ DimensionNotInteger loc $ baseName name

patternType :: Pattern -> Type
patternType (Wildcard (Info t) _) = t
patternType (Id ident) = unInfo $ identType ident
patternType (TuplePattern pats _) = Tuple $ map patternType pats


 -- | resolveUserTypes :: UncheckedPreProg -> Prog
 -- | resolveUserTypes prog =
 -- |   let
 -- |     unresolveds = map f prog
 -- |     unresolvedTAs = rights unresolveds
 -- |     unresolvedFunDefs = lefts unresolveds
 -- |     aliasMap = typeAliasTableFromProg unresolvedTAs
 -- |     resolvedFunDefs = map (\fun -> resolveFunTypes fun aliasMap) unresolvedFunDefs
 -- |    in
 -- |     resolvedFunDefs
 -- |   where f (FunDec a) = Left (FunDec a)
 -- |         f (TypeDec a) = Right (TypeDec a)
 -- | 
 -- | resolveFunTypes :: FunDefBase f vn -> AliasMap shape as vn -> FunDefBase f vn
 -- | resolveFunTypes (FunDef ent name userRetType userParams body loc) aliasMap =
 -- |   let retType = lookupTypeBase userRetType aliasMap
 -- |       params = resolveParams userParams aliasMap
 -- |    in FunDef ent name retType params body loc
 -- | 
 -- | resolveParams :: [ParamBase f vn] -> AliasMap shape as vn -> [ParamBase f vn]
 -- | resolveParams userParams aliasMap =
 -- |   map (\(Param name typeDecl loc)
 -- |        -> Param name (lookupTypeBase typeDecl aliasMap) loc) userParams
 -- | 
 -- | lookupTypeBases = map (\someType aliasMap -> lookupTypeBase someType aliasMap)
 -- | 
 -- | lookupTypeBase :: TypeBase shape as vn -> AliasMap shape as vn -> Either TypeError (TypeBase shape as vn)
 -- | lookupTypeBase (Prim primtype) _ =
 -- |   Right $ Prim primtype
 -- | lookupTypeBase (Array arraytypebase) typeEnv =
 -- |   case lookupArrayTypeBase arraytypebase typeEnv
 -- |     of
 -- |       Left error
 -- |         -> Left error
 -- |       Right arraytypebase'
 -- |         -> Right $ Array arraytypebase'
 -- | 
 -- | lookupTypeBase (Tuple typebases) aliasMap =
 -- |   let typebases' = lookupTypeBases typebases aliasMap
 -- |    in if (Left error) `elem` typebases'
 -- |        then Left error
 -- |       else Right typebases'
 -- | 
 -- | lookupTupleArrayTypes :: [TupleArrayElemTypeBase shape as vn]
 -- |                       -> AliasMap shape as vn 
 -- |                       -> Either TypeError [TupleArrayElemTypeBase shape as vn]
 -- | lookupTupleArrayTypes types typeEnv = do
 -- |   types' <- map f types
 -- |   if (Left error) `elem` types'
 -- |     then Left error
 -- |   else Right types'
 -- | 
 -- | 
 -- |   where
 -- |     f (PrimArrayElem primtype _) = PrimArrayElem primtype NoInfo
 -- |     f (ArrayArrayElem arrayTypeBase) = ArrayArrayElem (lookupArrayTypeBase arrayTypeBase typeEnv)
 -- |     f (TupleArrayElem tupleArrayTypeBases) = TupleArrayElem (lookupArrayTypeBase tupleArrayTypeBases typeEnv)
 -- | 
 -- | 
 -- | lookupArrayTypeBase :: ArrayTypeBase shape as vn
 -- |                     -> AliasMap shape as vn
 -- |                     -> Either TypeError (ArrayTypeBase shape as vn)
 -- | lookupArrayTypeBase arrayTypeBase aliasMap =
 -- |   case arrayTypeBase
 -- |     of PrimArray a
 -- |          -> Right $ arrayTypeBase
 -- |        TupleArray tupleArrayElems shapedecl unique
 -- |          -> let
 -- |               tupleArrayElems' = lookupTupleArrayElems tupleArrayElems aliasMap
 -- |              in
 -- |               Right $ TupleArray tupleArrayElems' shapedecl unique
 -- |  -- |        UserAliasArray name svn uniqueness avn
 -- |  -- |          -> case HM.lookup name aliasMap
 -- |  -- |               of Just (Prim a)
 -- |  -- |                    -> Right $ PrimArray a svn uniqueness avn
 -- |  -- |                  Just (Tuple types)
 -- |  -- |                    -> let types' = map typeBaseToTupleArrayElemTypeBase types
 -- |  -- |                        in Right $ TupleArray (types') svn uniqueness
 -- |  -- |                  Nothing -> Left $ UndefinedAlias' name
 -- | 
 -- | lookupTupleArrayElems = map (\tupleArrayElem aliasMap -> lookupTupleArrayElem tupleArrayElem aliasMap)
 -- | lookupTupleArrayElem (PrimArrayElem a) _ = PrimArrayElem a
 -- | lookupTupleArrayElem (ArrayArrayElem a) aliasMap = ArrayArrayElem (lookupArrayTypeBase a aliasMap)
 -- | lookupTupleArrayElem (TupleArrayElem a) aliasMap = TupleArrayElem (lookupTupleArrayElems a aliasMap)
 -- |
typeAliasTableFromProg :: UncheckedProg
                       -> Either TypeError TypeAliasMap

typeAliasTableFromProg prog =
  let
    baseMap  = f $ progTypes prog
    typeList = map g $ progTypes prog
    taTable  = typeAliasTableFromProg' typeList baseMap HM.empty
   in
    stripEithersFromtaTable taTable
  where
    f typeList =
      foldr (\(TypeDef name (UserTypeDecl usertype) _) hashmap -> HM.insert name usertype hashmap) HM.empty typeList
    g (TypeDef name (UserTypeDecl _) srcloc) =
      (name, srcloc)

typeAliasTableFromProg' :: [(Name, SrcLoc)]
                        -> HM.HashMap Name (UserType shape vn)
                        -> (AliasMap shape vn)
                        -> Either TypeError (AliasMap shape vn)

typeAliasTableFromProg' [] _ aliasMap = Right aliasMap
typeAliasTableFromProg' ((name, srcloc):rest) hashmap aliasMap =
   case (HM.lookup name hashmap, HM.lookup name aliasMap) of
     (Just userType, Nothing)
       -> case typeBaseFromUserType (name, userType, srcloc) hashmap [name] of
            (Left error)
              -> Left error
            (Right someUserType)
              -> typeAliasTableFromProg' rest hashmap $ HM.insert name someUserType aliasMap
     (_, Just a)
       -> Left $ DupTypeAlias srcloc name

typeBaseFromUserType :: (Name, UserType shape vn, SrcLoc)
                     -> HM.HashMap Name (UserType shape vn)
                     -> [Name]
                     -> Either TypeError (UserType shape vn)
typeBaseFromUserType (name, userType, srcloc) hashmap unknowns =
  case userType of
    UserPrim somePrim
      -> Right $ UserPrim somePrim
    UserArray someType shape uniq
      -> case typeBaseFromUserType (name, someType, srcloc) hashmap unknowns
           of Left e
                -> Left e
              Right someTypeBase
                -> let Right res = typeBaseFromUserType (name, someTypeBase, srcloc) hashmap unknowns
                    in Right $ UserArray res shape uniq
    UserTuple someTypes
      -> case typeBasesFromUserTypes (name, someTypes, srcloc) hashmap unknowns
           of Left e -> Left e
              Right typeBases -> Right $ UserTuple typeBases
    UserTypeAlias someAlias
      -> if someAlias `elem` unknowns
           then Left $ CyclicalTypeDefinition srcloc name
         else typeBaseFromTypeAlias (someAlias, srcloc) hashmap unknowns

typeBaseFromTypeAlias :: (Name, SrcLoc)
                      -> HM.HashMap Name (UserType shape vn)
                      -> [Name]
                      -> Either TypeError (UserType shape vn)
typeBaseFromTypeAlias (name, loc) hashmap unknowns =
  case HM.lookup name hashmap
    of Just (UserPrim somePrim)
         -> Right $ UserPrim somePrim
       Just (UserArray someType shape uniq)
         -> case (typeBaseFromUserType (name, someType, loc) hashmap unknowns) of
              Right someTypes
                -> Right $ UserArray someTypes shape uniq
              Left error
                -> Left error
       Just (UserTuple someTypes)
         -> case typeBasesFromUserTypes (name, someTypes, loc) hashmap unknowns
              of Left error -> Left error
                 Right types -> Right $ UserTuple types
       Just (UserTypeAlias someAlias)
         -> typeBaseFromUserType (name, UserTypeAlias someAlias, loc) hashmap $ name:unknowns
       Nothing -> Left $ UndefinedAlias loc name

typeBasesFromUserTypes :: (Name, [UserType shape vn], SrcLoc)
                       -> HM.HashMap Name (UserType shape vn)
                       -> [Name]
                       -> Either TypeError ([UserType shape vn])
typeBasesFromUserTypes (name, userTypes, srcloc) hashmap unknowns =
  let
    f = (\userType -> typeBaseFromUserType (name, userType, srcloc) hashmap unknowns)
    tupleBaseTypes = map f userTypes
    errors = lefts tupleBaseTypes
    types = rights tupleBaseTypes
   in
     case errors of
       (error:_) -> Left error
       []        -> Right types

checkEitherList :: [Either a b] -> Either a [b]
checkEitherList list =
  let
    errors = lefts list
    types  = rights list
  in
  case errors of (x:_) -> Left x
                 _     -> Right types

 -- | userTypeBaseToArrayTypeBase :: (Name, (UserType shape vn), SrcLoc)
 -- |                             -> Uniqueness
 -- |                             -> HM.HashMap Name (UserType shape vn)
 -- |                             -> [Name]
 -- |                             -> Either TypeError (ArrayTypeBase shape as vn)
 -- | userTypeBaseToArrayTypeBase (UserPrim somePrim) uniq hashmap unknowns =
 -- |   Right $ PrimArray somePrim AnyDim uniq
 -- | userTypeBaseToArrayTypeBase (UserTuple someTypes) uniq hashmap unknowns =
 -- |   let someTypes'  = typeBasesFromUserTypes (name, someTypes, srcloc) hashmap unknowns
 -- |       someTypes'' = userTypesToArrayElemTypeBases (someTypes') hashmap unknowns
 -- | 
 -- |   in Right $ TupleArray someTypes' AnyDim uniq
 -- | 
---- | An array type.
--data ArrayTypeBase shape as vn =
--    PrimArray PrimType (shape vn) Uniqueness (as vn)
--    -- ^ An array whose elements are primitive types.
--  | TupleArray [TupleArrayElemTypeBase shape as vn] (shape vn) Uniqueness
--    -- ^ An array whose elements are tuples.
--    deriving (Show)
--
-- PrimArray

-- TupleArray

-- |
-- |
-- | userTypeToTupleArrayElemTypeBase :: (UserType shape vn)
-- |                                  -> Uniqueness
-- |                                  -> HM.HashMap Name (UserType shape vn)
-- |                                  -> [Name]
-- |                                  -> Either TypeError (TupleArrayElemTypeBase shape as vn)
-- | userTypeToTupleArrayElemTypeBase (UserPrim somePrim) _ _ _ =
-- |   Right $ PrimArrayElem somePrim ()
-- | userTypeToTupleArrayElemTypeBase (UserArray someType) unq hashmap unknowns =
-- |
-- | -- | -- | Types that can be elements of tuple-arrays.
-- | -- | data TupleArrayElemTypeBase shape as vn =
-- | -- |      PrimArrayElem PrimType (as vn)
-- | -- |    | ArrayArrayElem (ArrayTypeBase shape as vn)
-- | -- |    | TupleArrayElem [TupleArrayElemTypeBase shape as vn]
-- | -- |       deriving (Show)
-- |
-- |  -- PrimArrayElem
-- |
-- |  -- ArrayArrayElem
-- |
-- |  -- TupleArrayElem
-- |
--  userTypesToArrayElemTypeBases userTypes hashmap unknowns =
--    map (\userType -> userTypeToTupleArrayElemTypeBase userType unq)


stripEithersFromtaTable :: a -> Either TypeError TypeAliasMap
stripEithersFromtaTable a = undefined
