{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts, ScopedTypeVariables #-}
-- | The type checker checks whether the program is type-consistent.
module Futhark.TypeCheck
  ( -- * Interface
    checkProg
  , checkProgNoUniqueness
  , TypeError
  , ErrorCase
    -- * Extensionality
  , TypeM
  , bad
  , context
  , message
  , Checkable (..)
  , module Futhark.TypeCheck.TypeError
  , lookupVar
  , VarBindingLore (..)
    -- * Checkers
  , require
  , requireI
  , checkSubExp
  , checkExtType
  , matchExtPattern
  , matchExtReturnType
  )
  where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.RWS
import Data.Loc (noLoc)
import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe

import Prelude

import qualified Futhark.Representation.AST.Annotations as Annotations
import qualified Futhark.Representation.AST as AST
import Futhark.Representation.Aliases hiding (TypeEnv)
import Futhark.TypeCheck.TypeError
import Futhark.Analysis.Alias
import qualified Futhark.Util.Pretty as PP

-- | Information about an error that occured during type checking.
data TypeError lore = Error [String] (ErrorCase lore)

-- | What went wrong.
type ErrorCase lore =
  GenTypeError VName (Exp lore) (Several ExtType) (Several (PatElemT (Annotations.LetBound lore)))

instance PrettyLore lore => Show (TypeError lore) where
  show (Error [] err) =
    show err
  show (Error msgs err) =
    intercalate "\n" msgs ++ "\n" ++ show err

-- | A tuple of a return type and a list of parameters, possibly
-- named.
type FunBinding lore = (RetType lore, [FParam lore])

data VarBindingLore lore = LetBound (Annotations.LetBound lore)
                         | FunBound (Annotations.FParam lore)
                         | LambdaBound (Annotations.LParam lore)

data VarBinding lore = Bound Type (VarBindingLore lore) Names
                     | WasConsumed

data Usage = Consumed
           | Observed
             deriving (Eq, Ord, Show)

data Occurence = Occurence { observed :: Names
                           , consumed :: Names
                           }
             deriving (Eq, Show)

observation :: Names -> Occurence
observation = flip Occurence HS.empty

consumption :: Names -> Occurence
consumption = Occurence HS.empty

nullOccurence :: Occurence -> Bool
nullOccurence occ = HS.null (observed occ) && HS.null (consumed occ)

type Occurences = [Occurence]

type UsageMap = HM.HashMap VName [Usage]

usageMap :: Occurences -> UsageMap
usageMap = foldl comb HM.empty
  where comb m (Occurence obs cons) =
          let m' = HS.foldl' (ins Observed) m obs
          in HS.foldl' (ins Consumed) m' cons
        ins v m k = HM.insertWith (++) k [v] m

combineOccurences :: VName -> Usage -> Usage
                  -> Either (ErrorCase lore) Usage
combineOccurences _ Observed Observed = Right Observed
combineOccurences name Consumed Observed =
  Left $ UseAfterConsume name noLoc noLoc
combineOccurences name Observed Consumed =
  Left $ UseAfterConsume name noLoc noLoc
combineOccurences name Consumed Consumed =
  Left $ UseAfterConsume name noLoc noLoc

checkOccurences :: Occurences
                -> Either (ErrorCase lore) ()
checkOccurences = void . HM.traverseWithKey comb . usageMap
  where comb _    []     = Right ()
        comb name (u:us) = foldM_ (combineOccurences name) u us

allConsumed :: Occurences -> Names
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

-- | The environment contains a variable table and a function table.
-- Type checking happens with access to this environment.  The
-- function table is only initialised at the very beginning, but the
-- variable table will be extended during type-checking when
-- let-expressions are encountered.
data TypeEnv lore =
  TypeEnv { envVtable :: HM.HashMap VName (VarBinding lore)
          , envFtable :: HM.HashMap Name (FunBinding lore)
          , envCheckOccurences :: Bool
          , envContext :: [String]
          }

-- | The type checker runs in this monad.
newtype TypeM lore a = TypeM (RWST
                              (TypeEnv lore)     -- Reader
                              Dataflow           -- Writer
                              ()                 -- State
                              (Either (TypeError lore)) -- Inner monad
                              a)
  deriving (Monad, Functor, Applicative,
            MonadReader (TypeEnv lore),
            MonadWriter Dataflow)

instance HasTypeEnv (TypeM lore) where
  lookupType name = do (t, _, _) <- lookupVar name
                       return t
  askTypeEnv = asks $ HM.fromList . mapMaybe varType . HM.toList . envVtable
    where varType (name, Bound t _ _ ) = Just (name, t)
          varType (_,    WasConsumed)  = Nothing

runTypeM :: TypeEnv lore -> TypeM lore a
         -> Either (TypeError lore) a
runTypeM env (TypeM m) = fst <$> evalRWST m env ()

bad :: ErrorCase lore -> TypeM lore a
bad e = do
  messages <- asks envContext
  TypeM $ lift $ Left $ Error (reverse messages) e

-- | Add information about what is being type-checked to the current
-- context.  Liberal use of this combinator makes it easier to track
-- type errors, as the strings are added to type errors signalled via
-- 'bad'.
context :: String
          -> TypeM lore a
          -> TypeM lore a
context s = local $ \env -> env { envContext = s : envContext env}

message :: PP.Pretty a =>
           String -> a -> String
message s x = PP.prettyDoc 80 $
              PP.text s PP.<+> PP.align (PP.ppr x)

liftEither :: Either (ErrorCase lore) a -> TypeM lore a
liftEither = either bad return

liftEitherS :: Either String a -> TypeM lore a
liftEitherS = either (bad . TypeError noLoc) return

occur :: Occurences -> TypeM lore ()
occur occurs = tell Dataflow { usageOccurences = occurs }

-- | Proclaim that we have made read-only use of the given variable.
-- No-op unless the variable is array-typed.
observe :: VName -> TypeM lore ()
observe name = do
  (t, _, names) <- lookupVar name
  unless (basicType t) $
    occur [observation names]

-- | Proclaim that we have written to the given variable.
consume :: Names -> TypeM lore ()
consume als = occur [consumption als]

collectDataflow :: TypeM lore a -> TypeM lore (a, Dataflow)
collectDataflow m = pass $ do
  (x, dataflow) <- listen m
  return ((x, dataflow), const mempty)

noDataflow :: TypeM lore a -> TypeM lore a
noDataflow = censor $ const mempty

maybeCheckOccurences :: Occurences -> TypeM lore ()
maybeCheckOccurences us = do
  check <- asks envCheckOccurences
  when check $ liftEither $ checkOccurences us

alternative :: TypeM lore a -> TypeM lore b -> TypeM lore (a,b)
alternative m1 m2 = pass $ do
  (x, Dataflow occurs1) <- listen m1
  (y, Dataflow occurs2) <- listen m2
  maybeCheckOccurences occurs1
  maybeCheckOccurences occurs2
  let usage = Dataflow $ occurs1 `altOccurences` occurs2
  return ((x, y), const usage)

-- | Ban consumption of anything free.
noConsume :: TypeM lore a -> TypeM lore a
noConsume m = do
  (x, dflow) <- collectDataflow m
  tell dflow
  mapM_ nothingConsumed $ usageOccurences dflow
  return x
  where nothingConsumed occurence
          | HS.null cons =
            return ()
          | otherwise =
              bad $ TypeError noLoc $
              "Variables " ++
              intercalate ", " (map pretty $ HS.toList cons) ++
              " consumed inside loop."
          where cons = consumed occurence

-- | Given the immediate aliases, compute the full transitive alias
-- set (including the immediate aliases).
expandAliases :: Names -> TypeEnv lore -> Names
expandAliases names env = names `HS.union` aliasesOfAliases
  where aliasesOfAliases =  mconcat . map look . HS.toList $ names
        look k = case HM.lookup k $ envVtable env of
          Just (Bound _ _ als) -> als
          _                    -> mempty

binding :: Checkable lore =>
           [((Ident, VarBindingLore lore), Names)]
        -> TypeM lore a
        -> TypeM lore a
binding bnds = check . local (`bindVars` bnds)
  where bindVars = foldl bindVar
        boundnames = map (identName . fst . fst) bnds
        boundnameset = HS.fromList boundnames

        bindVar env ((Ident name tp, attr), immediate) =
          let names = expandAliases immediate env
              inedges = HS.toList names
              update (Bound tp' thisattr thesenames) =
                Bound tp' thisattr $ HS.insert name thesenames
              update b = b
          in env { envVtable =
                      HM.insert name (Bound tp attr names) $
                      adjustSeveral update inedges $
                      envVtable env
                 }

        adjustSeveral f = flip $ foldl $ flip $ HM.adjust f

        -- Check whether the bound variables have been used correctly
        -- within their scope.
        check m = do
          already_bound <- asks envVtable
          case filter ((`HM.member` already_bound) . identName . fst . fst) bnds of
            []  -> return ()
            ((v, _),_):_ -> bad $ TypeError noLoc $
                            "Variable " ++ pretty v ++ " being redefined."
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
                divide s = (s `HS.intersection` boundnameset,
                            s `HS.difference` boundnameset)

lookupVar :: VName -> TypeM lore (Type, VarBindingLore lore, Names)
lookupVar name = do
  bnd <- asks $ HM.lookup name . envVtable
  case bnd of
    Nothing -> bad $ UnknownVariableError name noLoc
    Just (Bound t lore names) -> return (t, lore, names)
    Just WasConsumed          -> bad $ UseAfterConsume name noLoc noLoc

lookupAliases :: VName -> TypeM lore Names
lookupAliases name = do (_, _, als) <- lookupVar name
                        return $ HS.insert name als

subExpAliasesM :: SubExp -> TypeM lore Names
subExpAliasesM (Constant {}) = return mempty
subExpAliasesM (Var v)       = lookupAliases v

lookupFun :: forall lore.Lore lore =>
             Name
          -> [SubExp]
          -> TypeM lore (RetType lore, [Type])
lookupFun fname args = do
  bnd <- asks $ HM.lookup fname . envFtable
  case bnd of
    Nothing -> bad $ UnknownFunctionError fname noLoc
    Just (ftype, params) -> do
      argts <- mapM subExpType args
      case applyRetType (representative :: lore) ftype params $
           zip args argts of
        Nothing ->
          bad $ ParameterMismatch (Just fname) noLoc
          (Right $ map (justOne . staticShapes1 . paramType) params) $
          map (justOne . staticShapes1) argts
        Just rt ->
          return (rt, map paramType params)

-- | @t1 `unifyTypes` t2@ attempts to unify @t2@ and @t2@.  If
-- unification cannot happen, 'Nothing' is returned, otherwise a type
-- that combines the aliasing of @t1@ and @t2@ is returned.  The
-- uniqueness of the resulting type will be the least of the
-- uniqueness of @t1@ and @t2@.
unifyTypes :: Type -> Type -> Maybe Type
unifyTypes (Basic t1) (Basic t2) = Basic <$> t1 `unifyBasicTypes` t2
unifyTypes (Array t1 ds1 u1) (Array t2 ds2 u2)
  | shapeRank ds1 == shapeRank ds2 = do
  t <- t1 `unifyBasicTypes` t2
  Just $ Array t ds2 (u1 <> u2)
unifyTypes (Mem size1 space1) (Mem size2 space2)
  | size1 == size2, space1 == space2 = Just $ Mem size1 space1
unifyTypes _ _ = Nothing

-- | As 'unifyTypes', but for element types.
unifyBasicTypes :: BasicType -> BasicType -> Maybe BasicType
unifyBasicTypes t1 t2
  | t1 == t2  = Just t1
  | otherwise = Nothing

-- | Determine if two types are identical, ignoring uniqueness.
-- Causes a '(TypeError vn)' if they fail to match, and otherwise returns
-- one of them.
unifySubExpTypes :: SubExp -> SubExp -> TypeM lore Type
unifySubExpTypes e1 e2 = do
  t1 <- subExpType e1
  t2 <- subExpType e2
  maybe (bad $
         UnifyError (PrimOp $ SubExp e1) (justOne $ staticShapes1 t1)
                    (PrimOp $ SubExp e2) (justOne $ staticShapes1 t2))
        return $
        unifyTypes t1 t2

-- | @checkAnnotation loc s t1 t2@ checks if @t2@ is a subtype of
-- @t1@.  If not, a 'BadAnnotation' is raised.
checkAnnotation :: String -> Type -> Type
                -> TypeM lore ()
checkAnnotation desc t1 t2
  | t2 `subtypeOf` t1 = return ()
  | otherwise = bad $ BadAnnotation noLoc desc
                (justOne $ staticShapes1 t1) (justOne $ staticShapes1 t2)

-- | @require ts se@ causes a '(TypeError vn)' if the type of @se@ is
-- not a subtype of one of the types in @ts@.
require :: Checkable lore => [Type] -> SubExp -> TypeM lore ()
require ts se = do
  t <- checkSubExp se
  unless (any (t `subtypeOf`) ts) $
    bad $ UnexpectedType noLoc (PrimOp $ SubExp se)
    (justOne $ staticShapes1 t)
    (map (justOne . staticShapes1) ts)

-- | Variant of 'require' working on variable names.
requireI :: Checkable lore => [Type] -> VName -> TypeM lore ()
requireI ts ident = require ts $ Var ident

checkArrIdent :: VName -> TypeM lore Type
checkArrIdent v = do
  t <- lookupType v
  case t of
    (Array {}) -> return t
    _          -> bad $ NotAnArray noLoc (PrimOp $ SubExp $ Var v) $
                  justOne $ staticShapes1 t

-- | Type check a program containing arbitrary type information,
-- yielding either a type error or a program with complete type
-- information.
checkProg :: Checkable lore =>
             AST.Prog lore -> Either (TypeError lore) ()
checkProg = checkProg' True

-- | As 'checkProg', but don't check whether uniqueness constraints
-- are being upheld.  The uniqueness of types must still be correct.
checkProgNoUniqueness :: Checkable lore =>
                         AST.Prog lore -> Either (TypeError lore) ()
checkProgNoUniqueness = checkProg' False

checkProg' :: Checkable lore =>
              Bool -> AST.Prog lore -> Either (TypeError lore) ()
checkProg' checkoccurs prog = do
  ftable <- buildFtable
  let typeenv = TypeEnv { envVtable = HM.empty
                        , envFtable = ftable
                        , envCheckOccurences = checkoccurs
                        , envContext = []
                        }

  runTypeM typeenv $
    mapM_ (noDataflow . checkFun) $ progFunctions prog'
  where
    prog' = aliasAnalysis prog
    -- To build the ftable we loop through the list of function
    -- definitions.  In addition to the normal ftable information
    -- (name, return type, argument types), we also keep track of
    -- position information, in order to report both locations of
    -- duplicate function definitions.  The position information is
    -- removed at the end.
    buildFtable = foldM expand (initialFtable prog')
                  (progFunctions prog')
    expand ftable (FunDec name ret params _)
      | HM.member name ftable =
        Left $ Error [] $ DupDefinitionError name noLoc noLoc
      | otherwise =
        Right $ HM.insert name (ret,params) ftable

-- The prog argument is just to disambiguate the lore.
initialFtable :: forall lore.Checkable lore =>
                 Prog lore -> HM.HashMap Name (FunBinding lore)
initialFtable _ = HM.map addBuiltin builtInFunctions
  where addBuiltin (t, ts) =
          (basicRetType t,
           map (basicFParam (representative :: lore) name) ts)
        name = ID (nameFromString "x", 0)

checkFun :: Checkable lore =>
            FunDec lore -> TypeM lore ()
checkFun (FunDec fname rettype params body) =
  context ("In function " ++ nameToString fname) $
    checkFun' (fname,
               retTypeValues rettype,
               funParamsToIdentsAndLores params,
               body) $ do
      checkFunParams params
      checkRetType rettype
      checkFunBody fname rettype body

funParamsToIdentsAndLores :: Checkable lore =>
                             [FParam lore]
                          -> [(Ident, VarBindingLore lore)]
funParamsToIdentsAndLores = map identAndLore
  where identAndLore fparam = (paramIdent fparam,
                               FunBound $ paramLore fparam)

checkFunParams :: Checkable lore =>
                  [FParam lore] -> TypeM lore ()
checkFunParams = mapM_ $ \param ->
  context ("In function parameter " ++ pretty param) $
  checkFParamLore (paramIdent param) (paramLore param)

checkAnonymousFun :: Checkable lore =>
                     (Name, [Type], [LParam (Aliases lore)], BodyT (Aliases lore))
                  -> TypeM lore ()
checkAnonymousFun (fname, rettype, params, body) =
  checkFun' (fname,
             staticShapes rettype,
             [ (paramIdent param, LambdaBound $ paramLore param) | param <- params ],
             body) $ do
    mapM_ checkType rettype
    checkLambdaBody rettype body

checkFun' :: (Checkable lore) =>
             (Name,
              [ExtType],
              [(Ident, VarBindingLore lore)],
              BodyT (Aliases lore))
          -> TypeM lore ()
          -> TypeM lore ()
checkFun' (fname, rettype, paramsWithLore, body) check = do
  checkParams
  binding (zip paramsWithLore $ repeat mempty) check

  checkReturnAlias $ bodyAliases body
  where params = map fst paramsWithLore

        checkParams = foldM_ expand [] params

        expand params' ident@(Ident pname _)
          | Just _ <- find ((==identName ident) . identName) params' =
            bad $ DupParamError fname pname noLoc
          | otherwise =
            return $ ident : params'

        notAliasingParam names =
          forM_ params $ \p ->
            when (not (unique $ identType p) &&
                  identName p `HS.member` names) $
              bad $ ReturnAliased fname (identName p) noLoc

        -- | Check that unique return values do not alias a
        -- non-consumed parameter.
        checkReturnAlias =
          foldM_ checkReturnAlias' HS.empty .
          returnAliasing rettype

        checkReturnAlias' seen (Unique, names)
          | any (`HS.member` HS.map snd seen) $ HS.toList names =
            bad $ UniqueReturnAliased fname noLoc
          | otherwise = do
            notAliasingParam names
            return $ seen `HS.union` tag Unique names
        checkReturnAlias' seen (Nonunique, names)
          | any (`HS.member` seen) $ HS.toList $ tag Unique names =
            bad $ UniqueReturnAliased fname noLoc
          | otherwise = return $ seen `HS.union` tag Nonunique names

        tag u = HS.map $ \name -> (u, name)

        returnAliasing expected got =
          [ (uniqueness p, names) |
            (p,names) <- zip expected got ]

checkSubExp :: Checkable lore => SubExp -> TypeM lore Type
checkSubExp (Constant val) =
  return $ Basic $ basicValueType val
checkSubExp (Var ident) = context ("In subexp " ++ pretty ident) $ do
  observe ident
  lookupType ident

checkBindings :: Checkable lore =>
                 [Binding lore] -> TypeM lore a
              -> TypeM lore a
checkBindings origbnds m = delve origbnds
  where delve (Let pat (_,annot) e:bnds) = do
          ((), dataflow) <-
            collectDataflow $
            context ("In expression\n" ++ message "  " e) $
            checkExp e
          checkExpLore annot
          scope <-
            checkBinding pat e dataflow
          scope $
            delve bnds
        delve [] =
          m

checkResult :: Checkable lore =>
               Result -> TypeM lore ()
checkResult = mapM_ checkSubExp

checkFunBody :: Checkable lore =>
                Name
             -> RetType lore
             -> Body lore
             -> TypeM lore ()
checkFunBody fname rt (Body (_,lore) bnds res) = do
  checkBindings bnds $ do
    checkResult res
    matchReturnType fname rt res
  checkBodyLore lore

checkLambdaBody :: Checkable lore =>
                   [Type] -> Body lore -> TypeM lore ()
checkLambdaBody ret (Body (_,lore) bnds res) = do
  checkBindings bnds $ checkLambdaResult ret res
  checkBodyLore lore

checkLambdaResult :: Checkable lore =>
                     [Type] -> Result -> TypeM lore ()
checkLambdaResult ts es
  | length ts /= length es =
    bad $ TypeError noLoc $
    "Lambda has return type " ++ prettyTuple ts ++
    " describing " ++ show (length ts) ++ " values, but body returns " ++
    show (length es) ++ " values: " ++ prettyTuple es
  | otherwise = forM_ (zip ts es) $ \(t, e) -> do
      et <- checkSubExp e
      unless (et `subtypeOf` t) $
        bad $ TypeError noLoc $
        "Subexpression " ++ pretty e ++ " has type " ++ pretty et ++
        " but expected " ++ pretty t

checkBody :: Checkable lore =>
             Body lore -> TypeM lore ()
checkBody (Body (_,lore) bnds res) = do
  checkBindings bnds $ checkResult res
  checkBodyLore lore

checkPrimOp :: Checkable lore =>
               PrimOp lore -> TypeM lore ()

checkPrimOp (SubExp es) =
  void $ checkSubExp es

checkPrimOp (ArrayLit es t) = do
  mapM_ checkSubExp es
  -- Find the universal type of the array arguments.
  et <- case es of
          [] -> return t
          e:es' -> do
            let check elemt eleme = do
                  elemet <- subExpType eleme
                  case unifyTypes elemt elemet of
                    Just elemt' ->
                      return elemt'
                    Nothing ->
                      bad $ TypeError noLoc $ pretty elemet ++
                      " is not of expected type " ++ pretty elemt ++ "."
            et <- subExpType e
            foldM check et es'

  -- Unify that type with the one given for the array literal.
  checkAnnotation "array-element" t et

checkPrimOp (BinOp op e1 e2 t) = checkBinOp op e1 e2 t

checkPrimOp (Not e) =
  require [Basic Bool] e

checkPrimOp (Complement e) =
  require [Basic Int] e

checkPrimOp (Negate e) =
  require [Basic Int, Basic Float32, Basic Float64] e

checkPrimOp (Abs e) =
  require [Basic Int] e

checkPrimOp (Signum e) =
  require [Basic Int] e

checkPrimOp (Index cs ident idxes) = do
  mapM_ (requireI [Basic Cert]) cs
  vt <- lookupType ident
  observe ident
  when (arrayRank vt < length idxes) $
    bad $ IndexingError ident
          (arrayRank vt) (length idxes) noLoc
  mapM_ (require [Basic Int]) idxes

checkPrimOp (Iota e) =
  require [Basic Int] e

checkPrimOp (Replicate countexp valexp) = do
  require [Basic Int] countexp
  void $ checkSubExp valexp

checkPrimOp (Scratch _ shape) =
  mapM_ checkSubExp shape

checkPrimOp (Reshape cs newshape arrexp) = do
  rank <- arrayRank <$> checkArrIdent arrexp
  mapM_ (requireI [Basic Cert]) cs
  mapM_ (require [Basic Int] . newDim) newshape
  zipWithM_ (checkDimChange rank) newshape [0..]
  where checkDimChange _ (DimNew _) _ =
          return ()
        checkDimChange rank (DimCoercion se) i
          | i >= rank =
            bad $ TypeError noLoc $
            "Asked to coerce dimension " ++ show i ++ " to " ++ pretty se ++
            ", but array " ++ pretty arrexp ++ " has only " ++ pretty rank ++ " dimensions"
          | otherwise =
            return ()

checkPrimOp (Rearrange cs perm arr) = do
  mapM_ (requireI [Basic Cert]) cs
  arrt <- lookupType arr
  let rank = arrayRank arrt
  when (length perm /= rank || sort perm /= [0..rank-1]) $
    bad $ PermutationError noLoc perm rank $ Just arr

checkPrimOp (Stripe cs stride arr) = do
  mapM_ (requireI [Basic Cert]) cs
  require [Basic Int] stride
  void $ checkArrIdent arr

checkPrimOp (Unstripe cs stride arr) = do
  mapM_ (requireI [Basic Cert]) cs
  require [Basic Int] stride
  void $ checkArrIdent arr

checkPrimOp (Split cs sizeexps arrexp) = do
  mapM_ (requireI [Basic Cert]) cs
  mapM_ (require [Basic Int]) sizeexps
  void $ checkArrIdent arrexp

checkPrimOp (Concat cs arr1exp arr2exps ressize) = do
  mapM_ (requireI [Basic Cert]) cs
  arr1t  <- checkArrIdent arr1exp
  arr2ts <- mapM checkArrIdent arr2exps
  -- The arguments to concat need not have the same uniqueness, so set
  -- it all to nonunique before comparing.
  let arr1t' = setUniqueness arr1t Nonunique
      arr2ts' = map (`setUniqueness` Nonunique) arr2ts
      success = all (== stripArray 1 arr1t') $
                map (stripArray 1) arr2ts'
  unless success $
    bad $ TypeError noLoc $
    "Types of arguments to concat do not match.  Got " ++
    pretty arr1t ++ " and " ++ intercalate ", " (map pretty arr2ts)
  require [Basic Int] ressize

checkPrimOp (Copy e) =
  void $ checkArrIdent e

checkPrimOp (Assert e _) =
  require [Basic Bool] e

checkPrimOp (Alloc e _) =
  require [Basic Int] e

checkPrimOp (Partition cs _ flags arrs) = do
  mapM_ (requireI [Basic Cert]) cs
  flagst <- lookupType flags
  unless (rowType flagst == Basic Int) $
    bad $ TypeError noLoc $ "Flag array has type " ++ pretty flagst ++ "."
  forM_ arrs $ \arr -> do
    arrt <- lookupType arr
    unless (arrayRank arrt > 0) $
      bad $ TypeError noLoc $
      "Array argument " ++ pretty arr ++
      " to partition has type " ++ pretty arrt ++ "."

checkLoopOp :: Checkable lore =>
               LoopOp lore -> TypeM lore ()

checkLoopOp (DoLoop respat merge form loopbody) = do
  let (mergepat, mergeexps) = unzip merge
  mergeargs <- mapM checkArg mergeexps

  funparams <- case form of
    ForLoop loopvar boundexp -> do
      iparam <- basicFParamM loopvar Int
      let funparams = iparam : mergepat
          paramts   = map paramType funparams

      boundarg <- checkArg boundexp
      checkFuncall Nothing paramts $ boundarg : mergeargs
      return funparams
    WhileLoop cond -> do
      case find ((==cond) . paramName . fst) merge of
        Just (condparam,_) ->
          unless (paramType condparam == Basic Bool) $
          bad $ TypeError noLoc $
          "Conditional '" ++ pretty cond ++ "' of while-loop is not boolean, but " ++
          pretty (paramType condparam) ++ "."
        Nothing ->
          bad $ TypeError noLoc $
          "Conditional '" ++ pretty cond ++ "' of while-loop is not a merge varible."
      let funparams = mergepat
          paramts   = map paramType funparams
      checkFuncall Nothing paramts mergeargs
      return funparams

  let rettype = map paramType mergepat

  context "Inside the loop body" $ noConsume $
    checkFun' (nameFromString "<loop body>",
               staticShapes rettype,
               funParamsToIdentsAndLores funparams,
               loopbody) $ do
      checkFunParams funparams
      checkBody loopbody
      bodyt <- bodyExtType loopbody
      unless (map rankShaped bodyt `subtypesOf`
              map rankShaped (staticShapes rettype)) $
        bad $ ReturnTypeError noLoc (nameFromString "<loop body>")
        (Several $ staticShapes rettype)
        (Several bodyt)
  forM_ respat $ \res ->
    case find ((==res) . paramName) mergepat of
      Nothing -> bad $ TypeError noLoc $
                 "Loop result variable " ++
                 textual res ++
                 " is not a merge variable."
      Just _  -> return ()

checkLoopOp (Map ass size fun arrexps) = do
  mapM_ (requireI [Basic Cert]) ass
  require [Basic Int] size
  arrargs <- checkSOACArrayArgs size arrexps
  void $ checkLambda fun arrargs

checkLoopOp (ConcatMap cd size fun inarrs) = do
  mapM_ (requireI [Basic Cert]) cd
  require [Basic Int] size
  forM_ inarrs $ \inarr -> do
    args <- mapM (checkArg . Var) inarr
    void $ checkConcatMapLambda fun args

checkLoopOp (Reduce ass size fun inputs) = do
  let (startexps, arrexps) = unzip inputs
  mapM_ (requireI [Basic Cert]) ass
  require [Basic Int] size
  startargs <- mapM checkArg startexps
  arrargs   <- checkSOACArrayArgs size arrexps
  checkLambda fun $ startargs ++ arrargs
  let startt      = map argType startargs
      intupletype = map argType arrargs
      funret      = lambdaReturnType fun
  unless (startt `subtypesOf` funret) $
    bad $ TypeError noLoc $
    "Accumulator is of type " ++ prettyTuple startt ++
    ", but reduce function returns type " ++ prettyTuple funret ++ "."
  unless (intupletype `subtypesOf` funret) $
    bad $ TypeError noLoc $
    "Array element value is of type " ++ prettyTuple intupletype ++
    ", but reduce function returns type " ++ prettyTuple funret ++ "."

-- Scan is exactly identical to Reduce.  Duplicate for clarity anyway.
checkLoopOp (Scan ass size fun inputs) = do
  let (startexps, arrexps) = unzip inputs
  mapM_ (requireI [Basic Cert]) ass
  require [Basic Int] size
  startargs <- mapM checkArg startexps
  arrargs   <- checkSOACArrayArgs size arrexps
  checkLambda fun $ startargs ++ arrargs
  let startt      = map argType startargs
      intupletype = map argType arrargs
      funret      = lambdaReturnType fun
  unless (startt `subtypesOf` funret) $
    bad $ TypeError noLoc $
    "Initial value is of type " ++ prettyTuple startt ++
    ", but scan function returns type " ++ prettyTuple funret ++ "."
  unless (intupletype `subtypesOf` funret) $
    bad $ TypeError noLoc $
    "Array element value is of type " ++ prettyTuple intupletype ++
    ", but scan function returns type " ++ prettyTuple funret ++ "."

checkLoopOp (Redomap ass size outerfun innerfun accexps arrexps) = do
  mapM_ (requireI [Basic Cert]) ass
  require [Basic Int] size
  arrargs <- checkSOACArrayArgs size arrexps
  accargs <- mapM checkArg accexps
  checkLambda innerfun $ accargs ++ arrargs
  let innerRetType = lambdaReturnType innerfun
      innerAccType = take (length accexps) innerRetType
      asArg t = (t, mempty, mempty)
  checkLambda outerfun $ map asArg $ innerAccType ++ innerAccType
  let acct = map argType accargs
      outerRetType = lambdaReturnType outerfun
  unless (acct `subtypesOf` innerAccType ) $
    bad $ TypeError noLoc $ "Initial value is of type " ++ prettyTuple acct ++
          ", but redomap inner reduction returns type " ++ prettyTuple innerRetType ++ "."
  unless (acct `subtypesOf` outerRetType) $
    bad $ TypeError noLoc $ "Initial value is of type " ++ prettyTuple acct ++
          ", but redomap outer reduction returns type " ++ prettyTuple outerRetType ++ "."

checkLoopOp (Kernel cs w index ispace inps returns body) = do
  mapM_ (requireI [Basic Cert]) cs
  require [Basic Int] w
  mapM_ (require [Basic Int]) bounds
  index_param <- basicFParamM index Int
  iparams' <- forM iparams $ \iparam -> basicFParamM iparam Int
  forM_ returns $ \(t, perm) ->
    let return_rank = arrayRank t + rank
    in unless (sort perm == [0..return_rank - 1]) $
       bad $ TypeError noLoc $
       "Permutation " ++ pretty perm ++
       " not valid for returning " ++ pretty t ++
       " from a rank " ++ pretty rank ++ " kernel."
  checkFun' (nameFromString "<kernel body>",
             staticShapes rettype,
             funParamsToIdentsAndLores $ index_param : iparams' ++ map kernelInputParam inps,
             body) $ do
    checkFunParams $ map kernelInputParam inps
    mapM_ checkKernelInput inps
    checkBody body
    bodyt <- bodyExtType body
    unless (map rankShaped bodyt `subtypesOf`
            map rankShaped (staticShapes rettype)) $
      bad $
      ReturnTypeError noLoc (nameFromString "<kernel body>")
      (Several $ staticShapes rettype)
      (Several bodyt)
  where (iparams, bounds) = unzip ispace
        rank = length ispace
        (rettype, _) = unzip returns
        checkKernelInput inp = do
          checkExp $ PrimOp $ Index []
            (kernelInputArray inp) (kernelInputIndices inp)

          arr_t <- lookupType $ kernelInputArray inp
          unless (stripArray (length $ kernelInputIndices inp) arr_t `subtypeOf`
                  kernelInputType inp) $
            bad $ TypeError noLoc $
            "Kernel input " ++ pretty inp ++ " has inconsistent type."

          let uses_all_iparams =
                all (`elem` kernelInputIndices inp) $ map Var iparams
          when (unique (kernelInputType inp) && not uses_all_iparams) $
             bad $ TypeError noLoc $ "Unique kernel input " ++
             pretty (kernelInputName inp) ++
             " does not use entire index space."

checkLoopOp (ReduceKernel cs w
             (KernelSize num_groups workgroup_size
              per_thread_elements num_elements offset_multiple)
             parfun seqfun accexps arrexps) = do
  mapM_ (requireI [Basic Cert]) cs
  require [Basic Int] w
  require [Basic Int] num_groups
  require [Basic Int] workgroup_size
  require [Basic Int] per_thread_elements
  require [Basic Int] num_elements
  require [Basic Int] offset_multiple
  arrargs <- checkSOACArrayArgs w arrexps
  accargs <- mapM checkArg accexps

  case lambdaParams seqfun of
    [] -> bad $ TypeError noLoc "Fold function takes no parameters."
    chunk_param : _
      | Basic Int <- paramType chunk_param -> do
          let seq_args = (Basic Int, mempty, mempty) :
                         [ (t `arrayOfRow` Var (paramName chunk_param), y, z)
                         | (t, y, z) <- arrargs ]
          checkLambda seqfun seq_args
      | otherwise ->
          bad $ TypeError noLoc "First parameter of fold function is not integer-typed."

  let seqRetType = lambdaReturnType seqfun
      asArg t = (t, mempty, mempty)
  checkLambda parfun $ map asArg $ Basic Int : seqRetType ++ seqRetType
  let acct = map argType accargs
      parRetType = lambdaReturnType parfun
  unless (acct `subtypesOf` seqRetType) $
    bad $ TypeError noLoc $ "Initial value is of type " ++ prettyTuple acct ++
          ", but redomap fold function returns type " ++ prettyTuple seqRetType ++ "."
  unless (acct `subtypesOf` parRetType) $
    bad $ TypeError noLoc $ "Initial value is of type " ++ prettyTuple acct ++
          ", but redomap reduction function returns type " ++ prettyTuple parRetType ++ "."

checkLoopOp (Stream ass size form lam arrexps _) = do
  let accexps = getStreamAccums form
  mapM_ (requireI [Basic Cert]) ass
  require [Basic Int] size
  accargs <- mapM checkArg accexps
  arrargs <- mapM lookupType arrexps
  _ <- checkSOACArrayArgs size arrexps
  let chunk = head $ extLambdaParams lam
  let asArg t = (t, mempty, mempty)
      inttp   = Basic Int
      lamarrs'= [ arrayOf t (Shape [Var $ paramName chunk]) (uniqueness t)
                   | t <- map (\(Array bt s u)->Array bt (stripDims 1 s) u)
                              arrargs ]
  checkExtLambda lam $ asArg inttp :
                       accargs ++ map asArg lamarrs'
  let acc_len= length accexps
  let lamrtp = take acc_len $ extLambdaReturnType lam
  unless (all (uncurry (==)) $ zip lamrtp (staticShapes $ map (\(y,_,_)->y) accargs)) $
    bad $ TypeError noLoc "Stream with inconsistent accumulator type in lambda."
  -- check reduce's lambda, if any
  _ <- case form of
        RedLike _ lam0 _ -> do
            let acct = map argType accargs
                outerRetType = lambdaReturnType lam0
            checkLambda lam0 (accargs ++ accargs)
            unless (acct `subtypesOf` outerRetType) $
                bad $ TypeError noLoc $ "Initial value is of type " ++ prettyTuple acct ++
                      ", but stream's reduce lambda returns type " ++ prettyTuple outerRetType ++ "."
        _ -> return ()
  -- just get the dflow of lambda on the fakearg, which does not alias
  -- arr, so we can later check that aliases of arr are not used inside lam.
  -- let fakearg = (fromDecl $ addNames $ removeNames $ typeOf arr', mempty, srclocOf pos)
  let fake_lamarrs' = map asArg lamarrs'
  (_,dflow) <- collectDataflow $
                checkExtLambda lam $ asArg inttp :
                                     accargs ++ fake_lamarrs'
  arr_aliases <- mapM lookupAliases arrexps
  let aliased_syms = HS.toList $ HS.fromList $ concatMap HS.toList arr_aliases
  let usages = usageMap $ usageOccurences dflow
  when (any (`HM.member` usages) aliased_syms) $
     bad $ TypeError noLoc "Stream with input array used inside lambda."
  -- check outerdim of Lambda's streamed-in array params are NOT specified,
  -- and that return type inner dimens are all specified but not as other
  -- lambda parameters!
  let lamarr_rtp = drop acc_len $ extLambdaReturnType lam
      lamarr_ptp = map paramType $ drop (acc_len+1) $ extLambdaParams lam
      names_lamparams = HS.fromList $ map paramName $ extLambdaParams lam
  _ <- mapM (checkOuterDim (paramName chunk) . head .    shapeDims . arrayShape) lamarr_ptp
  _ <- mapM (checkInnerDim names_lamparams   . tail . extShapeDims . arrayShape) lamarr_rtp
  return ()
    where checkOuterDim chunknm outdim = do
            let chunk_str = textual chunknm
            case outdim of
                    Constant _ ->
                      bad $ TypeError noLoc ("Stream: outer dimension of stream should NOT"++
                                             " be specified since it is "++chunk_str++"by default.")
                    Var idd    ->
                      if idd == chunknm then return True
                      else bad $ TypeError noLoc ("Stream: outer dimension of stream should NOT"++
                                                  " be specified since it is "++chunk_str++"by default.")
          boundDim (Free (Var idd)) = return $ Just idd
          boundDim (Free _        ) = return Nothing
          boundDim (Ext  _        ) =
            bad $ TypeError noLoc $ "Stream's lambda: inner dimensions of the"++
                                    " streamed-out arrays MUST be specified!"
          checkInnerDim lamparnms innerdims = do
            rtp_iner_syms <- catMaybes <$> mapM boundDim innerdims
            case find (`HS.member` lamparnms) rtp_iner_syms of
                Just name -> bad $ TypeError noLoc $
                                   "Stream's lambda: " ++ textual (baseName name) ++
                                   " cannot specify an inner result shape"
                _ -> return True

checkSegOp :: Checkable lore =>
              SegOp lore -> TypeM lore ()

checkSegOp (SegReduce ass size fun inputs descp_exp) = do
  descp_arg <- checkArg $ Var descp_exp
  require [Basic Int] size
  let descp_tp = argType descp_arg
  unless (elemType descp_tp == Int) $
    bad $ TypeError noLoc $
    "Array descriptor is of type " ++ pretty descp_tp ++
    ", but should be [Int]"
  checkLoopOp $ Reduce ass size fun inputs

-- SegScan is mostly identical to SegReduced. Duplicated for clarity.
checkSegOp (SegScan ass size _ fun inputs descp_exp) = do
  descp_arg <- checkArg $ Var descp_exp
  require [Basic Int] size
  let descp_tp = argType descp_arg
  unless (elemType descp_tp == Int) $
    bad $ TypeError noLoc $
    "Array descriptor is of type " ++ pretty descp_tp ++
    ", but should be [Int]"
  checkLoopOp $ Scan ass size fun inputs

checkSegOp (SegReplicate ass counts_vn data_vn mb_seg_vn) = do
  seg_tp <- case mb_seg_vn of
         Just vn -> liftM argType $ checkArg $ Var vn
         Nothing -> do data_tp <- liftM argType $ checkArg $ Var data_vn
                       return $ arrayOf (Basic Int) (arrayShape data_tp) Nonunique
  mapM_ (requireI [Basic Cert]) ass
  counts_arg <- checkArg $ Var counts_vn
  let counts_tp = argType counts_arg
  -- TODO: Not sure Troels is happy about this
  unless (arrayDims counts_tp == arrayDims seg_tp) $
    bad $ TypeError noLoc $
    "Arrays should have same shapes " ++ pretty counts_tp ++ " , " ++
    pretty seg_tp
  unless (elemType counts_tp == Int && not (null (arrayDims counts_tp))) $
    bad $ TypeError noLoc $
    "Array is of type " ++ pretty counts_tp ++
    ", but should be [Int] (segreplicate)"
  unless (elemType seg_tp == Int && not (null (arrayDims seg_tp))) $
    bad $ TypeError noLoc $
    "Array is of type " ++ pretty seg_tp ++
    ", but should be [Int] (segreplicate)"


checkExp :: Checkable lore =>
            Exp lore -> TypeM lore ()

checkExp (PrimOp op) = checkPrimOp op

checkExp (LoopOp op) = checkLoopOp op

checkExp (SegOp op) = checkSegOp op

checkExp (If e1 e2 e3 ts) = do
  require [Basic Bool] e1
  (_, dflow) <-
    collectDataflow $ checkBody e2 `alternative` checkBody e3
  tell dflow
  ts2 <- bodyExtType e2
  ts3 <- bodyExtType e3
  unless (ts2 `generaliseExtTypes` ts3 `subtypesOf` ts) $
    bad $ TypeError noLoc $
    unlines ["If-expression branches have types",
             "  " ++ prettyTuple ts2 ++ ", and",
             "  " ++ prettyTuple ts3,
             "Which is not a subtype of annotation",
             "  " ++ prettyTuple ts]

checkExp (Apply fname args t)
  | "trace" <- nameToString fname = do
  argts <- mapM (checkSubExp . fst) args
  when (staticShapes argts /= retTypeValues t) $
    bad $ TypeError noLoc $ "Expected apply result type " ++ pretty t
    ++ " but got " ++ pretty argts

checkExp (Apply fname args rettype_annot) = do
  (rettype_derived, paramtypes) <- lookupFun fname $ map fst args
  argflows <- mapM (checkArg . fst) args
  when (rettype_derived /= rettype_annot) $
    bad $ TypeError noLoc $ "Expected apply result type " ++ pretty rettype_derived
    ++ " but annotation is " ++ pretty rettype_annot
  checkFuncall (Just fname) paramtypes argflows

checkSOACArrayArgs :: Checkable lore =>
                      SubExp -> [VName] -> TypeM lore [Arg]
checkSOACArrayArgs width vs =
  forM vs $ \v -> do
    (vt, v') <- checkSOACArrayArg v
    let argSize = arraySize 0 vt
    unless (argSize == width) $
      bad $ TypeError noLoc $
      "SOAC argument " ++ pretty v ++ " has outer size " ++
      pretty argSize ++ ", but width of SOAC is " ++
      pretty width
    return v'
  where checkSOACArrayArg ident = do
          (t, als, dflow) <- checkArg $ Var ident
          case peelArray 1 t of
            Nothing -> bad $ TypeError noLoc $
                       "SOAC argument " ++ pretty ident ++ " is not an array"
            Just rt -> return (t, (rt, als, dflow))

checkType :: Checkable lore =>
             Type -> TypeM lore ()
checkType = mapM_ checkSubExp . arrayDims

checkExtType :: Checkable lore =>
                TypeBase ExtShape
             -> TypeM lore ()
checkExtType t = mapM_ checkExtDim $ extShapeDims $ arrayShape t
  where checkExtDim (Free se) = void $ checkSubExp se
        checkExtDim (Ext _)   = return ()

checkBinOp :: Checkable lore =>
              BinOp -> SubExp -> SubExp -> BasicType
           -> TypeM lore ()
checkBinOp Plus e1 e2 t = checkPolyBinOp Plus [Float32, Float64, Int] e1 e2 t
checkBinOp Minus e1 e2 t = checkPolyBinOp Minus [Float32, Float64, Int] e1 e2 t
checkBinOp Pow e1 e2 t = checkPolyBinOp Pow [Float32, Float64, Int] e1 e2 t
checkBinOp Times e1 e2 t = checkPolyBinOp Times [Float32, Float64, Int] e1 e2 t
checkBinOp FloatDiv e1 e2 t = checkPolyBinOp FloatDiv [Float32, Float64] e1 e2 t
checkBinOp Div e1 e2 t = checkPolyBinOp Div [Int] e1 e2 t
checkBinOp Mod e1 e2 t = checkPolyBinOp Mod [Int] e1 e2 t
checkBinOp Quot e1 e2 t = checkPolyBinOp Quot [Int] e1 e2 t
checkBinOp Rem e1 e2 t = checkPolyBinOp Rem [Int] e1 e2 t
checkBinOp ShiftR e1 e2 t = checkPolyBinOp ShiftR [Int] e1 e2 t
checkBinOp ShiftL e1 e2 t = checkPolyBinOp ShiftL [Int] e1 e2 t
checkBinOp Band e1 e2 t = checkPolyBinOp Band [Int] e1 e2 t
checkBinOp Xor e1 e2 t = checkPolyBinOp Xor [Int] e1 e2 t
checkBinOp Bor e1 e2 t = checkPolyBinOp Bor [Int] e1 e2 t
checkBinOp LogAnd e1 e2 t = checkPolyBinOp LogAnd [Bool] e1 e2 t
checkBinOp LogOr e1 e2 t = checkPolyBinOp LogOr [Bool] e1 e2 t
checkBinOp Equal e1 e2 t = checkRelOp Equal [Int, Float32, Float64] e1 e2 t
checkBinOp Less e1 e2 t = checkRelOp Less [Int, Float32, Float64] e1 e2 t
checkBinOp Leq e1 e2 t = checkRelOp Leq [Int, Float32, Float64] e1 e2 t

checkRelOp :: Checkable lore =>
              BinOp -> [BasicType]
           -> SubExp -> SubExp
           -> BasicType
           -> TypeM lore ()
checkRelOp op tl e1 e2 t = do
  require (map Basic tl) e1
  require (map Basic tl) e2
  _ <- unifySubExpTypes e1 e2
  checkAnnotation (pretty op ++ " result") (Basic t) $ Basic Bool

checkPolyBinOp :: Checkable lore =>
                  BinOp -> [BasicType]
               -> SubExp -> SubExp -> BasicType
               -> TypeM lore ()
checkPolyBinOp op tl e1 e2 t = do
  require (map Basic tl) e1
  require (map Basic tl) e2
  t' <- unifySubExpTypes e1 e2
  checkAnnotation (pretty op ++ " result") (Basic t) t'

sequentially :: Checkable lore =>
                TypeM lore a -> (a -> Dataflow -> TypeM lore b) -> TypeM lore b
sequentially m1 m2 = do
  (a, m1flow) <- collectDataflow m1
  (b, m2flow) <- collectDataflow $ m2 a m1flow
  occur $ usageOccurences m1flow `seqOccurences`
          usageOccurences m2flow
  return b

checkPatElem :: Checkable lore =>
                PatElem lore -> TypeM lore ()
checkPatElem (PatElem ident bindage attr) = do
  checkBndSizes ident
  checkBindage bindage
  checkLetBoundLore ident attr

checkBindage :: Checkable lore =>
                Bindage -> TypeM lore ()
checkBindage BindVar = return ()
checkBindage (BindInPlace cs src is) = do
  mapM_ (requireI [Basic Cert]) cs
  srct <- lookupType src
  mapM_ (require [Basic Int]) is

  unless (unique srct || basicType srct) $
    bad $ TypeError noLoc $ "Source '" ++ textual src ++ "' is not unique"

  consume =<< lookupAliases src

  -- Check that the new value has the same type as what is already
  -- there (It does not have to be unique, though.)
  case peelArray (length is) srct of
    Nothing -> bad $ IndexingError src
                     (arrayRank srct) (length is) noLoc
    Just _  -> return ()

checkBinding :: Checkable lore =>
                Pattern lore -> Exp lore -> Dataflow
             -> TypeM lore (TypeM lore a -> TypeM lore a)
checkBinding pat e dflow =
  context ("When matching\n" ++ message "  " pat ++ "\nwith\n" ++ message "  " e) $ do
    matchPattern (removePatternAliases pat) (removeExpAliases e)
    return $ \m -> sequentially (tell dflow)
                   (const . const $
                    binding (zip (identsAndLore pat)
                             (map (unNames . fst . patElemLore) $
                              patternElements pat))
                    (do mapM_ checkPatElem (patternElements $ removePatternAliases pat)
                        m))
  where identsAndLore = map identAndLore . patternElements . removePatternAliases
        identAndLore bindee = (patElemIdent bindee, LetBound $ patElemLore bindee)

matchExtPattern :: [PatElem lore] -> [ExtType] -> TypeM lore ()
matchExtPattern pat ts = do
  (ts', restpat, _) <- liftEitherS $ patternContext pat ts
  unless (length restpat == length ts') $
    bad $ InvalidPatternError (Several pat) (Several ts) Nothing noLoc
  evalStateT (zipWithM_ checkBinding' restpat ts') []
  where checkBinding' patElem@(PatElem (Ident name namet) _ _) t = do
          lift $ checkAnnotation ("binding of variable " ++ textual name)
            (patElemRequires patElem) t
          add $ Ident name namet

        add ident = do
          bnd <- gets $ find (==ident)
          case bnd of
            Nothing -> modify (ident:)
            Just (Ident name _) ->
              lift $ bad $ DupPatternError name noLoc noLoc

matchExtReturnType :: Name -> [ExtType] -> Result
                   -> TypeM lore ()
matchExtReturnType fname rettype ses = do
  ts <- staticShapes <$> mapM subExpType ses
  unless (ts `subtypesOf` rettype) $
    bad $ ReturnTypeError noLoc fname
          (Several rettype)
          (Several ts)

patternContext :: [PatElemT attr] -> [ExtType] ->
                  Either String ([Type], [PatElemT attr], [PatElemT attr])
patternContext pat rt = do
  (rt', (restpat,_), shapepat) <- runRWST (mapM extract rt) () (pat, HM.empty)
  return (rt', restpat, shapepat)
  where extract t = setArrayShape t <$> Shape <$>
                    mapM extract' (extShapeDims $ arrayShape t)
        extract' (Free se) = return se
        extract' (Ext x)   = correspondingVar x
        correspondingVar x = do
          (remnames, m) <- get
          case (remnames, HM.lookup x m) of
            (_, Just v) -> return $ Var $ patElemName v
            (v:vs, Nothing)
              | Basic Int <- patElemType v -> do
                tell [v]
                put (vs, HM.insert x v m)
                return $ Var $ patElemName v
            (_, Nothing) ->
              lift $ Left "Pattern cannot match context"

checkBndSizes :: Checkable lore =>
                 Ident -> TypeM lore ()
checkBndSizes (Ident _ t) = do
  let dims = arrayDims t
  mapM_ (require [Basic Int]) dims

validApply :: ArrayShape shape =>
              [TypeBase shape]
           -> [TypeBase shape]
           -> Bool
validApply expected got =
  length got == length expected &&
  and (zipWith subtypeOf (map rankShaped got) (map rankShaped expected))

type Arg = (Type, Names, Dataflow)

argType :: Arg -> Type
argType (t, _, _) = t

checkArg :: Checkable lore =>
            SubExp -> TypeM lore Arg
checkArg arg = do (argt, dflow) <- collectDataflow $ checkSubExp arg
                  als <- subExpAliasesM arg
                  return (argt, als, dflow)

checkFuncall :: Checkable lore =>
                Maybe Name
             -> [Type] -> [Arg]
             -> TypeM lore ()
checkFuncall fname params args = do
  let argts = map argType args
      paramts = params
  unless (validApply paramts argts) $
    bad $ ParameterMismatch fname noLoc
          (Right $ map (justOne . staticShapes1) params) $
          map (justOne . staticShapes1 . argType) args
  forM_ (zip (map diet paramts) args) $ \(d, (_, als, dflow)) -> do
    maybeCheckOccurences $ usageOccurences dflow
    let occurs = [consumption (consumeArg als d)]
    occur $ usageOccurences dflow `seqOccurences` occurs
  where consumeArg als Consume = als
        consumeArg _   Observe = mempty

checkLambda :: Checkable lore =>
               Lambda lore -> [Arg] -> TypeM lore ()
checkLambda (Lambda i params body ret) args = do
  mapM_ checkType ret
  iparam <- basicLParamM i Int
  if length params == length args then do
    checkFuncall Nothing (map paramType params) args
    noConsume $ checkAnonymousFun
      (nameFromString "<anonymous>", ret, iparam:params, body)
  else bad $ TypeError noLoc $ "Anonymous function defined with " ++ show (length params) ++ " parameters, but expected to take " ++ show (length args) ++ " arguments."

checkConcatMapLambda :: Checkable lore =>
                        Lambda lore -> [Arg] -> TypeM lore ()
checkConcatMapLambda (Lambda i params body rettype) args = do
  mapM_ checkType rettype
  iparam <- basicLParamM i Int
  let (_,elemparams) =
        splitAt (length params - length args) params
      fname = nameFromString "<anonymous>"
      rettype' = [ arrayOf t (ExtShape [Ext 0]) $ uniqueness t
                 | t <- staticShapes rettype ]
  if length elemparams == length args then do
    checkFuncall Nothing (map paramType elemparams) args
    noConsume $ checkFun' (fname,
                          rettype',
                          [ (paramIdent param, LambdaBound $ paramLore param)
                          | param <- iparam:params ],
                          body) $
      checkBindings (bodyBindings body) $ do
        checkResult $ bodyResult body
        matchExtReturnType fname rettype' $ bodyResult body
  else bad $ TypeError noLoc $ "concatMap function defined with " ++ show (length params) ++ " parameters, but expected to take " ++ show (length args) ++ " array arguments."

checkExtLambda :: Checkable lore =>
                  ExtLambda lore -> [Arg] -> TypeM lore ()
checkExtLambda (ExtLambda i params body rettype) args =
  if length params == length args then do
    iparam <- basicLParamM i Int
    checkFuncall Nothing (map paramType params) args
    let fname = nameFromString "<anonymous>"
    noConsume $ checkFun' (fname,
                          rettype,
                          [ (paramIdent param, LambdaBound $ paramLore param)
                          | param <- iparam:params ],
                          body) $
      checkBindings (bodyBindings body) $ do
        checkResult $ bodyResult body
        matchExtReturnType fname rettype $ bodyResult body
    else bad $ TypeError noLoc $
         "Existential lambda defined with " ++ show (length params) ++
         " parameters, but expected to take " ++ show (length args) ++ " arguments."

-- | The class of lores that can be type-checked.
class (FreeIn (Annotations.Exp lore),
       FreeIn (Annotations.LetBound lore),
       FreeIn (Annotations.Body lore),
       Lore lore, PrettyLore lore) => Checkable lore where
  checkExpLore :: Annotations.Exp lore -> TypeM lore ()
  checkBodyLore :: Annotations.Body lore -> TypeM lore ()
  checkFParamLore :: Ident -> Annotations.FParam lore -> TypeM lore ()
  checkLetBoundLore :: Ident -> Annotations.LetBound lore -> TypeM lore ()
  checkRetType :: AST.RetType lore -> TypeM lore ()
  matchPattern :: AST.Pattern lore -> AST.Exp lore ->
                  TypeM lore ()
  basicFParam :: lore -> VName -> BasicType -> AST.FParam lore
  basicLParam :: lore -> VName -> BasicType -> AST.LParam lore
  matchReturnType :: Name -> RetType lore -> AST.Result -> TypeM lore ()

basicFParamM :: forall lore.Checkable lore =>
                VName -> BasicType -> TypeM lore (AST.FParam lore)
basicFParamM name t =
  return $ basicFParam (representative :: lore) name t

basicLParamM :: forall lore.Checkable lore =>
                VName -> BasicType -> TypeM lore (AST.LParam lore)
basicLParamM name t =
  return $ basicLParam (representative :: lore) name t
