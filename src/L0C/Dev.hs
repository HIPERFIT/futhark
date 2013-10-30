-- | This module contains a bunch of quick and dirty definitions for
-- making interactive development of @l0c@ easier.  Don't ever use
-- anything exported from this module in actual production code.
-- There is little (if any) error checking, IO exceptions abound and
-- everything might be idiosyncratic and brittle.  Feel free to add
-- your own nasty hacks.

module L0C.Dev
  ( name
  , ident
  , tident
  , expr
  , typ
  , lambda
  )
where

import Data.IORef
import Data.Loc
import qualified Data.Map as M
import qualified Data.Set as S
import System.IO.Unsafe

import Language.L0.Parser

import L0C.FreshNames
import L0C.L0
import L0C.Renamer
import L0C.TypeChecker

-- | Return a tagged name based on a string.
name :: String -> VName
name k = unsafePerformIO $
           atomicModifyIORef' uniqueNameSource $ \src ->
            let (k', src') = newID src $ nameFromString k
            in (src', k')

-- | Return a new, unique identifier.  Uses 'name'.
ident :: String -> Type -> Ident
ident k t = Ident (name k) t noLoc

-- | Return a new, unique identifier, based on a type declaration of
-- the form @"t name"@, for example @"[int] x"@.  Uses 'name'.
tident :: String -> Ident
tident s = case words s of
             [t,k] -> ident k $ typ t
             _ -> error "Bad ident"

uniqueNameSource :: IORef (NameSource VName)
uniqueNameSource = unsafePerformIO $ newIORef newUniqueNameSource
  where newUniqueNameSource = NameSource $ generator 0 M.empty
        generator i m s =
          case M.lookup (baseName s) m of
            Just s' -> (s', NameSource $ generator i m)
            Nothing ->
              let s' = s `setID` i
                  m' = M.insert (baseName s) s' m
              in (s', NameSource $ generator (i+1) m')

uniqueTag :: (NameSource VName -> f -> (t, NameSource VName)) -> f -> t
uniqueTag f x =
  x `seq` unsafePerformIO $ atomicModifyIORef' uniqueNameSource $ \src ->
    let (x', src') = f src x
    in (src', x')

uniqueTagExp :: TypeBox ty => ExpBase ty Name -> ExpBase ty VName
uniqueTagExp = uniqueTag tagExp'

uniqueTagType :: TypeBox ty => ty Name -> ty VName
uniqueTagType = uniqueTag tagType'

uniqueTagLambda :: TypeBox ty => LambdaBase ty Name -> LambdaBase ty VName
uniqueTagLambda = uniqueTag tagLambda'

rightResult :: Show a => Either a b -> b
rightResult = either (error . show) id

-- | Parse a string to an expression.
expr :: String -> Exp
expr = uniqueTagExp . rightResult . checkClosedExp . rightResult . parseExp "input"

-- | Parse a string to a type.
typ :: String -> Type
typ = uniqueTagType . (`setAliases` S.empty) . rightResult . parseType "input"

-- | Parse a string to an anonymous function.  Does not handle curried functions.
lambda :: String -> Lambda
lambda = uniqueTagLambda . rightResult . checkClosedLambda . rightResult . parseLambda "input"
  where checkClosedLambda (AnonymFun params body rettype loc) = do
          body' <- checkOpenExp env body
          return $ AnonymFun params body' rettype loc
            where env = M.fromList [ (identName param, fromDecl $ identType param)
                                     | param <- params ]
        checkClosedLambda (CurryFun {}) = error "Curries not handled"

tupleLambda :: String -> TupleLambda
tupleLambda = uniqueTagLambda . rightResult . checkClosedTupleLambda . rightResult . parseTupleLambda "input"
  where checkClosedTupleLambda (TupleLambda params body rettype loc) = do
          body' <- checkOpenExp env body
          return $ TupleLambda params body' rettype loc
            where env = M.fromList [ (identName param, fromDecl $ identType param)
                                     | param <- params ]
