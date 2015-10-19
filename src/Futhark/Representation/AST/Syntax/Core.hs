{-# LANGUAGE FlexibleContexts #-}
-- | The most primitive ("core") aspects of the AST.  Split out of
-- "Futhark.Representation.AST.Syntax" in order for
-- "Futhark.Representation.AST.Lore" to use these definitions.  This
-- module is re-exported from "Futhark.Representation.AST.Syntax" and
-- there should be no reason to include it explicitly.
module Futhark.Representation.AST.Syntax.Core
       (
         module Language.Futhark.Core

         -- * Types
         , Uniqueness(..)
         , Shape(..)
         , ExtDimSize(..)
         , ExtShape(..)
         , Rank(..)
         , ArrayShape(..)
         , Space (..)
         , SpaceId
         , TypeBase(..)
         , Type
         , ExtType
         , Diet(..)

         -- * Values
         , BasicValue(..)
         , Value(..)

         -- * Abstract syntax tree
         , Ident (..)
         , Certificates
         , SubExp(..)
         , ParamT (..)
         , Param
         , Bindage (..)
         , PatElemT (..)

         -- * Miscellaneous
         , Names
         ) where

import Control.Applicative
import Control.Monad.State
import Data.Array
import Data.Hashable
import Data.Monoid
import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM

import Prelude

import Language.Futhark.Core

-- | The size of an array type as a list of its dimension sizes.  If a
-- variable, that variable must be in scope where this array is used.
newtype Shape = Shape { shapeDims :: [SubExp] }
              deriving (Eq, Ord, Show)

-- | The size of this dimension.
data ExtDimSize = Free SubExp -- ^ Some known dimension.
                | Ext Int -- ^ Existentially quantified.
                  deriving (Eq, Ord, Show)

-- | Like 'Shape' but some of its elements may be bound in a local
-- environment instead.  These are denoted with integral indices.
newtype ExtShape = ExtShape { extShapeDims :: [ExtDimSize] }
                 deriving (Eq, Ord, Show)

-- | The size of an array type as merely the number of dimensions,
-- with no further information.
data Rank = Rank Int
            deriving (Show, Eq, Ord)

-- | A class encompassing types containing array shape information.
class (Monoid a, Eq a, Ord a) => ArrayShape a where
  -- | Return the rank of an array with the given size.
  shapeRank :: a -> Int
  -- | @stripDims n shape@ strips the outer @n@ dimensions from
  -- @shape@.
  stripDims :: Int -> a -> a
  -- | Check whether one shape if a subset of another shape.
  subShapeOf :: a -> a -> Bool

instance Monoid Shape where
  mempty = Shape mempty
  Shape l1 `mappend` Shape l2 = Shape $ l1 `mappend` l2

instance ArrayShape Shape where
  shapeRank (Shape l) = length l
  stripDims n (Shape dims) = Shape $ drop n dims
  subShapeOf = (==)

instance Monoid ExtShape where
  mempty = ExtShape mempty
  ExtShape l1 `mappend` ExtShape l2 = ExtShape $ l1 `mappend` l2

instance ArrayShape ExtShape where
  shapeRank (ExtShape l) = length l
  stripDims n (ExtShape dims) = ExtShape $ drop n dims
  subShapeOf (ExtShape ds1) (ExtShape ds2) =
    -- Must agree on Free dimensions, and ds1 may not be existential
    -- where ds2 is Free.  Existentials must also be congruent.
    length ds1 == length ds2 &&
    evalState (and <$> zipWithM subDimOf ds1 ds2) HM.empty
    where subDimOf (Free se1) (Free se2) = return $ se1 == se2
          subDimOf (Ext _)    (Free _)   = return False
          subDimOf (Free _)   (Ext _)    = return True
          subDimOf (Ext x)    (Ext y)    = do
            extmap <- get
            case HM.lookup y extmap of
              Just ywas | ywas == x -> return True
                        | otherwise -> return False
              Nothing -> do put $ HM.insert y x extmap
                            return True

instance Monoid Rank where
  mempty = Rank 0
  Rank x `mappend` Rank y = Rank $ x + y

instance ArrayShape Rank where
  shapeRank (Rank x) = x
  stripDims n (Rank x) = Rank $ x - n
  subShapeOf = (==)

-- | The memory space of a block.  If 'DefaultSpace', this is the "default"
-- space, whatever that is.  The exact meaning of the 'SpaceID'
-- depends on the backend used.  In GPU kernels, for example, this is
-- used to distinguish between constant, global and shared memory
-- spaces.  In GPU-enabled host code, it is used to distinguish
-- between host memory ('DefaultSpace') and GPU space.
data Space = DefaultSpace
           | Space SpaceId
             deriving (Show, Eq, Ord)

-- | A string representing a specific non-default memory space.
type SpaceId = String

-- | An Futhark type is either an array or an element type.  When
-- comparing types for equality with '==', shapes must match.
data TypeBase shape = Basic BasicType
                    | Array BasicType shape Uniqueness
                    | Mem SubExp Space
                    deriving (Show, Eq, Ord)

-- | A type with shape information, used for describing the type of
-- a computation.
type Type = TypeBase Shape

-- | A type with existentially quantified shapes - used as part of
-- function (and function-like) return types.  Generally only makes
-- sense when used in a list.
type ExtType = TypeBase ExtShape

-- | Information about which parts of a value/type are consumed.  For
-- example, we might say that a function taking three arguments of
-- types @([int], *[int], [int])@ has diet @[Observe, Consume,
-- Observe]@.
data Diet = Consume -- ^ Consumes this value.
          | Observe -- ^ Only observes value in this position, does
                    -- not consume.
            deriving (Eq, Ord, Show)

-- | Every possible value in Futhark.  Values are fully evaluated and their
-- type is always unambiguous.
data Value = BasicVal BasicValue
           | ArrayVal !(Array Int BasicValue) BasicType [Int]
             -- ^ It is assumed that the array is 0-indexed.
             deriving (Eq, Ord, Show)

-- | An identifier consists of its name and the type of the value
-- bound to the identifier.
data Ident = Ident { identName :: VName
                   , identType :: Type
                   }
               deriving (Show)

instance Eq Ident where
  x == y = identName x == identName y

instance Ord Ident where
  x `compare` y = identName x `compare` identName y

instance Hashable Ident where
  hashWithSalt salt = hashWithSalt salt . identName

-- | A list of names used for certificates in some expressions.
type Certificates = [VName]

-- | A subexpression is either a scalar constant or a variable.  One
-- important property is that evaluation of a subexpression is
-- guaranteed to complete in constant time.
data SubExp = Constant BasicValue
            | Var      VName
            deriving (Show, Eq, Ord)

-- | A function parameter.
data ParamT attr = Param
                   { paramIdent :: Ident
                     -- ^ Name and type of the function parameter.
                   , paramLore :: attr
                     -- ^ Function parameter attribute.
                   }
                   deriving (Ord, Show, Eq)

-- | A type alias for namespace control.
type Param = ParamT

-- | How a name in a let-binding is bound - either as a plain
-- variable, or in the form of an in-place update.
data Bindage = BindVar -- ^ Bind as normal.
             | BindInPlace Certificates VName [SubExp]
               -- ^ Perform an in-place update, in which the value
               -- being bound is inserted at the given index in the
               -- array referenced by the 'VName'.  Note that the
               -- result of the binding is the entire array, not just
               -- the value that has been inserted..  The
               -- 'Certificates' contain bounds checking certificates
               -- (if necessary).
                  deriving (Ord, Show, Eq)

-- | An element of a pattern - consisting of an 'Ident' (essentially a
-- pair of the name andtype), a 'Bindage', and an addditional
-- parametric attribute.
data PatElemT attr = PatElem { patElemIdent :: Ident
                               -- ^ The ident bound by a 'PatElem'.
                             , patElemBindage :: Bindage
                             , patElemLore :: attr
                               -- ^ Pattern element attribute.
                             }
                   deriving (Ord, Show, Eq)

-- | A set of names.
type Names = HS.HashSet VName
