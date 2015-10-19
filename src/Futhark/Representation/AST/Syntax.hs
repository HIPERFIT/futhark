{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances, StandaloneDeriving #-}
-- | This Is an ever-changing abstract syntax for Futhark.  Some types,
-- such as @Exp@, are parametrised by type and name representation.
-- See the @doc/@ subdirectory in the Futhark repository for a language
-- reference, or this module may be a little hard to understand.
module Futhark.Representation.AST.Syntax
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
  , Bindage (..)
  , PatElemT (..)
  , PatElem
  , PatternT (..)
  , Pattern
  , Binding(..)
  , Result
  , BodyT(..)
  , Body
  , PrimOp (..)
  , LoopOp (..)
  , SegOp (..)
  , ScanType(..)
  , BinOp (..)
  , DimChange (..)
  , ShapeChange
  , ExpT(..)
  , Exp
  , LoopForm (..)
  , LambdaT(..)
  , Lambda
  , ExtLambdaT (..)
  , ExtLambda
  , Annotations.RetType
  , StreamForm(..)
  , KernelInput (..)
  , KernelSize (..)

  -- * Definitions
  , ParamT (..)
  , Param
  , FParam
  , LParam
  , FunDecT (..)
  , FunDec
  , ProgT(..)
  , Prog

  -- * Miscellaneous
  , Names
  )
  where

import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Data.Loc

import Prelude

import Language.Futhark.Core
import Futhark.Representation.AST.Annotations (Annotations)
import qualified Futhark.Representation.AST.Annotations as Annotations
import Futhark.Representation.AST.Syntax.Core

type PatElem lore = PatElemT (Annotations.LetBound lore)

-- | A pattern is conceptually just a list of names and their types.
data PatternT lore =
  Pattern { patternContextElements :: [PatElem lore]
          , patternValueElements   :: [PatElem lore]
          }

deriving instance Annotations lore => Ord (PatternT lore)
deriving instance Annotations lore => Show (PatternT lore)
deriving instance Annotations lore => Eq (PatternT lore)

instance Monoid (PatternT lore) where
  mempty = Pattern [] []
  Pattern cs1 vs1 `mappend` Pattern cs2 vs2 = Pattern (cs1++cs2) (vs1++vs2)

-- | A type alias for namespace control.
type Pattern = PatternT

-- | A local variable binding.
data Binding lore = Let { bindingPattern :: Pattern lore
                        , bindingLore :: Annotations.Exp lore
                        , bindingExp :: Exp lore
                        }

deriving instance Annotations lore => Ord (Binding lore)
deriving instance Annotations lore => Show (Binding lore)
deriving instance Annotations lore => Eq (Binding lore)

-- | The result of a body is a sequence of subexpressions.
type Result = [SubExp]

-- | A body consists of a number of bindings, terminating in a result
-- (essentially a tuple literal).
data BodyT lore = Body { bodyLore :: Annotations.Body lore
                       , bodyBindings :: [Binding lore]
                       , bodyResult :: Result
                       }

deriving instance Annotations lore => Ord (BodyT lore)
deriving instance Annotations lore => Show (BodyT lore)
deriving instance Annotations lore => Eq (BodyT lore)

type Body = BodyT

-- | Binary operators.
data BinOp = Plus -- Binary Ops for Numbers
           | Minus
           | Pow
           | Times
           | FloatDiv
           | Div -- ^ Rounds towards negative infinity.
           | Mod
           | Quot -- ^ Rounds towards zero.
           | Rem
           | ShiftR
           | ShiftL
           | Band
           | Xor
           | Bor
           | LogAnd
           | LogOr
           -- Relational Ops for all basic types at least
           | Equal
           | Less
           | Leq
             deriving (Eq, Ord, Enum, Bounded, Show)

-- | The new dimension in a 'Reshape'-like operation.  This allows us to
-- disambiguate "real" reshapes, that change the actual shape of the
-- array, from type coercions that are just present to make the types
-- work out.
data DimChange d = DimCoercion d
                   -- ^ The new dimension is guaranteed to be numerically
                   -- equal to the old one.
                 | DimNew d
                   -- ^ The new dimension is not necessarily numerically
                   -- equal to the old one.
                 deriving (Eq, Ord, Show)

instance Functor DimChange where
  fmap f (DimCoercion d) = DimCoercion $ f d
  fmap f (DimNew      d) = DimNew $ f d

instance Foldable DimChange where
  foldMap f (DimCoercion d) = f d
  foldMap f (DimNew      d) = f d

instance Traversable DimChange where
  traverse f (DimCoercion d) = DimCoercion <$> f d
  traverse f (DimNew      d) = DimNew <$> f d

-- | A list of 'DimChange's, indicating the new dimensions of an array.
type ShapeChange d = [DimChange d]

data PrimOp lore
  = SubExp SubExp
    -- ^ Subexpressions, doubling as tuple literals if the
    -- list has anything but a single element.

  | ArrayLit  [SubExp] Type
    -- ^ Array literals, e.g., @[ [1+x, 3], [2, 1+4] ]@.
    -- Second arg is the element type of of the rows of the array.
    -- Scalar operations

  | BinOp BinOp SubExp SubExp BasicType
    -- ^ The type is the result type.

  | Not SubExp -- ^ E.g., @! True == False@.
  | Negate SubExp -- ^ E.g., @-(-1) = 1@.
  | Complement SubExp -- ^ E.g., @~(~1) = 1@.
  | Abs SubExp -- ^ @abs(-2) = 2@.
  | Signum SubExp -- ^ @signum(2)@ = 1.

  -- Assertion management.
  | Assert SubExp SrcLoc
  -- ^ Turn a boolean into a certificate, halting the
  -- program if the boolean is false.

  -- Primitive array operations

  | Index Certificates
          VName
          [SubExp]

  -- ^ 3rd arg are (optional) certificates for bounds
  -- checking.  If given (even as an empty list), no
  -- run-time bounds checking is done.

  | Split Certificates [SubExp] VName
  -- ^ 2nd arg is sizes of arrays you back, which is
  -- different from what the external language does.
  -- In the internal langauge,
  -- @a = [1,2,3,4]@
  -- @split( (1,0,2) , a ) = {[1], [], [2,3]}@

  | Concat Certificates VName [VName] SubExp
  -- ^ @concat([1],[2, 3, 4]) = [1, 2, 3, 4]@.

  | Copy VName
  -- ^ Copy the given array.  The result will not alias anything.

  -- Array construction.
  | Iota SubExp
  -- ^ @iota(n) = [0,1,..,n-1]@
  | Replicate SubExp SubExp
  -- ^ @replicate(3,1) = [1, 1, 1]@
  | Scratch BasicType [SubExp]
  -- ^ Create array of given type and shape, with undefined elements.

  -- Array index space transformation.
  | Reshape Certificates (ShapeChange SubExp) VName
   -- ^ 1st arg is the new shape, 2nd arg is the input array *)

  | Rearrange Certificates [Int] VName
  -- ^ Permute the dimensions of the input array.  The list
  -- of integers is a list of dimensions (0-indexed), which
  -- must be a permutation of @[0,n-1]@, where @n@ is the
  -- number of dimensions in the input array.

  | Stripe Certificates SubExp VName

  | Unstripe Certificates SubExp VName

  | Partition Certificates Int VName [VName]
    -- ^ First variable is the flag array, second is the element
    -- arrays.  If no arrays are given, the returned offsets are zero,
    -- and no arrays are returned.

  | Alloc SubExp Space
    -- ^ Allocate a memory block.  This really should not be an
    -- expression, but what are you gonna do...
  deriving (Eq, Ord, Show)

data LoopOp lore
  = DoLoop [VName] [(FParam lore, SubExp)] LoopForm (BodyT lore)
    -- ^ @loop {b} <- {a} = {v} (for i < n|while b) do b@.

  | Map Certificates SubExp (LambdaT lore) [VName]
    -- ^ @map(+1, {1,2,..,n}) = [2,3,..,n+1]@.

  | ConcatMap Certificates SubExp (LambdaT lore) [[VName]]

  | Reduce  Certificates SubExp (LambdaT lore) [(SubExp, VName)]
  | Scan   Certificates SubExp (LambdaT lore) [(SubExp, VName)]
  | Redomap Certificates SubExp (LambdaT lore) (LambdaT lore) [SubExp] [VName]
  | Stream Certificates SubExp (StreamForm lore) (ExtLambdaT lore) [VName] ChunkIntent

  | Kernel Certificates SubExp VName [(VName, SubExp)] [KernelInput lore]
    [(Type, [Int])] (Body lore)
  | ReduceKernel Certificates SubExp
    KernelSize
    (LambdaT lore)
    (LambdaT lore)
    [SubExp]
    [VName]

data StreamForm lore  = MapLike    StreamOrd
                      | RedLike    StreamOrd (LambdaT lore) [SubExp]
                      | Sequential [SubExp]
                        deriving (Eq, Ord, Show)

data KernelInput lore = KernelInput { kernelInputParam :: FParam lore
                                    , kernelInputArray :: VName
                                    , kernelInputIndices :: [SubExp]
                                    }

deriving instance Annotations lore => Eq (KernelInput lore)
deriving instance Annotations lore => Show (KernelInput lore)
deriving instance Annotations lore => Ord (KernelInput lore)

data KernelSize = KernelSize { kernelWorkgroups :: SubExp
                             , kernelWorkgroupSize :: SubExp
                             , kernelElementsPerThread :: SubExp
                             , kernelTotalElements :: SubExp
                             , kernelThreadOffsetMultiple :: SubExp
                             }
                deriving (Eq, Ord, Show)

-- | a @scan op ne xs@ can either be /'ScanInclusive'/ or /'ScanExclusive'/.
-- Inclusive = @[ ne `op` x_1 , ne `op` x_1 `op` x_2 , ... , ne `op` x_1 ... `op` x_n ]@
-- Exclusive = @[ ne, ne `op` x_1, ... , ne `op` x_1 ... `op` x_{n-1} ]@
--
-- Both versions generate arrays of the same size as @xs@ (this is not
-- always the semantics).
--
-- An easy way to remember which is which, is that inclusive /includes/
-- the last element in the calculation, whereas the exclusive does not
data ScanType = ScanInclusive
              | ScanExclusive
              deriving(Eq, Ord, Show)

-- | Segmented version of SOACS that use flat array representation.
-- This means a /single/ flat array for data, and segment descriptors
-- (integer arrays) for each dimension of the array.
--
-- For example the array
-- @ [ [ [1,2] , [3,4,5] ]
--   , [ [6]             ]
--   , []
--   ]
-- @
--
-- Can be represented as
-- @ data  = [1,2, 3,4,5, 6    ]
--   seg_1 = [2,   3,     1,   ]
--   seg_0 = [2,          1,  0]
-- @
data SegOp lore = SegReduce Certificates SubExp (LambdaT lore) [(SubExp, VName)] VName
                  -- ^ @map (\xs -> reduce(op,ne,xs), xss@ can loosely
                  -- be transformed into
                  -- @segreduce(op, ne, xss_flat, xss_descpritor)@
                  --
                  -- Note that this requires the neutral element to be constant
                | SegScan Certificates SubExp ScanType (LambdaT lore) [(SubExp, VName)] VName
                  -- ^ Identical to 'Scan', except that the last arg
                  -- is a segment descriptor.
                | SegReplicate Certificates VName VName (Maybe VName)
                  -- ^ @segreplicate(counts,data,seg)@ splits the
                  -- @data@ array into subarrays based on the lengths
                  -- given in @seg@. Subarray @sa_i@ is replicated
                  -- @counts_i@ times.
                  --
                  -- If @seg@ is @Nothing@, this is the same as
                  -- @seg = replicate (length counts) 1@
                  --
                  -- It should always be the case that
                  -- @length(counts) == length(seg)@
                deriving (Eq, Ord, Show)

deriving instance Annotations lore => Eq (LoopOp lore)
deriving instance Annotations lore => Show (LoopOp lore)
deriving instance Annotations lore => Ord (LoopOp lore)

data LoopForm = ForLoop VName SubExp
              | WhileLoop VName
              deriving (Eq, Show, Ord)

-- | Futhark Expression Language: literals + vars + int binops + array
-- constructors + array combinators (SOAC) + if + function calls +
-- let + tuples (literals & identifiers) TODO: please add float,
-- double, long int, etc.
data ExpT lore
  = PrimOp (PrimOp lore)
    -- ^ A simple (non-recursive) operation.

  | LoopOp (LoopOp lore)

  | SegOp (SegOp lore)

  | Apply  Name [(SubExp, Diet)] (Annotations.RetType lore)

  | If     SubExp (BodyT lore) (BodyT lore) [ExtType]

deriving instance Annotations lore => Eq (ExpT lore)
deriving instance Annotations lore => Show (ExpT lore)
deriving instance Annotations lore => Ord (ExpT lore)

-- | A type alias for namespace control.
type Exp = ExpT

-- | Anonymous function for use in a SOAC.
data LambdaT lore =
  Lambda { lambdaIndex      :: VName
         , lambdaParams     :: [LParam lore]
         , lambdaBody       :: BodyT lore
         , lambdaReturnType :: [Type]
         }

deriving instance Annotations lore => Eq (LambdaT lore)
deriving instance Annotations lore => Show (LambdaT lore)
deriving instance Annotations lore => Ord (LambdaT lore)

type Lambda = LambdaT

-- | Anonymous function for use in a SOAC, with an existential return
-- type.
data ExtLambdaT lore =
  ExtLambda { extLambdaIndex      :: VName
            , extLambdaParams     :: [LParam lore]
            , extLambdaBody       :: BodyT lore
            , extLambdaReturnType :: [ExtType]
            }

deriving instance Annotations lore => Eq (ExtLambdaT lore)
deriving instance Annotations lore => Show (ExtLambdaT lore)
deriving instance Annotations lore => Ord (ExtLambdaT lore)

type ExtLambda = ExtLambdaT

type FParam lore = ParamT (Annotations.FParam lore)

type LParam lore = ParamT (Annotations.LParam lore)

-- | Function Declarations
data FunDecT lore = FunDec { funDecName :: Name
                           , funDecRetType :: Annotations.RetType lore
                           , funDecParams :: [FParam lore]
                           , funDecBody :: BodyT lore
                           }

deriving instance Annotations lore => Eq (FunDecT lore)
deriving instance Annotations lore => Show (FunDecT lore)
deriving instance Annotations lore => Ord (FunDecT lore)

type FunDec = FunDecT

-- | An entire Futhark program.
newtype ProgT lore = Prog { progFunctions :: [FunDec lore] }
                     deriving (Eq, Ord, Show)

type Prog = ProgT
