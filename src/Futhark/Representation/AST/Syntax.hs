{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances, StandaloneDeriving #-}
-- | Futhark core language skeleton.  Concrete representations further
-- extend this skeleton by defining a "lore", which specifies concrete
-- annotations ("Futhark.Representation.AST.Annotations") and
-- semantics.
module Futhark.Representation.AST.Syntax
  (
    module Language.Futhark.Core
  , module Futhark.Representation.AST.Annotations
  , module Futhark.Representation.AST.Syntax.Core

  -- * Types
  , Uniqueness(..)
  , NoUniqueness(..)
  , Shape(..)
  , ExtDimSize(..)
  , ExtShape(..)
  , Rank(..)
  , ArrayShape(..)
  , Space (..)
  , TypeBase(..)
  , Diet(..)

  -- * Values
  , PrimValue(..)
  , Value(..)

  -- * Abstract syntax tree
  , Ident (..)
  , SubExp(..)
  , Bindage (..)
  , PatElemT (..)
  , PatternT (..)
  , Pattern
  , Binding(..)
  , Result
  , BodyT(..)
  , Body
  , PrimOp (..)
  , UnOp (..)
  , BinOp (..)
  , CmpOp (..)
  , ConvOp (..)
  , DimChange (..)
  , ShapeChange
  , ExpT(..)
  , Exp
  , LoopForm (..)
  , LambdaT(..)
  , Lambda
  , ExtLambdaT (..)
  , ExtLambda

  -- * Definitions
  , ParamT (..)
  , FParam
  , LParam
  , FunDefT (..)
  , FunDef
  , ProgT(..)
  , Prog
  )
  where

import Control.Applicative
import Data.Foldable
import Data.Monoid
import Data.Traversable
import Data.Loc

import Prelude

import Language.Futhark.Core
import Futhark.Representation.AST.Annotations
import Futhark.Representation.AST.Syntax.Core

-- | A pattern is conceptually just a list of names and their types.
data PatternT attr =
  Pattern { patternContextElements :: [PatElem attr]
          , patternValueElements   :: [PatElem attr]
          }
  deriving (Ord, Show, Eq)

instance Monoid (PatternT lore) where
  mempty = Pattern [] []
  Pattern cs1 vs1 `mappend` Pattern cs2 vs2 = Pattern (cs1++cs2) (vs1++vs2)

-- | A type alias for namespace control.
type Pattern lore = PatternT (LetAttr lore)

-- | A local variable binding.
data Binding lore = Let { bindingPattern :: Pattern lore
                        , bindingLore :: ExpAttr lore
                        , bindingExp :: Exp lore
                        }

deriving instance Annotations lore => Ord (Binding lore)
deriving instance Annotations lore => Show (Binding lore)
deriving instance Annotations lore => Eq (Binding lore)

-- | The result of a body is a sequence of subexpressions.
type Result = [SubExp]

-- | A body consists of a number of bindings, terminating in a result
-- (essentially a tuple literal).
data BodyT lore = Body { bodyLore :: BodyAttr lore
                       , bodyBindings :: [Binding lore]
                       , bodyResult :: Result
                       }

deriving instance Annotations lore => Ord (BodyT lore)
deriving instance Annotations lore => Show (BodyT lore)
deriving instance Annotations lore => Eq (BodyT lore)

type Body = BodyT

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

-- | A primitive operation that returns something of known size and
-- does not itself contain any bindings.
data PrimOp lore
  = SubExp SubExp
    -- ^ Subexpressions, doubling as tuple literals if the
    -- list has anything but a single element.

  | ArrayLit  [SubExp] Type
    -- ^ Array literals, e.g., @[ [1+x, 3], [2, 1+4] ]@.
    -- Second arg is the element type of of the rows of the array.
    -- Scalar operations

  | UnOp UnOp SubExp
    -- ^ Unary operation - result type is the same as the input type.

  | BinOp BinOp SubExp SubExp
    -- ^ Binary operation - result type is the same as the input
    -- types.

  | CmpOp CmpOp SubExp SubExp
    -- ^ Comparison - result type is always boolean.

  | ConvOp ConvOp SubExp
    -- ^ Conversion "casting".

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
  | Iota SubExp SubExp SubExp
  -- ^ @iota(n, x, s) = [x,x+s,..,x+(n-1)*s]@
  | Replicate SubExp SubExp
  -- ^ @replicate(3,1) = [1, 1, 1]@
  | Scratch PrimType [SubExp]
  -- ^ Create array of given type and shape, with undefined elements.

  -- Array index space transformation.
  | Reshape Certificates (ShapeChange SubExp) VName
   -- ^ 1st arg is the new shape, 2nd arg is the input array *)

  | Rearrange Certificates [Int] VName
  -- ^ Permute the dimensions of the input array.  The list
  -- of integers is a list of dimensions (0-indexed), which
  -- must be a permutation of @[0,n-1]@, where @n@ is the
  -- number of dimensions in the input array.

  | Partition Certificates Int VName [VName]
    -- ^ First variable is the flag array, second is the element
    -- arrays.  If no arrays are given, the returned offsets are zero,
    -- and no arrays are returned.
  deriving (Eq, Ord, Show)

-- | The root Futhark expression type.  The 'Op' constructor contains
-- a lore-specific operation.  Do-loops, branches and function calls
-- are special.  Everything else is a simple 'PrimOp'.
data ExpT lore
  = PrimOp (PrimOp lore)
    -- ^ A simple (non-recursive) operation.

  | Apply  Name [(SubExp, Diet)] (RetType lore)

  | If     SubExp (BodyT lore) (BodyT lore) [ExtType]

  | DoLoop [(FParam lore, SubExp)] [(FParam lore, SubExp)] LoopForm (BodyT lore)
    -- ^ @loop {a} = {v} (for i < n|while b) do b@.  The merge
    -- parameters are divided into context and value part.

  | Op (Op lore)

deriving instance Annotations lore => Eq (ExpT lore)
deriving instance Annotations lore => Show (ExpT lore)
deriving instance Annotations lore => Ord (ExpT lore)

-- | For-loop or while-loop?
data LoopForm = ForLoop VName SubExp
              | WhileLoop VName
              deriving (Eq, Show, Ord)

-- | A type alias for namespace control.
type Exp = ExpT

-- | Anonymous function for use in a SOAC.
data LambdaT lore =
  Lambda { lambdaParams     :: [LParam lore]
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
  ExtLambda { extLambdaParams     :: [LParam lore]
            , extLambdaBody       :: BodyT lore
            , extLambdaReturnType :: [ExtType]
            }

deriving instance Annotations lore => Eq (ExtLambdaT lore)
deriving instance Annotations lore => Show (ExtLambdaT lore)
deriving instance Annotations lore => Ord (ExtLambdaT lore)

type ExtLambda = ExtLambdaT

type FParam lore = ParamT (FParamAttr lore)

type LParam lore = ParamT (LParamAttr lore)

-- | Function Declarations
data FunDefT lore = FunDef { funDefEntryPoint :: Bool
                             -- ^ True if this function is an entry point.
                           , funDefName :: Name
                           , funDefRetType :: RetType lore
                           , funDefParams :: [FParam lore]
                           , funDefBody :: BodyT lore
                           }

deriving instance Annotations lore => Eq (FunDefT lore)
deriving instance Annotations lore => Show (FunDefT lore)
deriving instance Annotations lore => Ord (FunDefT lore)

type FunDef = FunDefT

-- | An entire Futhark program.
newtype ProgT lore = Prog { progFunctions :: [FunDef lore] }
                     deriving (Eq, Ord, Show)

type Prog = ProgT
