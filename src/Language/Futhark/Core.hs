-- | This module contains very basic definitions for Futhark - so basic,
-- that they can be shared between the internal and external
-- representation.
module Language.Futhark.Core
  ( Uniqueness(..)
  , BasicType(..)
  , BasicValue(..)
  , basicValueType
  , blankBasicValue
  , ChunkIntent(..)
  , StreamOrd(..)

  -- * Location utilities
  , locStr

  -- * Name handling
  , Name
  , nameToString
  , nameFromString
  , ID(..)
  , baseTag
  , baseName
  , baseString
  , VName
  , VarName(..)

  -- * Special identifiers
  , defaultEntryPoint
  , isBuiltInFunction
  , builtInFunctions

    -- * Integer re-export
  , Int32
  )

where

import Data.Char
import Data.Hashable
import Data.Int (Int32)
import Data.Loc
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import qualified Data.HashMap.Lazy as HM

import Text.PrettyPrint.Mainland
import Text.Printf

-- | The uniqueness attribute of a type.  This essentially indicates
-- whether or not in-place modifications are acceptable.
data Uniqueness = Unique    -- ^ At most one outer reference.
                | Nonunique -- ^ Any number of references.
                  deriving (Eq, Ord, Show)

instance Monoid Uniqueness where
  mempty = Unique
  _ `mappend` Nonunique = Nonunique
  Nonunique `mappend` _ = Nonunique
  u `mappend` _         = u

instance Hashable Uniqueness where
  hashWithSalt salt Unique    = salt
  hashWithSalt salt Nonunique = salt * 2

data ChunkIntent = MaxChunk
                 | MinChunk
                    deriving (Eq, Ord, Show)

data StreamOrd  = InOrder
                | Disorder
                    deriving (Eq, Ord, Show)

-- | Low-level primitive types.  TODO: please add float, double, long
-- int, etc.
data BasicType = Int
               | Bool
               | Char
               | Float32
               | Float64
               | Cert
                 deriving (Eq, Ord, Show, Enum, Bounded)

-- | Non-array values.
data BasicValue = IntVal !Int32
                | Float32Val !Float
                | Float64Val !Double
                | LogVal !Bool
                | CharVal !Char
                | Checked -- ^ The only value of type @cert@.
                  deriving (Eq, Ord, Show)

-- | The type of a basic value.
basicValueType :: BasicValue -> BasicType
basicValueType (IntVal _) = Int
basicValueType (Float32Val _) = Float32
basicValueType (Float64Val _) = Float64
basicValueType (LogVal _) = Bool
basicValueType (CharVal _) = Char
basicValueType Checked = Cert

-- | A "blank" value of the given basic type - this is zero, or
-- whatever is close to it.  Don't depend on this value, but use it
-- for e.g. creating arrays to be populated by do-loops.
blankBasicValue :: BasicType -> BasicValue
blankBasicValue Int = IntVal 0
blankBasicValue Float32 = Float32Val 0.0
blankBasicValue Float64 = Float64Val 0.0
blankBasicValue Bool = LogVal False
blankBasicValue Char = CharVal '\0'
blankBasicValue Cert = Checked

instance Pretty BasicType where
  ppr Int = text "int"
  ppr Char = text "char"
  ppr Bool = text "bool"
  ppr Float32 = text "float32"
  ppr Float64 = text "float64"
  ppr Cert = text "cert"

instance Pretty BasicValue where
  ppr (IntVal x) = text $ show x
  ppr (CharVal c) = text $ show c
  ppr (LogVal b) = text $ show b
  ppr (Float32Val x) = text $ printf "%f" x
  ppr (Float64Val x) = text $ printf "%f" x
  ppr Checked = text "Checked"

-- | The name of the default program entry point (main).
defaultEntryPoint :: Name
defaultEntryPoint = nameFromString "main"

-- | @isBuiltInFunction k@ is 'True' if @k@ is an element of 'builtInFunctions'.
isBuiltInFunction :: Name -> Bool
isBuiltInFunction fnm = fnm `HM.member` builtInFunctions

-- | A map of all built-in functions and their types.
builtInFunctions :: HM.HashMap Name (BasicType,[BasicType])
builtInFunctions = HM.fromList $ map namify
                   [("toFloat32", (Float32, [Int]))
                   ,("trunc32", (Int, [Float32]))
                   ,("sqrt32", (Float32, [Float32]))
                   ,("log32", (Float32, [Float32]))
                   ,("exp32", (Float32, [Float32]))

                   ,("toFloat64", (Float64, [Int]))
                   ,("trunc64", (Int, [Float64]))
                   ,("sqrt64", (Float64, [Float64]))
                   ,("log64", (Float64, [Float64]))
                   ,("exp64", (Float64, [Float64]))

                   ,("num_groups", (Int, []))
                   ,("group_size", (Int, []))
                   ]
  where namify (k,v) = (nameFromString k, v)

-- | The abstract (not really) type representing names in the Futhark
-- compiler.  'String's, being lists of characters, are very slow,
-- while 'T.Text's are based on byte-arrays.
newtype Name = Name T.Text
  deriving (Show, Eq, Ord)

instance Pretty Name where
  ppr = text . nameToString

instance Hashable Name where
  hashWithSalt salt (Name t) = hashWithSalt salt t

instance Monoid Name where
  Name t1 `mappend` Name t2 = Name $ t1 <> t2
  mempty = Name mempty

-- | Convert a name to the corresponding list of characters.
nameToString :: Name -> String
nameToString (Name t) = T.unpack t

-- | Convert a list of characters to the corresponding name.
nameFromString :: String -> Name
nameFromString = Name . T.pack

-- | A human-readable location string, of the form
-- @filename:lineno:columnno@.
locStr :: SrcLoc -> String
locStr (SrcLoc NoLoc) = "unknown location"
locStr (SrcLoc (Loc (Pos file line1 col1 _) (Pos _ line2 col2 _))) =
  -- Assume that both positions are in the same file (what would the
  -- alternative mean?)
  file ++ ":" ++ show line1 ++ ":" ++ show col1
       ++ "-" ++ show line2 ++ ":" ++ show col2

-- | An arbitrary value tagged with some integer.  Only the integer is
-- used in comparisons, no matter the type of @vn@.
newtype ID vn = ID (vn, Int)
  deriving (Show)

-- | Alias for a tagged 'Name'.  This is used as the name
-- representation in most the compiler.
type VName = ID Name

-- | Return the tag contained in the 'ID'.
baseTag :: ID vn -> Int
baseTag (ID (_, tag)) = tag

-- | Return the name contained in the 'ID'.
baseName :: ID vn -> vn
baseName (ID (vn, _)) = vn

-- | Return the base 'Name' converted to a string.
baseString :: VName -> String
baseString = nameToString . baseName

instance Eq (ID vn) where
  ID (_, x) == ID (_, y) = x == y

instance Ord (ID vn) where
  ID (_, x) `compare` ID (_, y) = x `compare` y

instance Pretty vn => Pretty (ID vn) where
  ppr (ID (vn, i)) = ppr vn <> text "_" <> text (show i)

instance Hashable (ID vn) where
  hashWithSalt salt (ID (_,i)) = salt * i

-- | A type that can be used for representing variable names.  These
-- must support tagging, as well as conversion to a textual format.
class (Ord vn, Show vn, Pretty vn, Hashable vn) => VarName vn where
  -- | Set the numeric tag associated with this name.
  setID :: vn -> Int -> vn
  -- | Identity-preserving prettyprinting of a name.  This means that
  -- if and only if @x == y@, @textual x == textual y@.
  textual :: vn -> String
  -- | Create a name based on a string and a numeric tag.
  varName :: String -> Maybe Int -> vn

instance VarName vn => VarName (ID vn) where
  setID (ID (vn, _)) i = ID (vn, i)
  textual (ID (vn, i)) = textual vn ++ '_' : show i
  varName s i = ID (varName s Nothing, fromMaybe 0 i)

instance VarName Name where
  setID (Name t) i = Name $ stripSuffix t <> T.pack ('_' : show i)
  textual = nameToString
  varName s (Just i) = nameFromString s `setID` i
  varName s Nothing = nameFromString s

-- | Chop off terminating underscore followed by numbers.
stripSuffix :: T.Text -> T.Text
stripSuffix = T.dropWhileEnd (=='_') . T.dropWhileEnd isDigit
