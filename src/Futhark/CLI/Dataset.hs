{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}

-- | @futhark dataset@
module Futhark.CLI.Dataset (main) where

import Control.Monad
import Control.Monad.ST
import qualified Data.Binary as Bin
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Vector.Generic (freeze)
import qualified Data.Vector.Storable as SVec
import qualified Data.Vector.Storable.Mutable as USVec
import Data.Word
import qualified Futhark.Data as V
import Futhark.Data.Reader (readValues)
import Futhark.Util.Options
import Language.Futhark.Parser
import Language.Futhark.Pretty ()
import Language.Futhark.Prop (UncheckedTypeExp)
import Language.Futhark.Syntax hiding
  ( FloatValue (..),
    IntValue (..),
    PrimValue (..),
    Value,
    ValueType,
  )
import System.Exit
import System.IO
import System.Random.PCG (Variate, initialize, uniformR)

-- | Run @futhark dataset@.
main :: String -> [String] -> IO ()
main = mainWithOptions initialDataOptions commandLineOptions "options..." f
  where
    f [] config
      | null $ optOrders config = Just $ do
        maybe_vs <- readValues <$> BS.getContents
        case maybe_vs of
          Nothing -> do
            hPutStrLn stderr "Malformed data on standard input."
            exitFailure
          Just vs ->
            case format config of
              Text -> mapM_ (T.putStrLn . V.valueText) vs
              Binary -> mapM_ (BS.putStr . Bin.encode) vs
              Type -> mapM_ (T.putStrLn . V.valueTypeText . V.valueType) vs
      | otherwise =
        Just $
          zipWithM_
            ($)
            (optOrders config)
            [fromIntegral (optSeed config) ..]
    f _ _ =
      Nothing

data OutputFormat
  = Text
  | Binary
  | Type
  deriving (Eq, Ord, Show)

data DataOptions = DataOptions
  { optSeed :: Int,
    optRange :: RandomConfiguration,
    optOrders :: [Word64 -> IO ()],
    format :: OutputFormat
  }

initialDataOptions :: DataOptions
initialDataOptions = DataOptions 1 initialRandomConfiguration [] Text

commandLineOptions :: [FunOptDescr DataOptions]
commandLineOptions =
  [ Option
      "s"
      ["seed"]
      ( ReqArg
          ( \n ->
              case reads n of
                [(n', "")] ->
                  Right $ \config -> config {optSeed = n'}
                _ ->
                  Left $ do
                    hPutStrLn stderr $ "'" ++ n ++ "' is not an integer."
                    exitFailure
          )
          "SEED"
      )
      "The seed to use when initialising the RNG.",
    Option
      "g"
      ["generate"]
      ( ReqArg
          ( \t ->
              case tryMakeGenerator t of
                Right g ->
                  Right $ \config ->
                    config
                      { optOrders =
                          optOrders config
                            ++ [g (optRange config) (format config)]
                      }
                Left err ->
                  Left $ do
                    hPutStrLn stderr err
                    exitFailure
          )
          "TYPE"
      )
      "Generate a random value of this type.",
    Option
      []
      ["text"]
      (NoArg $ Right $ \opts -> opts {format = Text})
      "Output data in text format (must precede --generate).",
    Option
      "b"
      ["binary"]
      (NoArg $ Right $ \opts -> opts {format = Binary})
      "Output data in binary Futhark format (must precede --generate).",
    Option
      "t"
      ["type"]
      (NoArg $ Right $ \opts -> opts {format = Type})
      "Output the type (textually) rather than the value (must precede --generate).",
    setRangeOption "i8" seti8Range,
    setRangeOption "i16" seti16Range,
    setRangeOption "i32" seti32Range,
    setRangeOption "i64" seti64Range,
    setRangeOption "u8" setu8Range,
    setRangeOption "u16" setu16Range,
    setRangeOption "u32" setu32Range,
    setRangeOption "u64" setu64Range,
    setRangeOption "f32" setf32Range,
    setRangeOption "f64" setf64Range
  ]

setRangeOption ::
  Read a =>
  String ->
  (Range a -> RandomConfiguration -> RandomConfiguration) ->
  FunOptDescr DataOptions
setRangeOption tname set =
  Option
    ""
    [name]
    ( ReqArg
        ( \b ->
            let (lower, rest) = span (/= ':') b
                upper = drop 1 rest
             in case (reads lower, reads upper) of
                  ([(lower', "")], [(upper', "")]) ->
                    Right $ \config ->
                      config {optRange = set (lower', upper') $ optRange config}
                  _ ->
                    Left $ do
                      hPutStrLn stderr $ "Invalid bounds for " ++ tname ++ ": " ++ b
                      exitFailure
        )
        "MIN:MAX"
    )
    $ "Range of " ++ tname ++ " values."
  where
    name = tname ++ "-bounds"

tryMakeGenerator ::
  String ->
  Either String (RandomConfiguration -> OutputFormat -> Word64 -> IO ())
tryMakeGenerator t
  | Just vs <- readValues $ BS.pack t =
    return $ \_ fmt _ -> mapM_ (outValue fmt) vs
  | otherwise = do
    t' <- toValueType =<< either (Left . show) Right (parseType name (T.pack t))
    return $ \conf fmt seed -> do
      let v = randomValue conf t' seed
      outValue fmt v
  where
    name = "option " ++ t
    outValue Text = T.putStrLn . V.valueText
    outValue Binary = BS.putStr . Bin.encode
    outValue Type = T.putStrLn . V.valueTypeText . V.valueType

toValueType :: UncheckedTypeExp -> Either String V.ValueType
toValueType TETuple {} = Left "Cannot handle tuples yet."
toValueType TERecord {} = Left "Cannot handle records yet."
toValueType TEApply {} = Left "Cannot handle type applications yet."
toValueType TEArrow {} = Left "Cannot generate functions."
toValueType TESum {} = Left "Cannot handle sumtypes yet."
toValueType TEDim {} = Left "Cannot handle existential sizes."
toValueType (TEUnique t _) = toValueType t
toValueType (TEArray t d _) = do
  d' <- constantDim d
  V.ValueType ds t' <- toValueType t
  return $ V.ValueType (d' : ds) t'
  where
    constantDim (DimExpConst k _) = Right k
    constantDim _ = Left "Array has non-constant dimension declaration."
toValueType (TEVar (QualName [] v) _)
  | Just t <- lookup v m = Right $ V.ValueType [] t
  where
    m = map f [minBound .. maxBound]
    f t = (nameFromText (V.primTypeText t), t)
toValueType (TEVar v _) =
  Left $ "Unknown type " ++ pretty v

-- | Closed interval, as in @System.Random@.
type Range a = (a, a)

data RandomConfiguration = RandomConfiguration
  { i8Range :: Range Int8,
    i16Range :: Range Int16,
    i32Range :: Range Int32,
    i64Range :: Range Int64,
    u8Range :: Range Word8,
    u16Range :: Range Word16,
    u32Range :: Range Word32,
    u64Range :: Range Word64,
    f32Range :: Range Float,
    f64Range :: Range Double
  }

-- The following lines provide evidence about how Haskells record
-- system sucks.
seti8Range :: Range Int8 -> RandomConfiguration -> RandomConfiguration
seti8Range bounds config = config {i8Range = bounds}

seti16Range :: Range Int16 -> RandomConfiguration -> RandomConfiguration
seti16Range bounds config = config {i16Range = bounds}

seti32Range :: Range Int32 -> RandomConfiguration -> RandomConfiguration
seti32Range bounds config = config {i32Range = bounds}

seti64Range :: Range Int64 -> RandomConfiguration -> RandomConfiguration
seti64Range bounds config = config {i64Range = bounds}

setu8Range :: Range Word8 -> RandomConfiguration -> RandomConfiguration
setu8Range bounds config = config {u8Range = bounds}

setu16Range :: Range Word16 -> RandomConfiguration -> RandomConfiguration
setu16Range bounds config = config {u16Range = bounds}

setu32Range :: Range Word32 -> RandomConfiguration -> RandomConfiguration
setu32Range bounds config = config {u32Range = bounds}

setu64Range :: Range Word64 -> RandomConfiguration -> RandomConfiguration
setu64Range bounds config = config {u64Range = bounds}

setf32Range :: Range Float -> RandomConfiguration -> RandomConfiguration
setf32Range bounds config = config {f32Range = bounds}

setf64Range :: Range Double -> RandomConfiguration -> RandomConfiguration
setf64Range bounds config = config {f64Range = bounds}

initialRandomConfiguration :: RandomConfiguration
initialRandomConfiguration =
  RandomConfiguration
    (minBound, maxBound)
    (minBound, maxBound)
    (minBound, maxBound)
    (minBound, maxBound)
    (minBound, maxBound)
    (minBound, maxBound)
    (minBound, maxBound)
    (minBound, maxBound)
    (0.0, 1.0)
    (0.0, 1.0)

randomValue :: RandomConfiguration -> V.ValueType -> Word64 -> V.Value
randomValue conf (V.ValueType ds t) seed =
  case t of
    V.I8 -> gen i8Range V.I8Value
    V.I16 -> gen i16Range V.I16Value
    V.I32 -> gen i32Range V.I32Value
    V.I64 -> gen i64Range V.I64Value
    V.U8 -> gen u8Range V.U8Value
    V.U16 -> gen u16Range V.U16Value
    V.U32 -> gen u32Range V.U32Value
    V.U64 -> gen u64Range V.U64Value
    V.F32 -> gen f32Range V.F32Value
    V.F64 -> gen f64Range V.F64Value
    V.Bool -> gen (const (False, True)) V.BoolValue
  where
    gen range final = randomVector (range conf) final ds seed

randomVector ::
  (SVec.Storable v, Variate v) =>
  Range v ->
  (SVec.Vector Int -> SVec.Vector v -> V.Value) ->
  [Int] ->
  Word64 ->
  V.Value
randomVector range final ds seed = runST $ do
  -- USe some nice impure computation where we can preallocate a
  -- vector of the desired size, populate it via the random number
  -- generator, and then finally reutrn a frozen binary vector.
  arr <- USVec.new n
  g <- initialize 6364136223846793006 seed
  let fill i
        | i < n = do
          v <- uniformR range g
          USVec.write arr i v
          fill $! i + 1
        | otherwise =
          final (SVec.fromList ds) . SVec.convert <$> freeze arr
  fill 0
  where
    n = product ds
