{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Trustworthy #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Simple C runtime representation.
module Futhark.CodeGen.Backends.SimpleRep
  ( tupleField,
    funName,
    defaultMemBlockType,
    intTypeToCType,
    primTypeToCType,
    signedPrimTypeToCType,
    arrayName,
    opaqueName,
    externalValueType,
    cproduct,
    csum,

    -- * Primitive value operations
    cIntOps,
    cFloat32Ops,
    cFloat32Funs,
    cFloat64Ops,
    cFloat64Funs,
    cFloatConvOps,

    -- * Storing/restoring values in byte sequences
    storageSize,
    storeValueHeader,
    loadValueHeader,
  )
where

import Data.Bits (shiftR, xor)
import Data.Char (isAlphaNum, isDigit, ord)
import Futhark.CodeGen.ImpCode
import Futhark.Util (zEncodeString)
import Futhark.Util.Pretty (prettyOneLine)
import qualified Language.C.Quote.C as C
import qualified Language.C.Syntax as C
import Text.Printf

-- | The C type corresponding to a signed integer type.
intTypeToCType :: IntType -> C.Type
intTypeToCType Int8 = [C.cty|typename int8_t|]
intTypeToCType Int16 = [C.cty|typename int16_t|]
intTypeToCType Int32 = [C.cty|typename int32_t|]
intTypeToCType Int64 = [C.cty|typename int64_t|]

-- | The C type corresponding to an unsigned integer type.
uintTypeToCType :: IntType -> C.Type
uintTypeToCType Int8 = [C.cty|typename uint8_t|]
uintTypeToCType Int16 = [C.cty|typename uint16_t|]
uintTypeToCType Int32 = [C.cty|typename uint32_t|]
uintTypeToCType Int64 = [C.cty|typename uint64_t|]

-- | The C type corresponding to a float type.
floatTypeToCType :: FloatType -> C.Type
floatTypeToCType Float32 = [C.cty|float|]
floatTypeToCType Float64 = [C.cty|double|]

-- | The C type corresponding to a primitive type.  Integers are
-- assumed to be unsigned.
primTypeToCType :: PrimType -> C.Type
primTypeToCType (IntType t) = intTypeToCType t
primTypeToCType (FloatType t) = floatTypeToCType t
primTypeToCType Bool = [C.cty|typename bool|]
primTypeToCType Unit = [C.cty|typename bool|]

-- | The C type corresponding to a primitive type.  Integers are
-- assumed to have the specified sign.
signedPrimTypeToCType :: Signedness -> PrimType -> C.Type
signedPrimTypeToCType TypeUnsigned (IntType t) = uintTypeToCType t
signedPrimTypeToCType TypeDirect (IntType t) = intTypeToCType t
signedPrimTypeToCType _ t = primTypeToCType t

-- | @tupleField i@ is the name of field number @i@ in a tuple.
tupleField :: Int -> String
tupleField i = "v" ++ show i

-- | @funName f@ is the name of the C function corresponding to
-- the Futhark function @f@.
funName :: Name -> String
funName = ("futrts_" ++) . zEncodeString . nameToString

funName' :: String -> String
funName' = funName . nameFromString

-- | The type of memory blocks in the default memory space.
defaultMemBlockType :: C.Type
defaultMemBlockType = [C.cty|char*|]

-- | The name of exposed array type structs.
arrayName :: PrimType -> Signedness -> Int -> String
arrayName pt signed rank =
  prettySigned (signed == TypeUnsigned) pt ++ "_" ++ show rank ++ "d"

-- | The name of exposed opaque types.
opaqueName :: String -> [ValueDesc] -> String
opaqueName s _
  | valid = "opaque_" ++ s
  where
    valid =
      head s /= '_'
        && not (isDigit $ head s)
        && all ok s
    ok c = isAlphaNum c || c == '_'
opaqueName s vds = "opaque_" ++ hash (zipWith xor [0 ..] $ map ord (s ++ concatMap p vds))
  where
    p (ScalarValue pt signed _) =
      show (pt, signed)
    p (ArrayValue _ space pt signed dims) =
      show (space, pt, signed, length dims)

    -- FIXME: a stupid hash algorithm; may have collisions.
    hash =
      printf "%x" . foldl xor 0
        . map
          ( iter . (* 0x45d9f3b)
              . iter
              . (* 0x45d9f3b)
              . iter
              . fromIntegral
          )
    iter x = ((x :: Word32) `shiftR` 16) `xor` x

-- | The type used to expose a Futhark value in the C API.  A pointer
-- in the case of arrays and opaques.
externalValueType :: ExternalValue -> C.Type
externalValueType (OpaqueValue _ desc vds) =
  [C.cty|struct $id:("futhark_" ++ opaqueName desc vds)*|]
externalValueType (TransparentValue _ (ArrayValue _ _ pt signed shape)) =
  [C.cty|struct $id:("futhark_" ++ arrayName pt signed (length shape))*|]
externalValueType (TransparentValue _ (ScalarValue pt signed _)) =
  signedPrimTypeToCType signed pt

-- | Return an expression multiplying together the given expressions.
-- If an empty list is given, the expression @1@ is returned.
cproduct :: [C.Exp] -> C.Exp
cproduct [] = [C.cexp|1|]
cproduct (e : es) = foldl mult e es
  where
    mult x y = [C.cexp|$exp:x * $exp:y|]

-- | Return an expression summing the given expressions.
-- If an empty list is given, the expression @0@ is returned.
csum :: [C.Exp] -> C.Exp
csum [] = [C.cexp|0|]
csum (e : es) = foldl mult e es
  where
    mult x y = [C.cexp|$exp:x + $exp:y|]

instance C.ToIdent Name where
  toIdent = C.toIdent . zEncodeString . nameToString

instance C.ToIdent VName where
  toIdent = C.toIdent . zEncodeString . pretty

instance C.ToExp VName where
  toExp v _ = [C.cexp|$id:v|]

instance C.ToExp IntValue where
  toExp (Int8Value v) = C.toExp v
  toExp (Int16Value v) = C.toExp v
  toExp (Int32Value v) = C.toExp v
  toExp (Int64Value v) = C.toExp v

instance C.ToExp FloatValue where
  toExp (Float32Value v) = C.toExp v
  toExp (Float64Value v) = C.toExp v

instance C.ToExp PrimValue where
  toExp (IntValue v) = C.toExp v
  toExp (FloatValue v) = C.toExp v
  toExp (BoolValue True) = C.toExp (1 :: Int8)
  toExp (BoolValue False) = C.toExp (0 :: Int8)
  toExp UnitValue = C.toExp (1 :: Int8)

instance C.ToExp SubExp where
  toExp (Var v) = C.toExp v
  toExp (Constant c) = C.toExp c

cIntOps :: [C.Definition]
cIntOps =
  concatMap (`map` [minBound .. maxBound]) ops
    ++ cIntPrimFuns
  where
    ops =
      [ mkAdd,
        mkSub,
        mkMul,
        mkUDiv,
        mkUDivUp,
        mkUMod,
        mkUDivSafe,
        mkUDivUpSafe,
        mkUModSafe,
        mkSDiv,
        mkSDivUp,
        mkSMod,
        mkSDivSafe,
        mkSDivUpSafe,
        mkSModSafe,
        mkSQuot,
        mkSRem,
        mkSQuotSafe,
        mkSRemSafe,
        mkSMin,
        mkUMin,
        mkSMax,
        mkUMax,
        mkShl,
        mkLShr,
        mkAShr,
        mkAnd,
        mkOr,
        mkXor,
        mkUlt,
        mkUle,
        mkSlt,
        mkSle,
        mkPow,
        mkIToB,
        mkBToI
      ]
        ++ map mkSExt [minBound .. maxBound]
        ++ map mkZExt [minBound .. maxBound]

    taggedI s Int8 = s ++ "8"
    taggedI s Int16 = s ++ "16"
    taggedI s Int32 = s ++ "32"
    taggedI s Int64 = s ++ "64"

    -- Use unsigned types for add/sub/mul so we can do
    -- well-defined overflow.
    mkAdd = simpleUintOp "add" [C.cexp|x + y|]
    mkSub = simpleUintOp "sub" [C.cexp|x - y|]
    mkMul = simpleUintOp "mul" [C.cexp|x * y|]
    mkUDiv = simpleUintOp "udiv" [C.cexp|x / y|]
    mkUDivUp = simpleUintOp "udiv_up" [C.cexp|(x+y-1) / y|]
    mkUMod = simpleUintOp "umod" [C.cexp|x % y|]
    mkUDivSafe = simpleUintOp "udiv_safe" [C.cexp|y == 0 ? 0 : x / y|]
    mkUDivUpSafe = simpleUintOp "udiv_up_safe" [C.cexp|y == 0 ? 0 : (x+y-1) / y|]
    mkUModSafe = simpleUintOp "umod_safe" [C.cexp|y == 0 ? 0 : x % y|]
    mkUMax = simpleUintOp "umax" [C.cexp|x < y ? y : x|]
    mkUMin = simpleUintOp "umin" [C.cexp|x < y ? x : y|]

    mkSDiv t =
      let ct = intTypeToCType t
       in [C.cedecl|static inline $ty:ct $id:(taggedI "sdiv" t)($ty:ct x, $ty:ct y) {
                         $ty:ct q = x / y;
                         $ty:ct r = x % y;
                         return q -
                           (((r != 0) && ((r < 0) != (y < 0))) ? 1 : 0);
             }|]
    mkSDivUp t =
      simpleIntOp "sdiv_up" [C.cexp|$id:(taggedI "sdiv" t)(x+y-1,y)|] t
    mkSMod t =
      let ct = intTypeToCType t
       in [C.cedecl|static inline $ty:ct $id:(taggedI "smod" t)($ty:ct x, $ty:ct y) {
                         $ty:ct r = x % y;
                         return r +
                           ((r == 0 || (x > 0 && y > 0) || (x < 0 && y < 0)) ? 0 : y);
              }|]
    mkSDivSafe t =
      simpleIntOp "sdiv_safe" [C.cexp|y == 0 ? 0 : $id:(taggedI "sdiv" t)(x,y)|] t
    mkSDivUpSafe t =
      simpleIntOp "sdiv_up_safe" [C.cexp|$id:(taggedI "sdiv_safe" t)(x+y-1,y)|] t
    mkSModSafe t =
      simpleIntOp "smod_safe" [C.cexp|y == 0 ? 0 : $id:(taggedI "smod" t)(x,y)|] t

    mkSQuot = simpleIntOp "squot" [C.cexp|x / y|]
    mkSRem = simpleIntOp "srem" [C.cexp|x % y|]
    mkSQuotSafe = simpleIntOp "squot_safe" [C.cexp|y == 0 ? 0 : x / y|]
    mkSRemSafe = simpleIntOp "srem_safe" [C.cexp|y == 0 ? 0 : x % y|]
    mkSMax = simpleIntOp "smax" [C.cexp|x < y ? y : x|]
    mkSMin = simpleIntOp "smin" [C.cexp|x < y ? x : y|]
    mkShl = simpleUintOp "shl" [C.cexp|x << y|]
    mkLShr = simpleUintOp "lshr" [C.cexp|x >> y|]
    mkAShr = simpleIntOp "ashr" [C.cexp|x >> y|]
    mkAnd = simpleUintOp "and" [C.cexp|x & y|]
    mkOr = simpleUintOp "or" [C.cexp|x | y|]
    mkXor = simpleUintOp "xor" [C.cexp|x ^ y|]
    mkUlt = uintCmpOp "ult" [C.cexp|x < y|]
    mkUle = uintCmpOp "ule" [C.cexp|x <= y|]
    mkSlt = intCmpOp "slt" [C.cexp|x < y|]
    mkSle = intCmpOp "sle" [C.cexp|x <= y|]

    -- We define some operations as macros rather than functions,
    -- because this allows us to use them as constant expressions
    -- in things like array sizes and static initialisers.
    macro name rhs =
      [C.cedecl|$esc:("#define " ++ name ++ "(x) (" ++ prettyOneLine rhs ++ ")")|]

    mkPow t =
      let ct = intTypeToCType t
       in [C.cedecl|static inline $ty:ct $id:(taggedI "pow" t)($ty:ct x, $ty:ct y) {
                         $ty:ct res = 1, rem = y;
                         while (rem != 0) {
                           if (rem & 1) {
                             res *= x;
                           }
                           rem >>= 1;
                           x *= x;
                         }
                         return res;
              }|]

    mkSExt from_t to_t = macro name [C.cexp|($ty:to_ct)(($ty:from_ct)x)|]
      where
        name = "sext_" ++ pretty from_t ++ "_" ++ pretty to_t
        from_ct = intTypeToCType from_t
        to_ct = intTypeToCType to_t

    mkZExt from_t to_t = macro name [C.cexp|($ty:to_ct)(($ty:from_ct)x)|]
      where
        name = "zext_" ++ pretty from_t ++ "_" ++ pretty to_t
        from_ct = uintTypeToCType from_t
        to_ct = intTypeToCType to_t

    mkBToI to_t =
      [C.cedecl|static inline $ty:to_ct
                    $id:name($ty:from_ct x) { return x; } |]
      where
        name = "btoi_bool_" ++ pretty to_t
        from_ct = primTypeToCType Bool
        to_ct = intTypeToCType to_t

    mkIToB from_t =
      [C.cedecl|static inline $ty:to_ct
                    $id:name($ty:from_ct x) { return x; } |]
      where
        name = "itob_" ++ pretty from_t ++ "_bool"
        to_ct = primTypeToCType Bool
        from_ct = intTypeToCType from_t

    simpleUintOp s e t =
      [C.cedecl|static inline $ty:ct $id:(taggedI s t)($ty:ct x, $ty:ct y) { return $exp:e; }|]
      where
        ct = uintTypeToCType t
    simpleIntOp s e t =
      [C.cedecl|static inline $ty:ct $id:(taggedI s t)($ty:ct x, $ty:ct y) { return $exp:e; }|]
      where
        ct = intTypeToCType t
    intCmpOp s e t =
      [C.cedecl|static inline typename bool $id:(taggedI s t)($ty:ct x, $ty:ct y) { return $exp:e; }|]
      where
        ct = intTypeToCType t
    uintCmpOp s e t =
      [C.cedecl|static inline typename bool $id:(taggedI s t)($ty:ct x, $ty:ct y) { return $exp:e; }|]
      where
        ct = uintTypeToCType t

cIntPrimFuns :: [C.Definition]
cIntPrimFuns =
  [C.cunit|
$esc:("#if defined(__OPENCL_VERSION__)")
   static typename int32_t $id:(funName' "popc8") (typename int8_t x) {
      return popcount(x);
   }
   static typename int32_t $id:(funName' "popc16") (typename int16_t x) {
      return popcount(x);
   }
   static typename int32_t $id:(funName' "popc32") (typename int32_t x) {
      return popcount(x);
   }
   static typename int32_t $id:(funName' "popc64") (typename int64_t x) {
      return popcount(x);
   }
$esc:("#elif defined(__CUDA_ARCH__)")
   static typename int32_t $id:(funName' "popc8") (typename int8_t x) {
      return __popc(zext_i8_i32(x));
   }
   static typename int32_t $id:(funName' "popc16") (typename int16_t x) {
      return __popc(zext_i16_i32(x));
   }
   static typename int32_t $id:(funName' "popc32") (typename int32_t x) {
      return __popc(x);
   }
   static typename int32_t $id:(funName' "popc64") (typename int64_t x) {
      return __popcll(x);
   }
$esc:("#else")
   static typename int32_t $id:(funName' "popc8") (typename int8_t x) {
     int c = 0;
     for (; x; ++c) {
       x &= x - 1;
     }
     return c;
    }
   static typename int32_t $id:(funName' "popc16") (typename int16_t x) {
     int c = 0;
     for (; x; ++c) {
       x &= x - 1;
     }
     return c;
   }
   static typename int32_t $id:(funName' "popc32") (typename int32_t x) {
     int c = 0;
     for (; x; ++c) {
       x &= x - 1;
     }
     return c;
   }
   static typename int32_t $id:(funName' "popc64") (typename int64_t x) {
     int c = 0;
     for (; x; ++c) {
       x &= x - 1;
     }
     return c;
   }
$esc:("#endif")

$esc:("#if defined(__OPENCL_VERSION__)")
   static typename uint8_t $id:(funName' "mul_hi8") (typename uint8_t a, typename uint8_t b) {
      return mul_hi(a, b);
   }
   static typename uint16_t $id:(funName' "mul_hi16") (typename uint16_t a, typename uint16_t b) {
      return mul_hi(a, b);
   }
   static typename uint32_t $id:(funName' "mul_hi32") (typename uint32_t a, typename uint32_t b) {
      return mul_hi(a, b);
   }
   static typename uint64_t $id:(funName' "mul_hi64") (typename uint64_t a, typename uint64_t b) {
      return mul_hi(a, b);
   }
$esc:("#elif defined(__CUDA_ARCH__)")
   static typename uint8_t $id:(funName' "mul_hi8") (typename uint8_t a, typename uint8_t b) {
     typename uint16_t aa = a;
     typename uint16_t bb = b;
     return (aa * bb) >> 8;
   }
   static typename uint16_t $id:(funName' "mul_hi16") (typename uint16_t a, typename uint16_t b) {
     typename uint32_t aa = a;
     typename uint32_t bb = b;
     return (aa * bb) >> 16;
   }
   static typename uint32_t $id:(funName' "mul_hi32") (typename uint32_t a, typename uint32_t b) {
      return mulhi(a, b);
   }
   static typename uint64_t $id:(funName' "mul_hi64") (typename uint64_t a, typename uint64_t b) {
      return mul64hi(a, b);
   }
$esc:("#else")
   static typename uint8_t $id:(funName' "mul_hi8") (typename uint8_t a, typename uint8_t b) {
     typename uint16_t aa = a;
     typename uint16_t bb = b;
     return (aa * bb) >> 8;
    }
   static typename uint16_t $id:(funName' "mul_hi16") (typename uint16_t a, typename uint16_t b) {
     typename uint32_t aa = a;
     typename uint32_t bb = b;
     return (aa * bb) >> 16;
    }
   static typename uint32_t $id:(funName' "mul_hi32") (typename uint32_t a, typename uint32_t b) {
     typename uint64_t aa = a;
     typename uint64_t bb = b;
     return (aa * bb) >> 32;
    }
   $esc:("#ifdef __EMSCRIPTEN__")
      static typename uint64_t $id:(funName' "mul_hi64") (typename uint64_t x, typename uint64_t y) {
        typename uint64_t a = x >> 32, b = x & 0xffffffff;
        typename uint64_t c = y >> 32, d = y & 0xffffffff;
        typename uint64_t ac = a * c;
        typename uint64_t bc = b * c;
        typename uint64_t ad = a * d;
        typename uint64_t bd = b * d;
        typename uint64_t mid34 = (bd >> 32) + (bc & 0xffffffff) + (ad & 0xffffffff);
        typename uint64_t upper64 = ac + (bc >> 32) + (ad >> 32) + (mid34 >> 32);
        return upper64;
       }
   $esc:("#else")
      static typename uint64_t $id:(funName' "mul_hi64") (typename uint64_t a, typename uint64_t b) {
        typename __uint128_t aa = a;
        typename __uint128_t bb = b;
        return (aa * bb) >> 64;
       }
   $esc:("#endif")
$esc:("#endif")

$esc:("#if defined(__OPENCL_VERSION__)")
   static typename uint8_t $id:(funName' "mad_hi8") (typename uint8_t a, typename uint8_t b, typename uint8_t c) {
      return mad_hi(a, b, c);
   }
   static typename uint16_t $id:(funName' "mad_hi16") (typename uint16_t a, typename uint16_t b, typename uint16_t c) {
      return mad_hi(a, b, c);
   }
   static typename uint32_t $id:(funName' "mad_hi32") (typename uint32_t a, typename uint32_t b, typename uint32_t c) {
      return mad_hi(a, b, c);
   }
   static typename uint64_t $id:(funName' "mad_hi64") (typename uint64_t a, typename uint64_t b, typename uint64_t c) {
      return mad_hi(a, b, c);
   }
$esc:("#else")
   static typename uint8_t $id:(funName' "mad_hi8") (typename uint8_t a, typename uint8_t b, typename uint8_t c) {
     return futrts_mul_hi8(a, b) + c;
    }
   static typename uint16_t $id:(funName' "mad_hi16") (typename uint16_t a, typename uint16_t b, typename uint16_t c) {
     return futrts_mul_hi16(a, b) + c;
    }
   static typename uint32_t $id:(funName' "mad_hi32") (typename uint32_t a, typename uint32_t b, typename uint32_t c) {
     return futrts_mul_hi32(a, b) + c;
    }
   static typename uint64_t $id:(funName' "mad_hi64") (typename uint64_t a, typename uint64_t b, typename uint64_t c) {
     return futrts_mul_hi64(a, b) + c;
    }
$esc:("#endif")


$esc:("#if defined(__OPENCL_VERSION__)")
   static typename int32_t $id:(funName' "clz8") (typename int8_t x) {
      return clz(x);
   }
   static typename int32_t $id:(funName' "clz16") (typename int16_t x) {
      return clz(x);
   }
   static typename int32_t $id:(funName' "clz32") (typename int32_t x) {
      return clz(x);
   }
   static typename int32_t $id:(funName' "clz64") (typename int64_t x) {
      return clz(x);
   }
$esc:("#elif defined(__CUDA_ARCH__)")
   static typename int32_t $id:(funName' "clz8") (typename int8_t x) {
      return __clz(zext_i8_i32(x))-24;
   }
   static typename int32_t $id:(funName' "clz16") (typename int16_t x) {
      return __clz(zext_i16_i32(x))-16;
   }
   static typename int32_t $id:(funName' "clz32") (typename int32_t x) {
      return __clz(x);
   }
   static typename int32_t $id:(funName' "clz64") (typename int64_t x) {
      return __clzll(x);
   }
$esc:("#else")
   static typename int32_t $id:(funName' "clz8") (typename int8_t x) {
    int n = 0;
    int bits = sizeof(x) * 8;
    for (int i = 0; i < bits; i++) {
        if (x < 0) break;
        n++;
        x <<= 1;
    }
    return n;
   }
   static typename int32_t $id:(funName' "clz16") (typename int16_t x) {
    int n = 0;
    int bits = sizeof(x) * 8;
    for (int i = 0; i < bits; i++) {
        if (x < 0) break;
        n++;
        x <<= 1;
    }
    return n;
   }
   static typename int32_t $id:(funName' "clz32") (typename int32_t x) {
    int n = 0;
    int bits = sizeof(x) * 8;
    for (int i = 0; i < bits; i++) {
        if (x < 0) break;
        n++;
        x <<= 1;
    }
    return n;
   }
   static typename int32_t $id:(funName' "clz64") (typename int64_t x) {
    int n = 0;
    int bits = sizeof(x) * 8;
    for (int i = 0; i < bits; i++) {
        if (x < 0) break;
        n++;
        x <<= 1;
    }
    return n;
   }
$esc:("#endif")

$esc:("#if defined(__OPENCL_VERSION__)")
   // OpenCL has ctz, but only from version 2.0, which we cannot assume we are using.
   static typename int32_t $id:(funName' "ctz8") (typename int8_t x) {
      int i = 0;
      for (; i < 8 && (x&1)==0; i++, x>>=1);
      return i;
   }
   static typename int32_t $id:(funName' "ctz16") (typename int16_t x) {
      int i = 0;
      for (; i < 16 && (x&1)==0; i++, x>>=1);
      return i;
   }
   static typename int32_t $id:(funName' "ctz32") (typename int32_t x) {
      int i = 0;
      for (; i < 32 && (x&1)==0; i++, x>>=1);
      return i;
   }
   static typename int32_t $id:(funName' "ctz64") (typename int64_t x) {
      int i = 0;
      for (; i < 64 && (x&1)==0; i++, x>>=1);
      return i;
   }
$esc:("#elif defined(__CUDA_ARCH__)")
   static typename int32_t $id:(funName' "ctz8") (typename int8_t x) {
     int y = __ffs(x);
     return y == 0 ? 8 : y-1;
   }
   static typename int32_t $id:(funName' "ctz16") (typename int16_t x) {
     int y = __ffs(x);
     return y == 0 ? 16 : y-1;
   }
   static typename int32_t $id:(funName' "ctz32") (typename int32_t x) {
     int y = __ffs(x);
     return y == 0 ? 32 : y-1;
   }
   static typename int32_t $id:(funName' "ctz64") (typename int64_t x) {
     int y = __ffsll(x);
     return y == 0 ? 64 : y-1;
   }
$esc:("#else")
// FIXME: assumes GCC or clang.
   static typename int32_t $id:(funName' "ctz8") (typename int8_t x) {
     return x == 0 ? 8 : __builtin_ctz((typename uint32_t)x);
   }
   static typename int32_t $id:(funName' "ctz16") (typename int16_t x) {
     return x == 0 ? 16 : __builtin_ctz((typename uint32_t)x);
   }
   static typename int32_t $id:(funName' "ctz32") (typename int32_t x) {
     return x == 0 ? 32 :  __builtin_ctz(x);
   }
   static typename int32_t $id:(funName' "ctz64") (typename int64_t x) {
     return x == 0 ? 64 : __builtin_ctzll(x);
   }
$esc:("#endif")
                |]

cFloat32Ops :: [C.Definition]
cFloat64Ops :: [C.Definition]
cFloatConvOps :: [C.Definition]
(cFloat32Ops, cFloat64Ops, cFloatConvOps) =
  ( map ($ Float32) mkOps,
    map ($ Float64) mkOps,
    [ mkFPConvFF "fpconv" from to
      | from <- [minBound .. maxBound],
        to <- [minBound .. maxBound]
    ]
  )
  where
    taggedF s Float32 = s ++ "32"
    taggedF s Float64 = s ++ "64"
    convOp s from to = s ++ "_" ++ pretty from ++ "_" ++ pretty to

    mkOps =
      [mkFDiv, mkFAdd, mkFSub, mkFMul, mkFMin, mkFMax, mkPow, mkCmpLt, mkCmpLe]
        ++ map (mkFPConvIF "sitofp") [minBound .. maxBound]
        ++ map (mkFPConvUF "uitofp") [minBound .. maxBound]
        ++ map (flip $ mkFPConvFI "fptosi") [minBound .. maxBound]
        ++ map (flip $ mkFPConvFU "fptoui") [minBound .. maxBound]

    mkFDiv = simpleFloatOp "fdiv" [C.cexp|x / y|]
    mkFAdd = simpleFloatOp "fadd" [C.cexp|x + y|]
    mkFSub = simpleFloatOp "fsub" [C.cexp|x - y|]
    mkFMul = simpleFloatOp "fmul" [C.cexp|x * y|]
    mkFMin = simpleFloatOp "fmin" [C.cexp|fmin(x, y)|]
    mkFMax = simpleFloatOp "fmax" [C.cexp|fmax(x, y)|]
    mkCmpLt = floatCmpOp "cmplt" [C.cexp|x < y|]
    mkCmpLe = floatCmpOp "cmple" [C.cexp|x <= y|]

    mkPow Float32 =
      [C.cedecl|static inline float fpow32(float x, float y) { return pow(x, y); }|]
    mkPow Float64 =
      [C.cedecl|static inline double fpow64(double x, double y) { return pow(x, y); }|]

    mkFPConv from_f to_f s from_t to_t =
      [C.cedecl|static inline $ty:to_ct
                    $id:(convOp s from_t to_t)($ty:from_ct x) { return ($ty:to_ct)x;} |]
      where
        from_ct = from_f from_t
        to_ct = to_f to_t

    mkFPConvFF = mkFPConv floatTypeToCType floatTypeToCType
    mkFPConvFI = mkFPConv floatTypeToCType intTypeToCType
    mkFPConvIF = mkFPConv intTypeToCType floatTypeToCType
    mkFPConvFU = mkFPConv floatTypeToCType uintTypeToCType
    mkFPConvUF = mkFPConv uintTypeToCType floatTypeToCType

    simpleFloatOp s e t =
      [C.cedecl|static inline $ty:ct $id:(taggedF s t)($ty:ct x, $ty:ct y) { return $exp:e; }|]
      where
        ct = floatTypeToCType t
    floatCmpOp s e t =
      [C.cedecl|static inline typename bool $id:(taggedF s t)($ty:ct x, $ty:ct y) { return $exp:e; }|]
      where
        ct = floatTypeToCType t

cFloat32Funs :: [C.Definition]
cFloat32Funs =
  [C.cunit|
    static inline typename bool $id:(funName' "isnan32")(float x) {
      return isnan(x);
    }

    static inline typename bool $id:(funName' "isinf32")(float x) {
      return isinf(x);
    }

$esc:("#ifdef __OPENCL_VERSION__")
    static inline float $id:(funName' "log32")(float x) {
      return log(x);
    }

    static inline float $id:(funName' "log2_32")(float x) {
      return log2(x);
    }

    static inline float $id:(funName' "log10_32")(float x) {
      return log10(x);
    }

    static inline float $id:(funName' "sqrt32")(float x) {
      return sqrt(x);
    }

    static inline float $id:(funName' "exp32")(float x) {
      return exp(x);
    }

    static inline float $id:(funName' "cos32")(float x) {
      return cos(x);
    }

    static inline float $id:(funName' "sin32")(float x) {
      return sin(x);
    }

    static inline float $id:(funName' "tan32")(float x) {
      return tan(x);
    }

    static inline float $id:(funName' "acos32")(float x) {
      return acos(x);
    }

    static inline float $id:(funName' "asin32")(float x) {
      return asin(x);
    }

    static inline float $id:(funName' "atan32")(float x) {
      return atan(x);
    }

    static inline float $id:(funName' "cosh32")(float x) {
      return cosh(x);
    }

    static inline float $id:(funName' "sinh32")(float x) {
      return sinh(x);
    }

    static inline float $id:(funName' "tanh32")(float x) {
      return tanh(x);
    }

    static inline float $id:(funName' "acosh32")(float x) {
      return acosh(x);
    }

    static inline float $id:(funName' "asinh32")(float x) {
      return asinh(x);
    }

    static inline float $id:(funName' "atanh32")(float x) {
      return atanh(x);
    }

    static inline float $id:(funName' "atan2_32")(float x, float y) {
      return atan2(x,y);
    }

    static inline float $id:(funName' "hypot32")(float x, float y) {
      return hypot(x,y);
    }

    static inline float $id:(funName' "gamma32")(float x) {
      return tgamma(x);
    }

    static inline float $id:(funName' "lgamma32")(float x) {
      return lgamma(x);
    }

    static inline float fmod32(float x, float y) {
      return fmod(x, y);
    }
    static inline float $id:(funName' "round32")(float x) {
      return rint(x);
    }
    static inline float $id:(funName' "floor32")(float x) {
      return floor(x);
    }
    static inline float $id:(funName' "ceil32")(float x) {
      return ceil(x);
    }
    static inline float $id:(funName' "lerp32")(float v0, float v1, float t) {
      return mix(v0, v1, t);
    }
    static inline float $id:(funName' "mad32")(float a, float b, float c) {
      return mad(a,b,c);
    }
    static inline float $id:(funName' "fma32")(float a, float b, float c) {
      return fma(a,b,c);
    }
$esc:("#else")
    static inline float $id:(funName' "log32")(float x) {
      return logf(x);
    }

    static inline float $id:(funName' "log2_32")(float x) {
      return log2f(x);
    }

    static inline float $id:(funName' "log10_32")(float x) {
      return log10f(x);
    }

    static inline float $id:(funName' "sqrt32")(float x) {
      return sqrtf(x);
    }

    static inline float $id:(funName' "exp32")(float x) {
      return expf(x);
    }

    static inline float $id:(funName' "cos32")(float x) {
      return cosf(x);
    }

    static inline float $id:(funName' "sin32")(float x) {
      return sinf(x);
    }

    static inline float $id:(funName' "tan32")(float x) {
      return tanf(x);
    }

    static inline float $id:(funName' "acos32")(float x) {
      return acosf(x);
    }

    static inline float $id:(funName' "asin32")(float x) {
      return asinf(x);
    }

    static inline float $id:(funName' "atan32")(float x) {
      return atanf(x);
    }

    static inline float $id:(funName' "cosh32")(float x) {
      return coshf(x);
    }

    static inline float $id:(funName' "sinh32")(float x) {
      return sinhf(x);
    }

    static inline float $id:(funName' "tanh32")(float x) {
      return tanhf(x);
    }

    static inline float $id:(funName' "acosh32")(float x) {
      return acoshf(x);
    }

    static inline float $id:(funName' "asinh32")(float x) {
      return asinhf(x);
    }

    static inline float $id:(funName' "atanh32")(float x) {
      return atanhf(x);
    }

    static inline float $id:(funName' "atan2_32")(float x, float y) {
      return atan2f(x,y);
    }

    static inline float $id:(funName' "hypot32")(float x, float y) {
      return hypotf(x,y);
    }

    static inline float $id:(funName' "gamma32")(float x) {
      return tgammaf(x);
    }

    static inline float $id:(funName' "lgamma32")(float x) {
      return lgammaf(x);
    }

    static inline float fmod32(float x, float y) {
      return fmodf(x, y);
    }
    static inline float $id:(funName' "round32")(float x) {
      return rintf(x);
    }
    static inline float $id:(funName' "floor32")(float x) {
      return floorf(x);
    }
    static inline float $id:(funName' "ceil32")(float x) {
      return ceilf(x);
    }
    static inline float $id:(funName' "lerp32")(float v0, float v1, float t) {
      return v0 + (v1-v0)*t;
    }
    static inline float $id:(funName' "mad32")(float a, float b, float c) {
      return a*b+c;
    }
    static inline float $id:(funName' "fma32")(float a, float b, float c) {
      return fmaf(a,b,c);
    }
$esc:("#endif")
    static inline typename int32_t $id:(funName' "to_bits32")(float x) {
      union {
        float f;
        typename int32_t t;
      } p;
      p.f = x;
      return p.t;
    }

    static inline float $id:(funName' "from_bits32")(typename int32_t x) {
      union {
        typename int32_t f;
        float t;
      } p;
      p.f = x;
      return p.t;
    }

    static inline float fsignum32(float x) {
      return $id:(funName' "isnan32")(x) ? x : ((x > 0) - (x < 0));
    }
|]

cFloat64Funs :: [C.Definition]
cFloat64Funs =
  [C.cunit|
    static inline double $id:(funName' "log64")(double x) {
      return log(x);
    }

    static inline double $id:(funName' "log2_64")(double x) {
      return log2(x);
    }

    static inline double $id:(funName' "log10_64")(double x) {
      return log10(x);
    }

    static inline double $id:(funName' "sqrt64")(double x) {
      return sqrt(x);
    }

    static inline double $id:(funName' "exp64")(double x) {
      return exp(x);
    }

    static inline double $id:(funName' "cos64")(double x) {
      return cos(x);
    }

    static inline double $id:(funName' "sin64")(double x) {
      return sin(x);
    }

    static inline double $id:(funName' "tan64")(double x) {
      return tan(x);
    }

    static inline double $id:(funName' "acos64")(double x) {
      return acos(x);
    }

    static inline double $id:(funName' "asin64")(double x) {
      return asin(x);
    }

    static inline double $id:(funName' "atan64")(double x) {
      return atan(x);
    }

    static inline double $id:(funName' "cosh64")(double x) {
      return cosh(x);
    }

    static inline double $id:(funName' "sinh64")(double x) {
      return sinh(x);
    }

    static inline double $id:(funName' "tanh64")(double x) {
      return tanh(x);
    }

    static inline double $id:(funName' "acosh64")(double x) {
      return acosh(x);
    }

    static inline double $id:(funName' "asinh64")(double x) {
      return asinh(x);
    }

    static inline double $id:(funName' "atanh64")(double x) {
      return atanh(x);
    }

    static inline double $id:(funName' "atan2_64")(double x, double y) {
      return atan2(x,y);
    }

    static inline double $id:(funName' "hypot64")(double x, double y) {
      return hypot(x,y);
    }

    static inline double $id:(funName' "gamma64")(double x) {
      return tgamma(x);
    }

    static inline double $id:(funName' "lgamma64")(double x) {
      return lgamma(x);
    }

    static inline double $id:(funName' "fma64")(double a, double b, double c) {
      return fma(a,b,c);
    }

    static inline double $id:(funName' "round64")(double x) {
      return rint(x);
    }

    static inline double $id:(funName' "ceil64")(double x) {
      return ceil(x);
    }

    static inline double $id:(funName' "floor64")(double x) {
      return floor(x);
    }

    static inline typename bool $id:(funName' "isnan64")(double x) {
      return isnan(x);
    }

    static inline typename bool $id:(funName' "isinf64")(double x) {
      return isinf(x);
    }

    static inline typename int64_t $id:(funName' "to_bits64")(double x) {
      union {
        double f;
        typename int64_t t;
      } p;
      p.f = x;
      return p.t;
    }

    static inline double $id:(funName' "from_bits64")(typename int64_t x) {
      union {
        typename int64_t f;
        double t;
      } p;
      p.f = x;
      return p.t;
    }

    static inline double fmod64(double x, double y) {
      return fmod(x, y);
    }

    static inline double fsignum64(double x) {
      return $id:(funName' "isnan64")(x) ? x : ((x > 0) - (x < 0));
    }

$esc:("#ifdef __OPENCL_VERSION__")
    static inline double $id:(funName' "lerp64")(double v0, double v1, double t) {
      return mix(v0, v1, t);
    }
    static inline double $id:(funName' "mad64")(double a, double b, double c) {
      return mad(a,b,c);
    }
$esc:("#else")
    static inline double $id:(funName' "lerp64")(double v0, double v1, double t) {
      return v0 + (v1-v0)*t;
    }
    static inline double $id:(funName' "mad64")(double a, double b, double c) {
      return a*b+c;
    }
$esc:("#endif")
|]

storageSize :: PrimType -> Int -> C.Exp -> C.Exp
storageSize pt rank shape =
  [C.cexp|$int:header_size +
          $int:rank * sizeof(typename int64_t) +
          $exp:(cproduct dims) * $int:pt_size|]
  where
    header_size, pt_size :: Int
    header_size = 1 + 1 + 1 + 4 -- 'b' <version> <num_dims> <type>
    pt_size = primByteSize pt
    dims = [[C.cexp|$exp:shape[$int:i]|] | i <- [0 .. rank -1]]

typeStr :: Signedness -> PrimType -> String
typeStr sign pt =
  case (sign, pt) of
    (_, Bool) -> "bool"
    (_, Unit) -> "bool"
    (_, FloatType Float32) -> " f32"
    (_, FloatType Float64) -> " f64"
    (TypeDirect, IntType Int8) -> "  i8"
    (TypeDirect, IntType Int16) -> " i16"
    (TypeDirect, IntType Int32) -> " i32"
    (TypeDirect, IntType Int64) -> " i64"
    (TypeUnsigned, IntType Int8) -> "  u8"
    (TypeUnsigned, IntType Int16) -> " u16"
    (TypeUnsigned, IntType Int32) -> " u32"
    (TypeUnsigned, IntType Int64) -> " u64"

storeValueHeader :: Signedness -> PrimType -> Int -> C.Exp -> C.Exp -> [C.Stm]
storeValueHeader sign pt rank shape dest =
  [C.cstms|
          *$exp:dest++ = 'b';
          *$exp:dest++ = 2;
          *$exp:dest++ = $int:rank;
          memcpy($exp:dest, $string:(typeStr sign pt), 4);
          $exp:dest += 4;
          $stms:copy_shape
          |]
  where
    copy_shape
      | rank == 0 = []
      | otherwise =
        [C.cstms|
                memcpy($exp:dest, $exp:shape, $int:rank*sizeof(typename int64_t));
                $exp:dest += $int:rank*sizeof(typename int64_t);|]

loadValueHeader :: Signedness -> PrimType -> Int -> C.Exp -> C.Exp -> [C.Stm]
loadValueHeader sign pt rank shape src =
  [C.cstms|
     err |= (*$exp:src++ != 'b');
     err |= (*$exp:src++ != 2);
     err |= (*$exp:src++ != $exp:rank);
     err |= (memcmp($exp:src, $string:(typeStr sign pt), 4) != 0);
     $exp:src += 4;
     if (err == 0) {
       $stms:load_shape
       $exp:src += $int:rank*sizeof(typename int64_t);
     }|]
  where
    load_shape
      | rank == 0 = []
      | otherwise = [C.cstms|memcpy($exp:shape, src, $int:rank*sizeof(typename int64_t));|]
