{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

module Futhark.CodeGen.Backends.GenericWASM
  ( 
    runServer,
    GC.CParts (..),
    GC.asLibrary,
    GC.asExecutable,
    GC.asServer,
    JSEntryPoint (..),
    emccExportNames,
    javascriptWrapper,
    extToString
  )
where

import Data.FileEmbed
import Data.List (intercalate, nub)
import qualified Data.Text as T
import qualified Futhark.CodeGen.Backends.GenericC as GC
import Futhark.CodeGen.Backends.SequentialC.Boilerplate
import qualified Futhark.CodeGen.ImpCode.Sequential as Imp
import qualified Futhark.CodeGen.ImpGen.Sequential as ImpGen
import Futhark.IR.Primitive
import Futhark.IR.SeqMem
import Futhark.MonadFreshNames
import NeatInterpolation (text)

extToString :: Imp.ExternalValue -> String
extToString (Imp.TransparentValue (Imp.ArrayValue vn _ pt s dimSize)) = concat (replicate (length dimSize) "[]") ++ extToString (Imp.TransparentValue (Imp.ScalarValue pt s vn))
extToString (Imp.TransparentValue (Imp.ScalarValue (FloatType Float32) _ _)) = "f32"
extToString (Imp.TransparentValue (Imp.ScalarValue (FloatType Float64) _ _)) = "f64"
extToString (Imp.TransparentValue (Imp.ScalarValue (IntType Int8) Imp.TypeDirect _)) = "i8"
extToString (Imp.TransparentValue (Imp.ScalarValue (IntType Int16) Imp.TypeDirect _)) = "i16"
extToString (Imp.TransparentValue (Imp.ScalarValue (IntType Int32) Imp.TypeDirect _)) = "i32"
extToString (Imp.TransparentValue (Imp.ScalarValue (IntType Int64) Imp.TypeDirect _)) = "i64"
extToString (Imp.TransparentValue (Imp.ScalarValue (IntType Int8) Imp.TypeUnsigned _)) = "u8"
extToString (Imp.TransparentValue (Imp.ScalarValue (IntType Int16) Imp.TypeUnsigned _)) = "u16"
extToString (Imp.TransparentValue (Imp.ScalarValue (IntType Int32) Imp.TypeUnsigned _)) = "u32"
extToString (Imp.TransparentValue (Imp.ScalarValue (IntType Int64) Imp.TypeUnsigned _)) = "u64"
extToString (Imp.TransparentValue (Imp.ScalarValue Bool _ _)) = "bool"
extToString (Imp.OpaqueValue _ _) = "opaq"
extToString _ = "Not Reached"

-- TODO 32
-- Handle Booleans
-- Hhandle OpaqueTypes

--type EntryPointName = String
type EntryPointTyp = String

data JSEntryPoint = JSEntryPoint
  { name :: String,
    parameters :: [EntryPointTyp],
    ret :: [EntryPointTyp]
  }

jsServer :: String
jsServer = $(embedStringFile "rts/javascript/server.js")

jsValues :: String
jsValues = $(embedStringFile "rts/javascript/values.js")

initFunc :: String
initFunc =
  T.unpack
    [text|
   function initData(data) {
      var nDataBytes = data.length * data.BYTES_PER_ELEMENT;
      var dataPtr = Module._malloc(nDataBytes);
      var dataHeap = new Uint8Array(Module.HEAPU8.buffer, dataPtr, nDataBytes);
      dataHeap.set(new Uint8Array(data.buffer));
      return dataHeap
  }
  |]

-- initDataHeap :: Int -> String -> String
-- initDataHeap idx arrType = "    var dataHeap" ++ show idx ++ " = initData(new " ++ arrType ++ "(1));"

dataHeapConv :: String -> String -> String
dataHeapConv size arrType =
  "    var dataHeapRes = new " ++ arrType ++ "(dataHeap.buffer, res, " ++ size ++ ");"

javascriptWrapper :: [JSEntryPoint] -> String
javascriptWrapper entryPoints =
  unlines
    [ jsServer,
      jsValues,
      cwraps,
      cwrapsJSE entryPoints,
      unlines $ map cwrapEntryPoint entryPoints,
      initFunc,
      ptrOrScalar,
      arrWrapper,
      unlines $ concatMap (\jse -> map fromFutharkArrayShape (nub (ret jse ++ parameters jse))) entryPoints,
      unlines $ concatMap (\jse -> map fromFutharkArrayValues (nub (ret jse ++ parameters jse))) entryPoints,
      classDef,
      constructor entryPoints,
      getEntryPointsFun,
      unlines $ concatMap (\jse -> map toFutharkArray (nub (ret jse ++ parameters jse))) entryPoints,
      unlines $ map jsWrapEntryPoint entryPoints,
      endClassDef
    ]

--TODO Figure out if this needs arguements
arrWrapper :: String
arrWrapper =
  T.unpack
    [text|
    function padTyp(typ) {
      if (typ.length == 3) {
        return " " + typ;
      } else if (typ.length == 2) {
        return "  " + typ;
      } else {
        return typ;
      }
    }

    class FutharkArray {

      constructor(futctx, ptr, typ, fshape, fvalues) {
        this.futctx = futctx;
        this.ptr = ptr;
        this.typ = typ;
        this.fshape = fshape;
        this.fvalues = fvalues;
        this.shape_init = false;
        this.values_init = false;
      }

      str_type() {
        return padTyp(this.typ);
      }

      shape() {
        if (!this.shape_init) {
          this.shape_ = this.fshape(this.futctx, this.ptr);
          this.shape_init = true;
        }
        return this.shape_;
      }
 
      values() {
        if (!this.values_init) {
          this.values_ = this.fvalues(this.futctx, this.shape(), this.ptr);
          this.values_init = true;
        }
        return this.values_;
      }

      bytes_per_element() {
        return this.values().BYTES_PER_ELEMENT;
      }

      pointer() {
        return this.ptr;
      }
    }
  |]

cwraps :: String
cwraps =
  unlines
    [ cwrapFun "futhark_context_config_new" 0,
      cwrapFun "futhark_context_new" 1,
      cwrapFun "futhark_context_sync" 1,
      cwrapFun "futhark_context_get_error" 1
    ]

-- TODO Only wrap functions for first params
cwrapsJSE :: [JSEntryPoint] -> String
cwrapsJSE jses =
  unlines $
    map (\arg -> cwrapFun (gfn "new" arg) (dim arg + 2)) jses'
      ++ map (\arg -> cwrapFun (gfn "shape" arg) (dim arg + 2)) jses'
      ++ map (\arg -> cwrapFun (gfn "values_raw" arg) (dim arg + 2)) jses'
      ++ map (\arg -> cwrapFun (gfn "values" arg) 2) jses'
  where
    jses' = filter (\t -> dim t > 0) $ nub $ concatMap (\jse -> parameters jse ++ ret jse) jses
    gfn typ str = "futhark_" ++ typ ++ "_" ++ baseType str ++ "_" ++ show (dim str) ++ "d"

emccExportNames :: [JSEntryPoint] -> [String]
emccExportNames jses =
  map (\jse -> "'_futhark_entry_" ++ name jse ++ "'") jses
    ++ map (\arg -> "'" ++ gfn "new" arg ++ "'") jses'
    ++ map (\arg -> "'" ++ gfn "shape" arg ++ "'") jses'
    ++ map (\arg -> "'" ++ gfn "values_raw" arg ++ "'") jses'
    ++ map (\arg -> "'" ++ gfn "values" arg ++ "'") jses'
    ++ ["_futhark_context_config_new", "_futhark_context_new", "_futhark_context_sync", "_futhark_context_get_error"]
  where
    jses' = filter (\t -> dim t > 0) $ nub $ concatMap (\jse -> parameters jse ++ ret jse) jses
    gfn typ str = "_futhark_" ++ typ ++ "_" ++ baseType str ++ "_" ++ show (dim str) ++ "d"

cwrapFun :: String -> Int -> String
cwrapFun fname numArgs =
  T.unpack
    [text|
  ${fn} =
  Module.cwrap(
      '${fn}', 'number', [${args}],
    );
  |]
  where
    fn = T.pack fname
    args = T.pack $ intercalate ", " $ replicate numArgs "'number'"

classDef :: String
classDef = "class FutharkContext {"

endClassDef :: String
endClassDef = "}"

constructor :: [JSEntryPoint] -> String
constructor jses =
  T.unpack
    [text|
    constructor() {
      this.cfg = futhark_context_config_new();
      this.ctx = futhark_context_new(this.cfg);
      this.entry_points = {
        ${entries}
      };
    }
  |]
  where
    entries = T.pack $ intercalate "," $ map dicEntry jses

getEntryPointsFun :: String
getEntryPointsFun =
  T.unpack
    [text|
    get_entry_points() {
      return this.entry_points;
    }
  |]

dicEntry :: JSEntryPoint -> String
dicEntry jse =
  T.unpack
    [text|
  '${ename}' : [${params}, ${rets}]
  |]
  where
    ename = T.pack $ name jse
    params = T.pack $ show $ parameters jse
    rets = T.pack $ show $ ret jse

jsWrapEntryPoint :: JSEntryPoint -> String
jsWrapEntryPoint jse =
  unlines
    [ "  " ++ func_name ++ "(" ++ args1 ++ ") {",
      initss,
      paramsToPtr,
      "    if (futhark_entry_" ++ func_name ++ "(this.ctx, " ++ rets ++ ", " ++ args1 ++ ") > 0) {",
      "     var error_ptr = futhark_context_get_error(this.ctx);",
      "     var error_msg = '';",
      "     var next_char;",
      "     for (var i=0; 0 != (next_char=getValue(i + error_ptr, 'i8')); i++) {",
      "       error_msg = error_msg + String.fromCharCode(next_char);",
      "     }",
      "     throw error_msg;",
      "    }",
      results,
      "    futhark_context_sync(this.ctx);",
      "    return " ++ res ++ ";",
      "  }"
    ]
  where
    func_name = name jse
    alp = [0 .. length (parameters jse) - 1]
    args1 = intercalate ", " ["in" ++ show i | i <- alp]
    paramsToPtr = unlines ["  in" ++ show i ++ " = ptrOrScalar(in" ++ show i ++ ")" | i <- alp]

    alr = [0 .. length (ret jse) - 1]
    initss = unlines [inits i $ ret jse !! i | i  <- alr]
    results = unlines [if head (ret jse !! i) == '[' 
                       then makeFutharkArray i $ ret jse !! i
                       else resDataHeap i $ ret jse !! i | i <- alr]
    rets = intercalate ", " [retPtrOrOther i | i <- alr]
    res_array = intercalate ", " ["result" ++ show i | i <- alr]
    res = if length (ret jse) == 1 then "result0" else ("[" ++ res_array ++ "]")
    retPtrOrOther i =
      if head (ret jse !! i) == '['
      then "res" ++ show i
      else "dataHeap" ++ show i ++ ".byteOffset"

makeFutharkArray :: Int -> String -> String
makeFutharkArray i typ =
  "    var result" ++ show i ++ " = new FutharkArray(this, getValue(res" ++ show i ++ ", 'i32'), '"
    ++ baseType typ
    ++ "', " ++ fname "shape" 
    ++ ", " ++ fname "values"
    ++ ");"
    where
      fname foo = "from_futhark_" ++ foo ++ "_" ++ baseType typ  ++ "_" ++ show (dim typ) ++ "d_arr"

resDataHeap :: Int -> String -> String
resDataHeap i typ =
  "    var result" ++ show i ++ " = new " ++ typeConversion typ ++ "(dataHeap" ++ show i ++ ".buffer,"
    ++ " dataHeap"
    ++ show i
    ++ ".byteOffset, 1)[0]" ++ if typ == "bool" then "!==0;" else ";"
  

ptrOrScalar :: String
ptrOrScalar =
  T.unpack
    [text|
    function ptrOrScalar(x) {
      if (x.constructor.name == "FutharkArray") {
        return x.pointer();
      } else {
        return x;
      }
    }
  |]

cwrapEntryPoint :: JSEntryPoint -> String
cwrapEntryPoint jse =
  T.unpack
    [text|
    futhark_entry_${ename} =
      Module.cwrap(
        'futhark_entry_${ename}', 'number', ${args}
      );
   |]
  where
    ename = T.pack $ name jse
    arg_length = length (parameters jse) + length (ret jse)
    args = T.pack $ "['number'" ++ concat (replicate arg_length ", 'number'") ++ "]"

inits :: Int -> EntryPointTyp -> String
inits argNum ep =
  let (i, typ) = retType ep
   in if i == 0
        then initNotPtr argNum typ
        else makePtr argNum

initNotPtr :: Int -> String -> String
initNotPtr i typ =
  "var dataHeap" ++ show i ++ " = initData(new " ++ typeConversion typ ++ "(1));"

makePtr :: Int -> String
makePtr i = "    var res" ++ show i ++ " = Module._malloc(8);"

retType :: String -> (Integer, String)
retType ('[' : ']' : end) =
  let (val, typ) = retType end
   in (val + 1, typ)
retType typ = (0, typeConversion typ)

baseType :: String -> String
baseType ('[' : ']' : end) = baseType end
baseType typ = typ

dim :: String -> Int
dim ('[' : ']' : end) = dim end + 1
dim _ = 0

jsType :: String -> String
jsType = snd . retType

typeConversion :: String -> String
typeConversion typ =
  case typ of
    "i8" -> "Int8Array"
    "i16" -> "Int16Array"
    "i32" -> "Int32Array"
    "i64" -> "BigInt64Array"
    "u8" -> "Uint8Array"
    "u16" -> "Uint16Array"
    "u32" -> "Uint32Array"
    "u64" -> "BigUint64Array"
    "f32" -> "Float32Array"
    "f64" -> "Float64Array"
    "bool" -> "Int8Array"
    _ -> typ

toFutharkArray :: String -> String
toFutharkArray str =
  if dim str == 0
    then ""
    else
      unlines
        [ "to_futhark_" ++ ftype ++ "_" ++ show i ++ "d_arr(" ++ intercalate ", " args1 ++ ") {",
          -- "  // Possibly do sanity check that dimensions dim0 * dimn == arr.length",
          "  var dataHeap = initData(arr);",
          "  var fut_arr = futhark_new_" ++ ftype ++ "_" ++ show i ++ "d(" ++ intercalate ", " args2 ++ ");",
          "  return fut_arr;",
          "}"
        ]
  where
    ctx = "this.ctx"
    arr = "arr"
    ofs = "dataHeap.byteOffset"
    i = dim str
    dims = map (\j -> "dim" ++ show j) [0 .. i -1]
    --cast = map (\d -> "Number(" ++ d ++ ")") dims
    args1 = arr : dims
    args2 = [ctx, ofs] ++ dims
    ftype = baseType str

fromFutharkArrayShape :: String -> String
fromFutharkArrayShape str =
  if dim str == 0
    then ""
    else
      unlines
        [ "function from_futhark_shape_" ++ ftype ++ "_" ++ show i ++ "d_arr(ctx, fut_arr_ptr) {",
          "  var ptr = futhark_shape_" ++ ftype ++ "_" ++ show i ++ "d(" ++ intercalate ", " args1 ++ ");",
          "  var dataHeap = new Uint8Array(Module.HEAPU8.buffer, ptr, 8 * " ++ show i ++ ");",
          " var result = new BigUint64Array(dataHeap.buffer, dataHeap.byteOffset, " ++ show i ++ ");",
          " return result;",
          "}"
        ]
  where
    ctx = "ctx"
    arr = "fut_arr_ptr"
    args1 = [ctx, arr]
    i = dim str
    ftype = baseType str

fromFutharkArrayValues :: String -> String
fromFutharkArrayValues str =
  if dim str == 0
    then ""
    else
      unlines
        [ "function from_futhark_values_" ++ ftype ++ "_" ++ show i ++ "d_arr(ctx, dims, fut_arr_ptr) {",
          "  var length = Number(dims.reduce((a, b) => a * b));",
          "  var dataHeap = initData(new " ++ arrType ++ "(length));",
          "  var res = futhark_values_raw_" ++ ftype ++ "_" ++ show i ++ "d(" ++ intercalate ", " args2 ++ ");",
          dataHeapConv "length" arrType,
          "  return dataHeapRes;",
          "}"
        ]
  where
    ctx = "ctx"
    fut_arr = "fut_arr_ptr"
    args2 = [ctx, fut_arr]
    i = dim str
    ftype = baseType str
    arrType = jsType str

runServer :: String
runServer =
  T.unpack
    [text|
   Module.onRuntimeInitialized = () => {
     var context = new FutharkContext();
     var server = new Server(context);
     server.run();
   }
  |]