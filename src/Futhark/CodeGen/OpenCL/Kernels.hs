{-# LANGUAGE QuasiQuotes #-}
module Futhark.CodeGen.OpenCL.Kernels
       ( mapTranspose
       , Reduction (..)
       , reduce
       )
       where

import qualified Language.C.Syntax as C
import qualified Language.C.Quote.OpenCL as C

mapTranspose :: C.ToIdent a => a -> C.Type -> C.Func
mapTranspose kernel_name elem_type =
  [C.cfun|
  // This kernel is optimized to ensure all global reads and writes are coalesced,
  // and to avoid bank conflicts in shared memory.  The shared memory array is sized
  // to (BLOCK_DIM+1)*BLOCK_DIM.  This pads each row of the 2D block in shared memory
  // so that bank conflicts do not occur when threads address the array column-wise.
  __kernel void $id:kernel_name(__global $ty:elem_type *odata,
                                uint odata_offset,
                                __global $ty:elem_type *idata,
                                uint idata_offset,
                                uint width,
                                uint height,
                                __local $ty:elem_type* block) {
    uint x_index;
    uint y_index;
    uint our_array_offset;

    // Adjust the input and output arrays with the basic offset.
    odata += odata_offset;
    idata += idata_offset;

    // Adjust the input and output arrays for the third dimension.
    our_array_offset = get_global_id(2) * width * height;
    odata += our_array_offset;
    idata += our_array_offset;

    // read the matrix tile into shared memory
    x_index = get_global_id(0);
    y_index = get_global_id(1);

    if((x_index < width) && (y_index < height))
    {
        uint index_in = y_index * width + x_index;
        block[get_local_id(1)*(FUT_BLOCK_DIM+1)+get_local_id(0)] = idata[index_in];
    }

    barrier(CLK_LOCAL_MEM_FENCE);

    // Write the transposed matrix tile to global memory.
    x_index = get_group_id(1) * FUT_BLOCK_DIM + get_local_id(0);
    y_index = get_group_id(0) * FUT_BLOCK_DIM + get_local_id(1);
    if((x_index < height) && (y_index < width))
    {
        uint index_out = y_index * height + x_index;
        odata[index_out] = block[get_local_id(0)*(FUT_BLOCK_DIM+1)+get_local_id(1)];
    }
  }|]

data Reduction = Reduction {
    reductionKernelName :: String
  , reductionInputArrayIndexName :: String
  , reductionOffsetName :: String
  , reductionKernelArgs :: [C.Param]
  , reductionPrologue :: [C.BlockItem]
  , reductionFoldOperation :: [C.BlockItem]
  , reductionWriteFoldResult :: [C.BlockItem]
  , reductionReduceOperation :: [C.BlockItem]
  , reductionWriteFinalResult :: [C.BlockItem]
  }

reduce :: Reduction -> C.Func
reduce red =
  [C.cfun|
   __kernel void $id:(reductionKernelName red)($params:(reductionKernelArgs red))
   {
     $items:(reductionPrologue red)

     $items:(reductionFoldOperation red)

     uint lid = get_local_id(0);
     $items:(reductionWriteFoldResult red)

     /* in-wave reductions */
     uint wave_num = lid / WAVE_SIZE;
     uint wid = lid - (wave_num * WAVE_SIZE);
     for (uint $id:offset = 1; $id:offset < WAVE_SIZE; $id:offset *= 2) {
       /* in-wave reductions don't need a barrier */
       if ((wid & (2 * $id:offset - 1)) == 0) {
         $items:(reductionReduceOperation red)
         $items:(reductionWriteFoldResult red)
       }
     }
     /* cross-wave reductions */
     uint num_waves = (get_local_size(0) + WAVE_SIZE - 1)/WAVE_SIZE;
     for (uint skip_waves = 1; skip_waves < num_waves; skip_waves *=2) {
       barrier(CLK_LOCAL_MEM_FENCE);
       uint $id:offset = skip_waves * WAVE_SIZE;
       if (wid == 0 && (wave_num & (2*skip_waves - 1)) == 0) {
         $items:(reductionReduceOperation red)
         $items:(reductionWriteFoldResult red)
       }
     }

     if (lid == 0) {
       $items:(reductionWriteFinalResult red)
     }
   }
  |]
  where offset = reductionOffsetName red
