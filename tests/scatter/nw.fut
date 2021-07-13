-- Stripped version of nw from futhark-benchmarks
-- ==
-- no_wasm compiled input @ data/tiny.in
-- output @ data/tiny.out

let B0: i64 = 64

let fInd (B: i64) (y:i32) (x:i32): i32 = y*(i32.i64 B+1) + x
let max3 (x:i32, y:i32, z:i32) = if x < y
                                 then if y < z then z else y
                                 else if x < z then z else x
let mkVal [l2][l] (y:i32) (x:i32) (pen:i32) (inp_l:[l2][l2]i32) (ref_l:[l][l]i32) : i32 = #[unsafe]
  max3( ( (inp_l[y - 1, x - 1])) + ( ref_l[y-1, x-1])
      , ( (inp_l[y, x - 1])) - pen
      , ( (inp_l[y - 1, x])) - pen
      )

let intraBlockPar [lensq][len] (B: i64)
                               (penalty: i32)
                               (inputsets: [lensq]i32)
                               (reference2: [len][len]i32)
                               (b_y: i64) (b_x: i64)
                               : [B][B]i32 =
  let ref_l = reference2[b_y * B + 1: b_y * B + 1 + B,
                         b_x * B + 1: b_x * B + 1 + B] :> [B][B]i32

  let inputsets' = unflatten len len inputsets

  let Bp1 = B + 1

  -- Initialize inp_l with the already processed the column to the left of this
  -- block
  let inp_l = copy(inputsets'[b_y * B : b_y * B + B + 1, b_x * B : b_x * B + B + 1]) :> *[Bp1][Bp1]i32

  -- Process the first half (anti-diagonally) of the block
  let inp_l = loop inp_l for m < B do
        let (inds, vals) = unzip (
            -- tabulate over the m'th anti-diagonal before the middle
            tabulate B (\tx ->  (
                    if tx > m then ((-1, -1), 0)
                    else let ind_x = i32.i64 (tx + 1)
                         let ind_y = i32.i64 (m - tx + 1)
                         let v = mkVal ind_y ind_x penalty inp_l ref_l
                         in  ((i64.i32 ind_y, i64.i32 ind_x), v))))
        in  scatter_2d inp_l inds vals

  in  inp_l[1:B+1,1:B+1] :> [B][B]i32


let updateBlocks [q][lensq] (B: i64)
                            (len: i32) (blk: i64)
                            (mk_b_y: (i32 -> i32))
                            (mk_b_x: (i32 -> i32))
                            (block_inp: [q][B][B]i32)
                            (inputsets:  *[lensq]i32) =
  let (inds, vals) = unzip (
    tabulate (blk*B*B) (\gid ->
                 let B2 = i32.i64 (B*B)
                 let gid = i32.i64 gid
                 let (bx, lid2) = (gid / B2, gid % B2)
                 let (ty, tx)   = (lid2 / i32.i64 B, lid2 % i32.i64 B)

                 let b_y = mk_b_y bx
                 let b_x = mk_b_x bx
                 let v = #[unsafe] block_inp[bx, ty, tx]
                 let ind = (i32.i64 B*b_y + 1 + ty) * len + (i32.i64 B*b_x + tx + 1)
                 in  (i64.i32 ind, v)))
  in  scatter inputsets inds vals


let main [lensq] (penalty : i32)
                 (inputsets : *[lensq]i32)
                 (reference : *[lensq]i32) : *[lensq]i32 =
  let len = i32.f32 (f32.sqrt (f32.i64 lensq))
  let worksize = len - 1
  let B = i64.min (i64.i32 worksize) B0

  -- worksize should be a multiple of B0
  let B = assert (i64.i32 worksize % B == 0) B

  let block_width = trace <| worksize / i32.i64 B
  let reference2 = unflatten (i64.i32 len) (i64.i32 len) reference

  -- First anti-diagonal half of the entire input matrix
  let inputsets =
    loop inputsets for blk < block_width do
        let blk = i64.i32 (blk + 1)
        let block_inp =
          -- Process an anti-diagonal of independent blocks
          tabulate blk (\b_x ->
                let b_y = blk-1-b_x
                in  intraBlockPar B penalty inputsets reference2 b_y b_x
          )

        let mkBY bx = i32.i64 (blk - 1) - bx
        let mkBX bx = bx
        in  updateBlocks B len blk mkBY mkBX block_inp inputsets

  in  inputsets
