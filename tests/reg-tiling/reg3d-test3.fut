-- Test register tiling when all input arrays are invariant to one parallel dimension.
-- This is a more complex code, in which the code after the stream has both variant
-- and invariant parts, and double return.
--
-- ==
-- input {
--   [ [1.0f32, 3.0f32], [2.0f32, 4.0f32] ]
--   [ [5.0f32, 8.0f32], [6.0f32, 7.0f32] ]
--   [ [1.0f32, 1.0f32], [9.0f32, 1.0f32] ]
-- }
-- output { 
--   [[[18.0f32, 18.0f32], [26.0f32, 30.0f32]], [[-3.0f32, 10.0f32], [ 0.0f32, 14.0f32]]]
--   [[[28.0f32, 40.0f32], [42.0f32, 58.0f32]], [[39.0f32, 32.0f32], [48.0f32, 42.0f32]]]
-- }
--
-- no_python no_wasm compiled random input { [16][512]f32 [512][16]f32 [65536][512]f32 } auto output

let pred (x : f32) : bool = x < 9.0

let dotprod_filt [n] (vct: [n]f32) (xs: [n]f32) (ys: [n]f32) (k : i64) : (f32,f32) =
--  let s = f32.sum (map3 (\v x y -> let z = x*y in let f = f32.bool (pred v) in z*f) vct xs ys)
  let s = f32.sum (map3 (\y x v -> let z = x*y in let f = f32.bool (pred v) in z*f) ys xs vct)
  let var_term = 2.0 * #[unsafe] vct[k]
  let inv_term = 3.0 * #[unsafe] xs[k]
  let term = var_term + inv_term
  in (s - term, s + term)

let matmul_filt [n][p][m] (xss: [n][p]f32) (yss: [p][m]f32) (vct: [p]f32) : [n][m](f32,f32) =
  map (\xs -> map2 (dotprod_filt vct xs) (transpose yss) (iota m)) xss

let main [m][n][u]  (ass: [n][u]f32) 
                    (bss: [u][n]f32) 
                    (fss: [m][u]f32)
                    : ([m][n][n]f32,[m][n][n]f32) =
    map (matmul_filt ass bss) fss |> map (map unzip) |> map unzip |> unzip
