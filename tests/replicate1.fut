-- Simple test to see whether we can properly replicate arrays.  This
-- one sums the resulting array, to check very large ones.
-- ==
-- input { 20i64 } output { 3810 }
-- compiled no_python no_wasm input { 2000i64 } output { -296967286i32 }
-- structure distributed { Replicate 1 }
let main(n: i64): i32 =
  let x  = iota n
  let y  = replicate n x
  -- Hack to force manifestation.
  let y[0,0] = 10
  -- Conversion added to satisfy old test results that result from overflow
  in reduce (+) 0 (flatten y |> map i32.i64)
