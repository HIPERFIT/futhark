-- Some tests to try out very large/sparse histograms.
-- ==
-- tags { no_python no_wasm }
-- compiled input { 10000000i64     1000i64 } output { 499500i32 }
-- compiled input { 100000000i64   10000i64 } output { 49995000i32 }
-- compiled input { 100000000i64 1000000i64 } output { 1783293664i32 }

let main (n: i64) (m: i64) =
  reduce_by_index (replicate n 0) (+) 0 (map (%n) (iota m)) (map i32.i64 (iota m))
  |> i32.sum
