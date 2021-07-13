-- ==
-- tags { no_python no_wasm }
-- input { 100i64 1000i64 } output { 870104 }
-- compiled input { 400i64 1000i64} output { 985824 }
-- compiled input { 100000i64 100i64} output { 15799424 }
--
let main (n: i64) (m: i64): i32 =
  let a = map (\i  ->
                 map i32.i64 (map (+i) (iota(m))))
              (iota(n))
  let b = map  (\(a_r: [m]i32): [m]i32  ->
                 scan (+) 0 (a_r)) a in
  reduce (^) 0 (flatten b)
