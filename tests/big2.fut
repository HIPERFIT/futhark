-- ==
-- tags { no_gtx780 }
-- no_python no_wasm compiled input {2147483748i64} output { 0i8 -5i8 86i8 }

-- To avoid enormous output, we just sample the result.
let main n =
  let res = scan (+) 0 (map i8.i64 (iota n))
  in (res[0], res[n/2], res[n-1])
