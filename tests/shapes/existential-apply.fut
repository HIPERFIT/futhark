-- An existential size in an apply function returning a lifted type is fine.
-- ==
-- input { 2i64 } output { [0i64,1i64] }

let apply 'a '^b (f: a -> b) (x: a): b =
  f x

let main (n: i64) = apply iota n
