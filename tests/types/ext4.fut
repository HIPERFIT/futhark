-- ==
-- input { [true] [2] }
-- output { 1i64 }

let main [n] (xs: ?[n].[n]bool) (ys: [n]i32) = length (zip xs ys)
