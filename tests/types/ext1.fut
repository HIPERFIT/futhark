-- ==
-- input { 1i64 }
-- output { [true, true] [false, false] }

type^ t = ?[n].([n]bool, bool -> [n]bool)

let v x : t =
  let x' = x + 1
  in (replicate x' true,
      \b -> replicate x' b)

let main x =
  let (arr, f) = v x
  in unzip (zip arr (f false))
