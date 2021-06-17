-- ==
-- entry: rev fwd
-- compiled input { [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 5.0] }
-- output { [0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0] }

entry rev [n] (xs: [n]f64) =
  vjp f64.maximum xs 1

entry fwd [n] (xs: [n]f64) =
  tabulate n (\i -> jvp f64.maximum xs (tabulate n ((==i) >-> f64.bool)))