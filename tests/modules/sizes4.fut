type state_sized [n] = {arr: [n]i32}

module m : {
  type~ state
  val step : bool -> state -> state
} = {
  type~ state = ?[n].state_sized [n]
  let step b (s: state) = s with arr = [1,2,3]
}
