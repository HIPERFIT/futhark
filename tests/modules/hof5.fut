-- We require that some type is non-functional, but that type refers
-- to a lifted abstract type!
-- ==
-- error: non-functional

module m = \(p: {type ^a}) -> ({ type t = p.a } : { type t })
