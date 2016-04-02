// Definition of standard types separate from the prelude to allow primitives to use them
type Option a = | None | Some a
type Result e t = | Err e | Ok t
type Ordering = | LT | EQ | GT
in { Option, Result, Ordering }
