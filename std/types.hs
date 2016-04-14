// Definition of standard types separate from the prelude to allow primitives to use them
/// `Option` represents a value which may not exist.
type Option a = | None | Some a
/// `Result` represents either success (`Ok`) or an error (`Err`)
type Result e t = | Err e | Ok t
/// `Ordering` represents the result of comparing two values
type Ordering = | LT | EQ | GT
in { Option, Result, Ordering }
