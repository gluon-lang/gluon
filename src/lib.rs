#![crate_type="lib"]
//! # Example
//!
//! ```rust
//! # extern crate env_logger;
//! # extern crate embed_lang;
//! 
//! use embed_lang::vm::vm::{VM, run_expr};
//! 
//! # fn main() {
//!
//! let text = r#"
//! // `type` is used to declare a new type.
//! // In this case we declare `Eq` to be a record with a single field (`==`) which is a function
//! // which takes two arguments of the same type and returns a boolean
//! type Eq a = { (==) : a -> a -> Bool }
//! in
//! // `let` declares new variables.
//! let id x = x
//! and factorial n =
//!         if n < 2
//!         then 1
//!         else n * factorial (n - 1)
//! in
//! let list_module =
//!         // Declare a new type which only exists in the current scope
//!         type List a = | Cons a (List a) | Nil
//!         in
//!         let map f xs =
//!                 case xs of
//!                     | Cons y ys -> Cons (f y) (map f ys)
//!                     | Nil -> Nil
//!         in
//!         let eq eq_a: Eq a -> Eq (List a) =
//!                 let { (==) } = eq_a in
//!                 let (===) l r =
//!                         case l of
//!                             | Cons la lxs ->
//!                                 (case r of
//!                                     | Cons ra rxs -> la == ra && lxs === rxs
//!                                     | Nil -> False)
//!                             | Nil ->
//!                                 (case r of
//!                                     | Cons _ _ -> False
//!                                     | Nil -> True)
//!                 in { (==) = (===) }
//!         in {
//!             // Since `List` is local we export it so its constructors can be used
//!             // outside the current scope
//!             List,
//!             eq,
//!             map
//!         }
//! in
//! // Bring the `List` type and its constructors into scope
//! let { List, eq = list_Eq } = list_module
//! in
//! // Create `==` for `List Int`
//! let { (==) }: Eq (List Int) = list_Eq { (==) }
//! in
//! if Cons 1 Nil == Nil then
//!     error "This branch is not executed"
//! else
//!     io.print "Hello world!"
//! "#;
//! # let _ = ::env_logger::init();
//! let vm = VM::new();
//! if let Err(err) = run_expr(&vm, "example", text) {
//!     panic!("{}", err);
//! }
//!
//! # }
//! ```

#[macro_use]
extern crate log;
extern crate env_logger;

mod crates {
    extern crate base;
    extern crate parser;
    extern crate check;
    extern crate vm;
}

pub use crates::base;
pub use crates::parser;
pub use crates::check;
pub use crates::vm;
