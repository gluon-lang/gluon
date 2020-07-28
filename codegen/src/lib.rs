//! Various macros for integrating with the `gluon` vm.
//!
//! ## Derive Macros
//!
//! Custom derives for the following `gluon`-Traits are available:
//!
//! ### Getable
//!
//! Derives `Getable` for any enum or struct as long as all fields also implement
//! `Getable` (generic type parameters included). If the type is generic over a
//! lifetime, the lifetime will be constrained to that of the `'vm` lifetime in the
//! trait definition.
//!
//! __Note:__ Newtype structs are expected to be their inner type on the Gluon side.
//!
//! #### Examples
//!
//! Marhalling this gluon type:
//!
//! ```gluon
//! type Comment =
//!     | Normal String
//!     | Multiline String
//!     | Doc String
//! ```
//!
//! To this rust enum:
//!
//! ```rust
//! #[macro_use]
//! extern crate gluon_codegen;
//! extern crate gluon;
//!
//! enum Comment {
//!     Normal(String),
//!     Multiline(String),
//!     Doc(String),
//! }
//! # fn main() {}
//! ```
//!
//! ### Pushable
//!
//! Derives `Pushable` for any enum or struct as long as all fields also implement
//! `Pushable` (generic type parameters included).
//!
//! __Note:__ Newtype structs are pushed as their inner type.
//!
//! #### Examples
//!
//! Allowing the `User` struct to be marshalled to gluon code:
//!
//! ```rust
//! #[macro_use]
//! extern crate gluon_codegen;
//! extern crate gluon;
//!
//! #[derive(Pushable)]
//! struct User {
//!     name: String,
//!     age: u32,
//! }
//! # fn main() {}
//! ```
//!
//! As this compatible Record:
//!
//! ```gluon
//! type User = { name: String, age: Int }
//! ```
//!
//! ### VmType
//!
//! Derives `VmType` for a rust type, mapping it to a gluon type.
//!
//! Alternatively, you can specify the corresponding gluon type with the
//! `#[gluon(vm_type = "<gluon_type>")]` attribute, where the gluon type is the fully qualified type name.
//! The gluon type must be registered before a binding using the mapped rust type is first loaded.
//!
//! If the rust type has type parameters, they have to implement `VmType` as well.
//! All lifetimes have to be `'static`.
//!
//! __Note:__ Newtype structs are mapped to their inner type.
//!
//! #### Examples
//!
//! Deriving `VmType` for a struct:
//!
//! ```rust
//! #[macro_use]
//! extern crate gluon_codegen;
//! extern crate gluon;
//!
//! // will map to: `{ string: String, number: Int, vec: Array Float }`
//! #[derive(VmType)]
//! struct Struct {
//!     string: String,
//!     number: u32,
//!     vec: Vec<f64>,
//! }
//! # fn main() {}
//! ```
//!
//! Mapping to an existing type, assuming the following gluon type in the module `types`:
//!
//! ```gluon
//! type Either l r = | Left l | Right r
//! ```
//!
//! Requires the additional `vm_type` attribute:
//!
//! ```rust
//! #[macro_use]
//! extern crate gluon_codegen;
//! extern crate gluon;
//!
//! #[derive(VmType)]
//! #[gluon(vm_type = "types.Either")]
//! enum Either<L, R> {
//!     Left(L),
//!     Right(R),
//! }
//! # fn main() {}
//! ```
//!
//! ### Userdata
//!
//! Derives `Userdata` and the required `Trace` and `VmType` for a rust type.
//! Note that you will still have to use `Thread::register_type` to register the
//! rust type with the vm before it is used.
//!
//! #### Examples
//!
//! Deriving `Userdata` for a type that will be opaque for the gluon code:
//!
//! ```rust
//! #[macro_use]
//! extern crate gluon_codegen;
//! extern crate gluon;
//!
//! use std::sync::Arc;
//!
//! // Userdata requires Trace + Debug + Send + Sync
//! #[derive(Userdata, Trace, Debug)]
//! struct Ident {
//!     group: Arc<str>,
//!     name: Arc<str>,
//! }
//! # fn main() {}
//! ```
//!

#![recursion_limit = "128"]

#[macro_use]
extern crate quote;

mod ast_clone;
mod attr;
mod functor;
mod getable;
mod pushable;
mod shared;
mod trace;
mod userdata;
mod vm_type;

#[doc(hidden)]
#[proc_macro_derive(Getable, attributes(gluon))]
pub fn getable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    getable::derive(input.into()).into()
}

#[doc(hidden)]
#[proc_macro_derive(Pushable, attributes(gluon))]
pub fn pushable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    pushable::derive(input.into()).into()
}

#[doc(hidden)]
#[proc_macro_derive(Userdata, attributes(gluon))]
pub fn userdata(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    userdata::derive(input.into()).into()
}

#[doc(hidden)]
#[proc_macro_derive(VmType, attributes(gluon))]
pub fn vm_type(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    vm_type::derive(input.into()).into()
}

#[doc(hidden)]
#[proc_macro_derive(Trace, attributes(gluon, gluon_trace, gluon_userdata))]
pub fn trace(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    trace::derive(input.into()).into()
}

#[doc(hidden)]
#[proc_macro_derive(Functor, attributes(functor))]
pub fn functor(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    functor::derive(input.into()).into()
}

#[doc(hidden)]
#[proc_macro_derive(AstClone, attributes(gluon))]
pub fn ast_clone(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    ast_clone::derive(input.into()).into()
}
