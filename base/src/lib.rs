//! The base crate contains pervasive types used in the compiler such as type representations, the
//! AST and some basic containers.

#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;
extern crate pretty;

pub mod ast;
pub mod error;
pub mod fixed;
pub mod fnv;
pub mod instantiate;
pub mod metadata;
pub mod pos;
pub mod scoped_map;
pub mod source;
pub mod symbol;
pub mod types;
