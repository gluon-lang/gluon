//! The base crate contains pervasive types used in the compiler such as type representations, the
//! AST and some basic containers.

#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;

pub mod ast;
pub mod fixed;
pub mod symbol;
pub mod error;
pub mod types;
pub mod scoped_map;
pub mod metadata;
pub mod instantiate;
