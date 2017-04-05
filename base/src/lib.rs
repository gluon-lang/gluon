//! The base crate contains pervasive types used in the compiler such as type representations, the
//! AST and some basic containers.

extern crate log;
#[macro_use]
extern crate quick_error;
extern crate pretty;
extern crate smallvec;
#[macro_use]
extern crate collect_mac;

pub mod ast;
pub mod error;
pub mod fixed;
pub mod fnv;
pub mod kind;
pub mod merge;
pub mod metadata;
pub mod pos;
pub mod resolve;
pub mod scoped_map;
pub mod source;
pub mod symbol;
pub mod types;
