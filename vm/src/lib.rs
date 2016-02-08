//! Crate which contain the virtual machine which executes embed_lang programs

#[macro_use]
extern crate log;
#[cfg(test)]
extern crate env_logger;
#[macro_use]
extern crate quick_error;

extern crate base;
#[cfg(feature = "parser")]
extern crate parser;
#[cfg(feature = "check")]
extern crate check;

#[macro_use]
pub mod api;
pub mod compiler;
pub mod types;
pub mod vm;
pub mod interner;
pub mod gc;
pub mod stack;
mod primitives;
mod lazy;
#[cfg(all(feature = "check", feature = "parser"))]
pub mod import;
mod array;
