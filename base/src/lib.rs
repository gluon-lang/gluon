#![feature(alloc, core, slice_patterns)]
#[macro_use]
extern crate log;

pub mod ast;
pub mod gc;
pub mod interner;
