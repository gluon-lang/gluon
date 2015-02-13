#![crate_type="lib"]
#![feature(unsafe_destructor, unboxed_closures, box_syntax, alloc, core, collections, hash, io, std_misc, unicode)]
extern crate collections;
#[macro_use]
extern crate log;

pub use interner::InternedStr;
pub use parser::ParseResult;
pub use typecheck::TcType;
pub use compiler::{CompiledFunction, Instruction};


mod scoped_map;
mod interner;
pub mod ast;
mod lexer;
mod parser;
pub mod typecheck;
pub mod compiler;
pub mod vm;
mod gc;
mod fixed;
#[macro_use]
pub mod api;

