#![crate_type="lib"]
#![feature(globs, phase, macro_rules, default_type_params, overloaded_calls)]
extern crate collections;
#[phase(plugin, link)]
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

