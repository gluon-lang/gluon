#![crate_type="lib"]
#![feature(globs, phase, macro_rules, default_type_params, overloaded_calls)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

pub use interner::InternedStr;

pub use typecheck::TcType;
pub use compiler::{CompiledFunction, Instruction};


mod scoped_map;
mod interner;
pub mod ast;
mod lexer;
mod parser;
mod typecheck;
mod compiler;
pub mod vm;
pub mod api;

