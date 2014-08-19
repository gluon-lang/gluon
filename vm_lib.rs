#![crate_type="lib"]
#![feature(globs, phase, macro_rules, default_type_params, overloaded_calls)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

mod scoped_map;
mod interner;
pub mod ast;
pub mod lexer;
pub mod parser;
pub mod typecheck;
pub mod compiler;
pub mod vm;
pub mod api;
