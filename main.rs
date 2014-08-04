#![feature(globs, phase, macro_rules, unboxed_closures, default_type_params)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

use vm::*;

use std::io::BufReader;

mod scoped_map;
mod interner;
mod ast;
mod lexer;
mod parser;
mod typecheck;
mod compiler;
mod vm;


#[cfg(not(test))]
fn main() {
    let args = ::std::os::args();
    println!("{}", run_main(args[1].as_slice()));
}
