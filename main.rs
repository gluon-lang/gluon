#![feature(globs, phase, macro_rules, default_type_params)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

#[cfg(not(test))]
use vm::run_main;

mod scoped_map;
mod interner;
mod ast;
mod lexer;
mod parser;
mod typecheck;
mod compiler;
mod vm;
mod repl;


#[cfg(not(test))]
fn main() {
    let args = ::std::os::args();
    if args.len() < 2 {
        println!("Expected atleast 1 argument");
    }
    else if args[1].as_slice() == "-i" {
        repl::run();
    }
    else {
        println!("{}", run_main(args[1].as_slice()));
    }
}
