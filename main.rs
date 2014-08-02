#![feature(globs, phase, macro_rules)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

use parser::*;
use compiler::*;
use vm::*;

use std::io::BufReader;

mod interner;
mod ast;
mod lexer;
mod parser;
mod compiler;
mod vm;


#[cfg(not(test))]
fn run_main(s: &str) -> Result<Value, String> {
    let mut buffer = BufReader::new(s.as_bytes());
    let mut parser = Parser::new(&mut buffer);
    let f = match parser.function() {
        Ok(f) => f,
        Err(x) => return Err(format!("{}", x))
    };
    let x = ();
    let mut compiler = Compiler::new(&x);
    let cf = compiler.compile_function(&f);
    let vm = VM::new();
    let v = vm.run_function(&cf);
    Ok(v)
}

#[cfg(not(test))]
fn main() {
    let args = ::std::os::args();
    println!("{}", run_main(args[1].as_slice()));
}
