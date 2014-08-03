#![feature(globs, phase, macro_rules, unboxed_closures, default_type_params)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

use ast::unit_type;
use parser::*;
use typecheck::*;
use compiler::*;
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
fn run_main(s: &str) -> Result<Value, String> {
    let mut buffer = BufReader::new(s.as_bytes());
    let mut parser = Parser::new(&mut buffer, |s| TcIdent { typ: unit_type.clone(), name: s });
    let mut module = match parser.module() {
        Ok(f) => f,
        Err(x) => return Err(format!("{}", x))
    };
    let mut tc = Typecheck::new();
    try!(tc.typecheck_module(&mut module)
        .map_err(|e| format!("{}", e)));
    let mut compiler = Compiler::new(&module);
    let functions = compiler.compile_module(&module);
    let mut vm = VM::new();
    vm.new_functions(functions);
    let v = vm.run_function(vm.get_function(0));
    Ok(v)
}

#[cfg(not(test))]
fn main() {
    let args = ::std::os::args();
    println!("{}", run_main(args[1].as_slice()));
}
