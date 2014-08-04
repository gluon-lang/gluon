use std::io::BufReader;
use std::io::IoResult;

use ast::unit_type;
use parser::Parser;
use typecheck::{TcIdent, Typecheck};
use compiler::Compiler;
use vm::VM;

macro_rules! tryf(
    ($e:expr) => (try!(($e).map_err(|e| format!("{}", e))))
)

pub fn run() {
    let mut vm = VM::new();
    for line in ::std::io::stdin().lines() {
        match run_line(&mut vm, line) {
            Ok(continue_repl) => {
                if !continue_repl {
                    break
                }
            }
            Err(e) => println!("{}", e)
        }
    }
}

fn run_line(vm: &mut VM, line: IoResult<String>) -> Result<bool, String> {
    let expr_str = tryf!(line);
    if expr_str.as_slice().slice_to(2) == ":q" {
        return Ok(false)
    }
    let mut buffer = BufReader::new(expr_str.as_bytes());
    let mut parser = Parser::new(&mut buffer, |s| TcIdent { name: s, typ: unit_type.clone() });
    let mut expr = try!(parser.expression());
    let mut tc = Typecheck::new();
    tryf!(tc.typecheck(&mut expr));
    let mut instructions = Vec::new();
    {
        let vm: &VM = vm;
        let mut compiler = Compiler::new(vm);
        compiler.compile(&expr, &mut instructions);
    }
    let v = vm.execute_instructions(instructions.as_slice());
    match v {
        Some(v) => println!("{}", v),
        None => println!("")
    }
    Ok(true)
}
