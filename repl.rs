use std::io::BufReader;
use std::io::IoResult;

use parser::Parser;
use typecheck::*;
use compiler::Compiler;
use vm::{VM, StackFrame, load_script};

macro_rules! tryf(
    ($e:expr) => (try!(($e).map_err(|e| format!("{}", e))))
)

fn print(_: &VM, mut stack: StackFrame) {
    println!("{}", stack.pop());
}

pub fn run() {
    let mut vm = VM::new();
    vm.extern_function("printInt", vec![int_type_tc.clone()], unit_type_tc.clone(), print);
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
    match expr_str.as_slice().slice_to(2) {
        ":q" => return Ok(false),
        ":l" => {
            let filename = expr_str.as_slice().slice_from(2).trim();
            try!(load_file(vm, filename));
            return Ok(true)
        }
        _ => ()
    }
    let mut buffer = BufReader::new(expr_str.as_bytes());
    let mut parser = Parser::new(&mut buffer, |s| TcIdent { name: s, typ: unit_type_tc.clone() });
    let mut expr = try!(parser.expression());
    let mut instructions = Vec::new();
    {
        let vm: &VM = vm;
        let mut tc = Typecheck::new();
        tc.add_environment(vm);
        tryf!(tc.typecheck(&mut expr));
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

fn load_file(vm: &mut VM, filename: &str) -> Result<(), String> {
    use std::io::{File, BufferedReader};
    use std::path::Path;
    let file = tryf!(File::open(&Path::new(filename)));
    let mut buffer = BufferedReader::new(file);
    load_script(vm, &mut buffer)
}

