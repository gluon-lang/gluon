use std::io::BufReader;
use std::io::IoResult;

use vm_lib::typecheck::*;
use vm_lib::compiler::Compiler;
use vm_lib::vm::{VM, StackFrame, parse_expr, load_script};

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

fn run_command(vm: &mut VM, command: char, args: &str) -> Result<bool, String> {
    match command {
        'q' => Ok(false),
        'l' => {
            try!(load_file(vm, args));
            Ok(true)
        }
        't' => {
            match vm.find_type_info(args) {
                Some(info) => {
                    match info {
                        Struct(fields) => {
                            println!("struct {} {{", args);
                            for field in fields.iter()  {
                                println!("    {}: {},", field.name, field.typ);
                            }
                            println!("}}");
                        }
                        Enum(constructors) => {
                            println!("enum {} {{", args);
                            for ctor in constructors.iter()  {
                                print!("    {}(", ctor.name.id());
                                let mut args = ctor.arguments.iter();
                                match args.next() {
                                    Some(arg) => print!("{}", arg),
                                    None => ()
                                }
                                for arg in args {
                                    print!(",{}", arg);
                                }
                                println!("),");
                            }
                            println!("}}");
                        }
                    }
                }
                None => println!("{} is not a type", args)
            }
            Ok(true)
        }
        _ => Err("Invalid command ".to_string() + command.to_string())
    }
}

fn run_line(vm: &mut VM, line: IoResult<String>) -> Result<bool, String> {
    let expr_str = tryf!(line);
    let slice = expr_str.as_slice();
    match slice.char_at(0) {
        ':' => {
            run_command(vm, slice.char_at(1), expr_str.as_slice().slice_from(2).trim())
        }
        _ =>  {
            let mut buffer = BufReader::new(expr_str.as_bytes());
            let mut expr = try!(parse_expr(&mut buffer, vm));
            let (instructions, lambdas) = {
                let vm: &VM = vm;
                let mut tc = Typecheck::new();
                tc.add_environment(vm);
                tryf!(tc.typecheck(&mut expr));
                let mut compiler = Compiler::new(vm);
                compiler.compile_expr(&expr)
            };
            vm.new_functions(lambdas);
            let v = vm.execute_instructions(instructions.as_slice());
            match v {
                Some(v) => println!("{}", v),
                None => println!("")
            }
            Ok(true)
        }
    }
}

fn load_file(vm: &mut VM, filename: &str) -> Result<(), String> {
    use std::io::{File, BufferedReader};
    use std::path::Path;
    let file = tryf!(File::open(&Path::new(filename)));
    let mut buffer = BufferedReader::new(file);
    load_script(vm, &mut buffer)
}

