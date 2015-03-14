use std::io;
use std::io::BufReadExt;

use EmbedLang::typecheck::*;
use EmbedLang::compiler::{Assembly, Compiler};
use EmbedLang::vm::{VM, parse_expr, load_script};

macro_rules! tryf {
    ($e:expr) => (try!(($e).map_err(|e| format!("{:?}", e))))
}

fn print(vm: &VM) {
    println!("{:?}", vm.pop());
}

pub fn run() {
    let vm = VM::new();
    vm.extern_function("printInt", vec![INT_TYPE.clone()], UNIT_TYPE.clone(), Box::new(print))
        .unwrap();
    let stdin = io::stdin();
    for line in stdin.lock().lines() {
        match run_line(&vm, line) {
            Ok(continue_repl) => {
                if !continue_repl {
                    break
                }
            }
            Err(e) => println!("{}", e)
        }
    }
}

fn run_command(vm: &VM, command: char, args: &str) -> Result<bool, String> {
    match command {
        'q' => Ok(false),
        'l' => {
            try!(load_file(vm, args));
            Ok(true)
        }
        't' => {
            match vm.env().find_type_info(&vm.intern(args)) {
                Some(constructors) => {
                    println!("data {} {{", args);
                    for ctor in constructors.iter()  {
                        print!("    {}(", ctor.name.id());
                        let mut first = true;
                        ctor.arguments.each_type(|arg| {
                            if first {
                                first = false;
                                print!("{:?}", arg);
                            }
                            else {
                                print!(", {:?}", arg);
                            }
                        });
                        println!("),");
                    }
                    println!("}}");
                }
                None => println!("{} is not a type", args)
            }
            Ok(true)
        }
        _ => Err("Invalid command ".to_string() + &*command.to_string())
    }
}

fn run_line(vm: &VM, line: io::Result<String>) -> Result<bool, String> {
    let expr_str = tryf!(line);
    match expr_str.char_at(0) {
        ':' => {
            run_command(vm, expr_str.char_at(1), expr_str[2..].trim())
        }
        _ =>  {
            let mut buffer = io::BufReader::new(expr_str.as_bytes());
            let mut expr = try!(parse_expr(&mut buffer, vm));
            let (instructions, lambdas) = {
                let env = vm.env();
                let mut tc = Typecheck::new();
                tc.add_environment(&env);
                tryf!(tc.typecheck_expr(&mut expr));
                let mut compiler = Compiler::new(&env);
                compiler.compile_expr(&expr)
            };
            vm.new_functions(Assembly { initializer: Vec::new(), anonymous_functions: lambdas, trait_functions: Vec::new(), globals: Vec::new() });
            let v = try!(vm.execute_instructions(&*instructions));
            println!("{:?}", v);
            Ok(true)
        }
    }
}

fn load_file(vm: &VM, filename: &str) -> Result<(), String> {
    use std::fs::File;
    use std::io::BufReader;
    let file = tryf!(File::open(&Path::new(filename)));
    let mut buffer = BufReader::new(file);
    load_script(vm, &mut buffer)
}

