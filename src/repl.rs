use std::io::BufReader;
use std::io::IoResult;

use EmbedLang::typecheck::*;
use EmbedLang::compiler::Compiler;
use EmbedLang::vm::{VM, parse_expr, load_script};

macro_rules! tryf {
    ($e:expr) => (try!(($e).map_err(|e| format!("{:?}", e))))
}

fn print(vm: &VM) {
    println!("{:?}", vm.pop());
}

pub fn run() {
    let vm = VM::new();
    vm.extern_function("printInt", vec![INT_TYPE.clone()], UNIT_TYPE.clone(), Box::new(print));
    for line in ::std::io::stdin().lock().lines() {
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
                Some(info) => {
                    match info {
                        TypeInfo::Struct(&(ref typ, ref fields)) => {
                            println!("struct {} {{", args);
                            match *typ {
                                FunctionType(ref field_types, _) => {
                                    for (name, typ) in fields.iter().zip(field_types.iter()) {
                                        println!("    {}: {:?},", name, typ);
                                    }
                                }
                                _ => ()
                            }
                            println!("}}");
                        }
                        TypeInfo::Enum(constructors) => {
                            println!("enum {} {{", args);
                            for ctor in constructors.iter()  {
                                print!("    {}(", ctor.name.id());
                                let mut args = ctor.arguments.iter();
                                match args.next() {
                                    Some(arg) => print!("{:?}", arg),
                                    None => ()
                                }
                                for arg in args {
                                    print!(",{:?}", arg);
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
        _ => Err("Invalid command ".to_string() + command.to_string().as_slice())
    }
}

fn run_line(vm: &VM, line: IoResult<String>) -> Result<bool, String> {
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
                let env = vm.env();
                let mut tc = Typecheck::new();
                tc.add_environment(&env);
                tryf!(tc.typecheck_expr(&mut expr));
                let mut compiler = Compiler::new(&env);
                compiler.compile_expr(&expr)
            };
            vm.new_functions((lambdas, Vec::new()));
            let v = try!(vm.execute_instructions(instructions.as_slice()));
            println!("{:?}", v);
            Ok(true)
        }
    }
}

fn load_file(vm: &VM, filename: &str) -> Result<(), String> {
    use std::io::{File, BufferedReader};
    use std::path::Path;
    let file = tryf!(File::open(&Path::new(filename)));
    let mut buffer = BufferedReader::new(file);
    load_script(vm, &mut buffer)
}

