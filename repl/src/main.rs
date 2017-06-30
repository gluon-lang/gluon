//! REPL for the gluon programming language
#![doc(html_root_url="https://docs.rs/gluon_repl/0.4.1")] // # GLUON

#[macro_use]
extern crate log;
#[cfg(feature = "env_logger")]
extern crate env_logger;
#[macro_use]
extern crate clap;
extern crate futures;

#[macro_use]
extern crate gluon_vm;
extern crate gluon;

use gluon::base;
use gluon::parser;
use gluon::check;
use gluon::vm;

use gluon::{new_vm, Compiler, Thread, Error, Result};
use gluon::vm::thread::ThreadInternal;
use gluon::vm::Error as VMError;

mod repl;

fn run_files<'s, I>(vm: &Thread, files: I) -> Result<()>
where
    I: Iterator<Item = &'s str>,
{
    let mut compiler = Compiler::new();
    for file in files {
        compiler.load_file(&vm, file)?;
    }
    Ok(())
}

#[cfg(feature = "env_logger")]
fn init_env_logger() {
    let _ = ::env_logger::init();
}

#[cfg(not(feature = "env_logger"))]
fn init_env_logger() {}

fn fmt_file(name: &str) -> Result<()> {
    use std::io::{Read, Seek, SeekFrom, Write};
    use std::fs::{File, OpenOptions};

    use gluon::base::pretty_print::ExprPrinter;
    use gluon::base::source::Source;

    let mut input_file = OpenOptions::new()
        .read(true)
        .write(true)
        .open(name)?;
    
    let mut buffer = String::new();
    input_file.read_to_string(&mut buffer)?;

    let mut backup = File::create(&format!("{}.bk", name))?;
    backup.write_all(buffer.as_bytes())?;

    let expr = Compiler::new().parse_expr("", &buffer)?;

    let source = Source::new(&buffer);
    let printer = ExprPrinter::new(&source);

    let output = printer.format(100, &expr);
    input_file.seek(SeekFrom::Start(0))?;
    input_file.write_all(output.as_bytes())?;
    Ok(())
}

fn main() {
    const GLUON_VERSION: &'static str = env!("CARGO_PKG_VERSION");

    // Need the extra stack size when compiling the program using the msvc compiler
    ::std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            init_env_logger();

            let matches = clap_app!(gluon =>
                (version: GLUON_VERSION)
                (about: "executes gluon programs")
                (@arg REPL: -i --interactive "Starts the repl")
                (@subcommand fmt => 
                    (about: "Formats gluon source code")
                    (@arg INPUT: ... "Formats each file")
                )
                (@arg INPUT: ... "Executes each file as a gluon program")
            ).get_matches();
            if let Some(fmt_matches) = matches.subcommand_matches("fmt") {
                if let Some(args) = fmt_matches.values_of("INPUT") {
                    for arg in args {
                        if let Err(err) = fmt_file(arg) {
                            println!("{}", err);
                            std::process::exit(1);
                        }
                    }
                } else {
                    println!("Expected input arguments to `fmt`");
                    std::process::exit(1);
                }
            } else if matches.is_present("REPL") {
                if let Err(err) = repl::run() {
                    println!("{}", err);
                }
            } else if let Some(args) = matches.values_of("INPUT") {
                let vm = new_vm();
                match run_files(&vm, args) {
                    Ok(()) => (),
                    Err(err @ Error::VM(VMError::Message(_))) => {
                        println!("{}\n{}", err, vm.context().stack.stacktrace(0));
                    }
                    Err(msg) => println!("{}", msg),
                }
            } else {
                println!("{}", matches.usage());
            }
        })
        .unwrap()
        .join()
        .unwrap();
}


#[cfg(test)]
mod tests {
    // If nothing else this suppresses the unused imports warnings when compiling in test mode
    #[test]
    fn execute_repl_help() {
        super::main();
    }
}
