#[macro_use]
extern crate log;
#[cfg(feature = "env_logger")]
extern crate env_logger;
#[macro_use]
extern crate clap;
extern crate futures;

extern crate gluon_base as base;
extern crate gluon;
extern crate gluon_check as check;
extern crate gluon_parser as parser;
#[macro_use]
extern crate gluon_vm as vm;

#[cfg(not(test))]
use gluon::{new_vm, Compiler, Thread, Error, Result};
#[cfg(not(test))]
use gluon::vm::thread::ThreadInternal;
#[cfg(not(test))]
use gluon::vm::Error as VMError;

mod repl;

const GLUON_VERSION: &'static str = "0.3.0";


#[cfg(not(test))]
fn run_files<'s, I>(vm: &Thread, files: I) -> Result<()>
    where I: Iterator<Item = &'s str>,
{
    let mut compiler = Compiler::new();
    for file in files {
        compiler.load_file(&vm, file)?;
    }
    Ok(())
}


#[cfg(all(not(test), feature = "env_logger"))]
fn init_env_logger() {
    ::env_logger::init().unwrap();
}

#[cfg(all(not(test), not(feature = "env_logger")))]
fn init_env_logger() {}

#[cfg(not(test))]
fn main() {
    // Need the extra stack size when compiling the program using the msvc compiler
    ::std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            init_env_logger();

            let matches = clap_app!(gluon =>
                (version: GLUON_VERSION)
                (about: "executes gluon programs")
                (@arg REPL: -i --interactive "Starts the repl")
                (@arg INPUT: ... "Executes each file as a gluon program")
            ).get_matches();
            if matches.is_present("REPL") {
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
