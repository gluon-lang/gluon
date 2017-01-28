#[macro_use]
extern crate log;
#[cfg(feature = "env_logger")]
extern crate env_logger;
extern crate clap;
#[macro_use]
extern crate quick_error;
#[macro_use]
extern crate lazy_static;
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
#[cfg(not(test))]
use clap::{Arg, App};

mod repl;


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

            let matches = App::new("gluon")
                .about("Executes gluon programs")
                .arg(Arg::with_name("INPUT")
                    .multiple(true)
                    .help("Executes each file as a gluon program"))
                .arg(Arg::with_name("REPL")
                    .short("i")
                    .long("interactive")
                    .help("Starts the repl")
                    .takes_value(false))
                .get_matches();
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
