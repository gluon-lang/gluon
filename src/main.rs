#[macro_use]
extern crate log;
#[cfg(feature = "env_logger")]
extern crate env_logger;
extern crate clap;
#[macro_use]
extern crate quick_error;
#[macro_use]
extern crate lazy_static;
extern crate linenoise;

extern crate base;
extern crate embed_lang;
extern crate check;
extern crate parser;
#[macro_use]
extern crate vm;


#[cfg(not(test))]
use std::error::Error as StdError;
#[cfg(not(test))]
use embed_lang::{new_vm, Compiler};
#[cfg(not(test))]
use clap::{Arg, App};

mod repl;


#[cfg(not(test))]
fn run_files<'s, I>(files: I) -> Result<(), Box<StdError + Send + Sync>>
where I: Iterator<Item = &'s str>
{
    let vm = new_vm();
    let mut compiler = Compiler::new();
    for file in files {
        try!(compiler.load_file(&vm, file));
    }
    Ok(())
}


#[cfg(all(not(test), feature = "env_logger"))]
fn init_env_logger() {
    ::env_logger::init().unwrap();
}

#[cfg(all(not(test), not(feature = "env_logger")))]
fn init_env_logger() {
}

#[cfg(not(test))]
fn main() {
    // Need the extra stack size when compiling the program using the msvc compiler
    ::std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            init_env_logger();

            let matches = App::new("embed_lang")
                              .about("Executes embed_lang programs")
                              .arg(Arg::with_name("INPUT").multiple(true))
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
                match run_files(args) {
                    Ok(()) => (),
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
