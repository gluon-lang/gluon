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
use gluon::check;
use gluon::vm;

use gluon::{new_vm, Compiler, Thread, Error, Result};
use gluon::vm::thread::ThreadInternal;
use gluon::vm::Error as VMError;

mod repl;

fn run_files<'s, I>(vm: &Thread, files: I) -> Result<()>
    where I: Iterator<Item = &'s str>
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
                (@arg INPUT: ... "Executes each file as a gluon program")
            )
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


#[cfg(test)]
mod tests {
    // If nothing else this suppresses the unused imports warnings when compiling in test mode
    #[test]
    fn execute_repl_help() {
        super::main();
    }
}
