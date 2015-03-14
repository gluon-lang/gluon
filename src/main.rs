#![feature(collections, exit_status, old_path, io)]
#[macro_use]
extern crate log;

extern crate EmbedLang;

#[cfg(not(test))]
use EmbedLang::vm::{VM, run_main, run_buffer_main};

#[cfg(not(test))]
use std::env::set_exit_status;

mod repl;


#[cfg(not(test))]
fn main() {
    let args: Vec<_> = ::std::env::args().collect();
    if args.len() == 1 {
        let vm = VM::new();
        let buffer = ::std::io::stdin();
        let value = match run_buffer_main(&vm, &mut buffer.lock()) {
            Ok(value) => value,
            Err(err) => {
                println!("{}", err);
                set_exit_status(1);
                return
            }
        };
        println!("{:?}", value);
    }
    else if args[1] == "-i" {
        repl::run();
    }
    else if args.len() == 2 {
        let vm = VM::new();
        println!("{:?}", run_main(&vm, &args[1]));
    }
}
