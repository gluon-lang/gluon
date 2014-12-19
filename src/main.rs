#![feature(globs, phase, macro_rules, default_type_params)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

extern crate EmbedLang;

#[cfg(not(test))]
use EmbedLang::vm::{VM, run_main, run_buffer_main};

use std::os::set_exit_status;

mod repl;


#[cfg(not(test))]
fn main() {
    let args = ::std::os::args();
	println!("{}", args);
    if args.len() == 1 {
        let vm = VM::new();
        let mut buffer = ::std::io::stdin();
        let value = match run_buffer_main(&vm, &mut buffer) {
            Ok(value) => value,
            Err(err) => {
                println!("{}", err);
                set_exit_status(1);
                return
            }
        };
        println!("{}", value);
    }
    else if args[1].as_slice() == "-i" {
        repl::run();
    }
    else if args.len() == 2 {
        let vm = VM::new();
        println!("{}", run_main(&vm, args[1].as_slice()));
    }
}
