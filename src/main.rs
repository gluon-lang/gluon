#[macro_use]
extern crate log;
extern crate env_logger;

extern crate embed_lang;

#[cfg(not(test))]
use embed_lang::vm::{VM, run_expr};
#[cfg(not(test))]
use std::env;
#[cfg(not(test))]
use std::io::Read;

mod repl;


#[cfg(not(test))]
fn main() {
    let _ = ::env_logger::init();
    let args: Vec<_> = env::args().collect();
    if args.len() == 1 {
        let vm = VM::new();
        let buffer = ::std::io::stdin();
        let mut expr = String::new();
        buffer.lock().read_to_string(&mut expr)
            .unwrap();
        let value = match run_expr(&vm, &expr) {
            Ok(value) => value,
            Err(err) => {
                println!("{}", err);
                return
            }
        };
        println!("{:?}", value);
    }
    else if args[1] == "-i" {
        repl::run();
    }
}
