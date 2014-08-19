#![feature(globs, phase, macro_rules, default_type_params, overloaded_calls)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

extern crate vm_lib;

#[cfg(not(test))]
use vm_lib::vm::run_main;

mod repl;


#[cfg(not(test))]
fn main() {
    let args = ::std::os::args();
    if args.len() < 2 {
        println!("Expected atleast 1 argument");
    }
    else if args[1].as_slice() == "-i" {
        repl::run();
    }
    else {
        println!("{}", run_main(args[1].as_slice()));
    }
}
