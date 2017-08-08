//! Module containing bindings to the `regex` library.

extern crate regex;

use std::error::Error as StdError;

use vm;
use vm::api::{Userdata, VmType};
use vm::gc::{Gc, Traverseable};
use vm::thread::Thread;

#[derive(Debug)]
struct Regex(regex::Regex);

impl Userdata for Regex {}

impl VmType for Regex {
    type Type = Regex;
}

impl Traverseable for Regex {
    fn traverse(&self, _: &mut Gc) {}
}

#[derive(Debug)]
struct Error(regex::Error);

impl Userdata for Error {}

impl VmType for Error {
    type Type = Error;
}

impl Traverseable for Error {
    fn traverse(&self, _: &mut Gc) {}
}

fn new(re: &str) -> Result<Regex, Error> {
    match regex::Regex::new(re) {
        Ok(r) => Ok(Regex(r)),
        Err(e) => Err(Error(e)),
    }
}

fn is_match(re: &Regex, text: &str) -> bool {
    let &Regex(ref re) = re;
    re.is_match(text)
}

fn error_to_string(err: &Error) -> &str {
    let &Error(ref err) = err;
    err.description()
}


pub fn load(vm: &Thread) -> vm::Result<()> {
    vm.register_type::<Regex>("Regex", &[])?;
    vm.register_type::<Error>("Error", &[])?;
    vm.define_global(
        "regex",
        record!(new => primitive!(1 new),
                             is_match => primitive!(2 is_match),
                             error_to_string => primitive!(1 error_to_string)
                            ),
    )
}
