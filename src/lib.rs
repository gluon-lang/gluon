#![crate_type="lib"]
#[macro_use]
extern crate log;
extern crate env_logger;

mod crates {
    extern crate base;
    extern crate parser;
    extern crate check;
    extern crate vm;
}

pub use crates::base;
pub use crates::parser;
pub use crates::check;
pub use crates::vm;
