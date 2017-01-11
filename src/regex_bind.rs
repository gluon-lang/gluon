//! Module containing bindings to the `regex` library.

extern crate regex;

use vm;
use vm::thread::Thread;

use self::regex::Regex;

/// Test the equality of two strings using the regex crate
fn regex_match(re: &str, text: &str) -> bool {
    Regex::new(re).map(|r| r.is_match(text)).unwrap_or(false)
}

pub fn load(vm: &Thread) -> vm::Result<()> {
    vm.define_global("regex",
                     record!(matches => primitive!(2 regex_match)),
                    )
}
