#![feature(globs, phase, macro_rules)]
extern crate collections;
#[phase(plugin, link)]
extern crate log;

mod interner;
mod ast;
mod lexer;
mod parser;


fn main() {
}
