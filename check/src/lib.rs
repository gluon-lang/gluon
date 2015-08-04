#![feature(box_syntax)]
#[macro_use]
extern crate log;

extern crate base;

pub use base::interner::InternedStr;

pub use base::{ast, gc, interner};

pub mod typecheck;
mod kindcheck;
mod substitution;
mod scoped_map;
