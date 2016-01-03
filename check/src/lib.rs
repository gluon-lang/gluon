#[macro_use]
extern crate log;
#[cfg(test)]
extern crate env_logger;

extern crate union_find;

#[macro_use]
extern crate mopa;

extern crate base;

#[cfg(test)]
extern crate parser;

pub use base::ast;
pub use typed::Typed;

pub mod typecheck;
mod typed;
pub mod error;
pub mod kindcheck;
pub mod macros;
mod substitution;
pub mod scoped_map;
