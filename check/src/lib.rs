#[macro_use]
extern crate log;
#[cfg(test)]
extern crate env_logger;
extern crate union_find;

extern crate base;
#[cfg(test)]
extern crate parser;

mod instantiate;
pub mod typecheck;
mod unify_type;
mod unify;
pub mod kindcheck;
mod substitution;
