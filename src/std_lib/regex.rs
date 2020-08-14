//! Module containing bindings to the `regex` library.

extern crate regex;

use crate::vm::{self, thread::Thread, ExternModule};

#[derive(Debug, Userdata, Trace, VmType)]
#[gluon(vm_type = "std.regex.Regex")]
#[gluon(crate_name = "vm")]
#[gluon_trace(skip)]
struct Regex(regex::Regex);

#[derive(Debug, Userdata, Trace, VmType)]
#[gluon(vm_type = "std.regex.Error")]
#[gluon(crate_name = "vm")]
#[gluon_trace(skip)]
struct Error(regex::Error);

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

#[derive(Pushable, VmType)]
#[gluon(vm_type = "std.regex.types.Match")]
#[gluon(crate_name = "vm")]
struct Match<'a> {
    start: usize,
    end: usize,
    text: &'a str,
}

impl<'a> Match<'a> {
    fn new(m: regex::Match<'a>) -> Self {
        Match {
            start: m.start(),
            end: m.end(),
            text: m.as_str(),
        }
    }
}

fn find<'a>(re: &Regex, text: &'a str) -> Option<Match<'a>> {
    let &Regex(ref re) = re;
    re.find(text).map(Match::new)
}

fn captures<'a>(re: &Regex, text: &'a str) -> Option<Vec<Option<Match<'a>>>> {
    let &Regex(ref re) = re;
    re.captures(text)
        .map(|c| (0..c.len()).map(move |i| c.get(i).map(Match::new)))
        // FIXME Once rust stops ICEing .map(Collect::new)
        .map(|i| i.collect())
}

fn error_to_string(err: &Error) -> String {
    let &Error(ref err) = err;
    err.to_string()
}

mod std {
    pub mod regex {
        pub use crate::std_lib::regex as prim;
    }
}

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    vm.register_type::<Regex>("std.regex.Regex", &[])?;
    vm.register_type::<Error>("std.regex.Error", &[])?;

    ExternModule::new(
        vm,
        record! {
            type Error => Error,
            type Regex => Regex,
            type Match => Match,

            new => primitive!(1, std::regex::prim::new),
            is_match => primitive!(2, std::regex::prim::is_match),
            find => primitive!(2, std::regex::prim::find),
            // Workaround MIR bug in rustc
            captures => primitive!(2, "std.regex.prim.captures", |x, y| std::regex::prim::captures(x, y)),
            error_to_string => primitive!(1, std::regex::prim::error_to_string)
        },
    )
}
