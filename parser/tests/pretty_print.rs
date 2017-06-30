extern crate env_logger;
extern crate pretty;
extern crate difference;

extern crate gluon_parser as parser;
extern crate gluon_base as base;

use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

use difference::assert_diff;

use base::source::Source;
use base::pretty_print::ExprPrinter;

use parser::parse_string;

use support::MockEnv;

mod support;

fn test_format(name: &str) {
    let _ = env_logger::init();

    let name = Path::new(name);
    let mut contents = String::new();
    File::open(Path::new("../").join(name))
        .unwrap()
        .read_to_string(&mut contents)
        .unwrap();
    // The output uses \n line endings
    contents = contents.replace("\r\n", "\n");

    let expr = parse_string(&mut MockEnv::new(), &contents).unwrap();

    let source = Source::new(&contents);
    let printer = ExprPrinter::new(&source);
    let out_str = printer.format(100, &expr);
    if contents != out_str {
        let out_path = Path::new(env!("OUT_DIR")).join(name.file_name().unwrap());
        File::create(out_path)
            .unwrap()
            .write_all(out_str.as_bytes())
            .unwrap();
        assert_diff(&contents, &out_str, " ", 0);
    }
}

#[test]
fn map() {
    test_format("std/map.glu");
}

#[test]
fn prelude() {
    test_format("std/prelude.glu");
}

#[test]
fn state() {
    test_format("std/state.glu");
}

#[test]
fn stream() {
    test_format("std/stream.glu");
}

#[test]
fn string() {
    test_format("std/string.glu");
}

#[test]
fn test() {
    test_format("std/test.glu");
}

#[test]
fn types() {
    test_format("std/types.glu");
}

#[test]
fn writer() {
    test_format("std/writer.glu");
}

#[test]
fn repl() {
    test_format("repl/src/repl.glu");
}
