extern crate pretty;
extern crate difference;

extern crate gluon_parser as parser;
extern crate gluon_base as base;

use std::fs::File;
use std::io::Read;

use difference::assert_diff;

use base::source::Source;
use base::pretty_print::ExprPrinter;

use parser::parse_string;

use support::MockEnv;

mod support;

#[test]
fn map() {
    let mut contents = String::new();
    File::open("../std/map.glu")
        .unwrap()
        .read_to_string(&mut contents)
        .unwrap();

    let expr = parse_string(&mut MockEnv::new(), &contents).unwrap();

    let source = Source::new(&contents);
    let printer = ExprPrinter::new(&source);
    let doc = printer.pretty_expr(&expr);
    let mut out = Vec::new();
    doc.1.render(110, &mut out).unwrap();
    use std::io::Write;
    File::create("../test.glu")
        .unwrap()
        .write_all(&out)
        .unwrap();
    assert_diff(&contents, ::std::str::from_utf8(&out).unwrap(), " ", 0);
}
