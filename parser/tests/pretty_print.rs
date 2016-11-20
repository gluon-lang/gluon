extern crate pretty;

extern crate gluon_parser as parser;
extern crate gluon_base as base;

use std::fs::File;
use std::io::{Read, Write};

use pretty::Arena;

use parser::parse_string;

use support::MockEnv;

mod support;

#[test]
fn map() {
    let mut contents = String::new();
    File::open("../std/map.glu").unwrap().read_to_string(&mut contents).unwrap();

    let expr = parse_string(&mut MockEnv::new(), &contents).unwrap();

    let arena = Arena::new();
    let doc = base::pretty_print::pretty_expr(&arena, &expr.value);
    let mut out = Vec::new();
    doc.1.render(110, &mut out).unwrap();
    println!("{}", ::std::str::from_utf8(&out).unwrap());
    File::create("../test").unwrap().write_all(&out).unwrap();
    assert!(false);
}
