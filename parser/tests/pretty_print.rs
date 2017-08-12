extern crate env_logger;
extern crate pretty;
extern crate difference;
#[macro_use]
extern crate pretty_assertions;

extern crate gluon_parser as parser;
extern crate gluon_base as base;

use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

use difference::assert_diff;

use parser::format_expr;

mod support;

fn test_format(name: &str) {
    let _ = env_logger::init();

    let name = Path::new(name);
    let mut contents = String::new();
    File::open(Path::new("../").join(name))
        .unwrap()
        .read_to_string(&mut contents)
        .unwrap();

    let out_str = format_expr(&contents).unwrap();

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

#[test]
fn dont_add_newline_for_let_literal() {
    let expr = r#"
let x = 1
x
"#;
    assert_eq!(
        &format_expr(expr).unwrap(),
        r#"
let x = 1
x
"#
    );
}

#[test]
fn dont_lose_information_in_literals() {
    let expr = r#"
3.14 "\t\n\r\""
"#;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}


#[test]
fn preserve_comment_between_let_in() {
    let expr = r#"
// test
let x = 1
// test
type Test = Int
// test
1
// test2
"#;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}

#[test]
fn preserve_whitespace_in_record() {
    let expr = r#"
{
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaax = 1,


    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbby = 2
}
"#;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}


#[test]
fn preserve_block_comments() {
    let expr = r#"
/* test */
let x = { field = f /* test */ 123 /* doc */ }
/* test */
x
"#;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}

#[test]
fn preserve_more_block_comments() {
    let expr = r#"
{ /* abc */ field /* abc */ = /* test */ 123 }
"#;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}

#[test]
fn preserve_shebang_line() {
    let expr = r#"#!/bin/gluon
/* test */
let x = { field = f /* test */ 123 /* doc */ }
/* test */
x
"#;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}

#[test]
fn nested_constructor_pattern() {
    let expr = r#"
match None with
| Some (Some x) -> x
| _ -> 123
"#;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}

#[test]
fn long_pattern_match() {
    let expr = r#"
let {
    CCCCCCCCCCCCCC,
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
} =
    test
123
"#;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}