#[macro_use(assert_diff)]
extern crate difference;
extern crate env_logger;
#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_format as format;

use std::env;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

use format::format_expr;

fn test_format(name: &str) {
    let _ = env_logger::init();

    let name = Path::new(name);
    let mut contents = String::new();
    File::open(Path::new("../").join(name))
        .unwrap()
        .read_to_string(&mut contents)
        .unwrap();

    let out_str = format_expr(&contents).unwrap_or_else(|err| panic!("{}", err));

    if contents != out_str {
        let args: Vec<_> = env::args().collect();
        let out_path = Path::new(&args[0][..])
            .parent()
            .and_then(|p| p.parent())
            .expect("folder")
            .join(name.file_name().unwrap());
        File::create(out_path)
            .unwrap()
            .write_all(out_str.as_bytes())
            .unwrap();

        assert_diff!(&contents, &out_str, " ", 0);
    }
}

#[test]
fn bool() {
    test_format("std/bool.glu");
}

#[test]
fn char() {
    test_format("std/char.glu");
}

#[test]
fn function() {
    test_format("std/function.glu");
}

#[test]
fn map() {
    test_format("std/map.glu");
}

#[test]
fn option() {
    test_format("std/option.glu");
}

#[test]
fn prelude() {
    test_format("std/prelude.glu");
}

#[test]
fn result() {
    test_format("std/result.glu");
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
fn unit() {
    test_format("std/unit.glu");
}

#[test]
fn writer() {
    test_format("std/writer.glu");
}

#[test]
fn parser() {
    test_format("std/parser.glu");
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
// test1
let x = 1
// test2
type Test = Int
// test3
1
// test4
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn preserve_whitespace_in_record() {
    let expr = r#"
{
    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaax = 1,


    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbby = 2,
}
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
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

// TODO
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

#[test]
fn preserve_comments_in_function_types() {
    let expr = r#"#!/bin/gluon
let x : /* first */ Int /* Int */ ->
    // Float
    Float /* last */ = ()
x
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn preserve_comments_app_types() {
    let expr = r#"#!/bin/gluon
let x : Test /* first */ Int
    // middle
    Float /* last */ = ()
x
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn preserve_doc_comments_in_record_types() {
    let expr = r#"#!/bin/gluon
type Test = {
    /// test
    field1 : Int,
    /**
     middle
    */
    field2 : Float
}
x
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn preserve_comments_in_empty_record() {
    let expr = r#"
{
// 123
}
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn preserve_comments_in_record_base() {
    let expr = r#"
{
    // 123
    ..
    // abc
    test
/* x */
}
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn small_record_in_let() {
    let expr = r#"
let semigroup =
    { append }
()
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}
