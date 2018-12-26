#[macro_use(assert_diff)]
extern crate difference;
extern crate env_logger;
#[macro_use]
extern crate pretty_assertions;

extern crate gluon;
extern crate gluon_base as base;
extern crate gluon_format as format;

use std::env;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

use gluon::{Compiler, RootedThread, VmBuilder};

fn new_vm() -> RootedThread {
    VmBuilder::new()
        .import_paths(Some(vec![".".into(), "..".into()]))
        .build()
}

fn format_expr(expr: &str) -> gluon::Result<String> {
    let mut compiler = Compiler::new();
    let thread = new_vm();
    compiler.format_expr(&mut format::Formatter::default(), &thread, "test", expr)
}

fn format_expr_expanded(expr: &str) -> gluon::Result<String> {
    let mut compiler = Compiler::new();
    let thread = new_vm();
    compiler.format_expr(
        &mut format::Formatter { expanded: true },
        &thread,
        "test",
        expr,
    )
}

fn test_format(name: &str) {
    let _ = env_logger::try_init();

    let mut contents = String::new();
    File::open(Path::new("../").join(name))
        .or_else(|_| File::open(name))
        .unwrap()
        .read_to_string(&mut contents)
        .unwrap();

    let mut compiler = Compiler::new();
    let thread = new_vm();
    let out_str = compiler
        .format_expr(&mut format::Formatter::default(), &thread, name, &contents)
        .unwrap_or_else(|err| panic!("{}", err));

    if contents != out_str {
        let args: Vec<_> = env::args().collect();
        let out_path = Path::new(&args[0][..])
            .parent()
            .and_then(|p| p.parent())
            .expect("folder")
            .join(Path::new(name).file_name().unwrap());
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
fn random() {
    test_format("std/random.glu");
}

#[test]
fn repl() {
    test_format("repl/src/repl.glu");
}

#[test]
fn json() {
    test_format("std/json/de.glu");
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
fn raw_string_literal() {
    let expr = r####"
r##"abc
    "  "##
"####;
    assert_eq!(&format_expr(expr).unwrap(), expr);
}

#[test]
fn implicit_arg() {
    let expr = r#"
f ?32 ""
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
fn doc_comment_in_record_expr() {
    let expr = r#"
{
    /// test
    /// test
    field1 = 1,
}
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

#[test]
fn do_expression() {
    let expr = r#"
do /* x1 */ x /* x2 */ = Some 1
// test
test abc 1232 ""
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn if_else_multiple() {
    let expr = r#"
if x then y
else if z then w
else 0
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn if_else_multiple_let_multiline_1() {
    let expr = r#"
if x then
    f 123 483
else if z then
    "12312"
else
    do x = 1
    x
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn if_else_multiple_multiline_2() {
    let expr = r#"
if x then
    do z = io
    io
else if z then
    type X = Int
    123
else
    let x = 1
    x
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn fully_break_function_type() {
    let expr = r#"
let traverse_with_key f m x : [Ord k]
        -> Applicative t
        -> (k -> a -> t b)
        -> Map k a
        -> ()
        -> ()
    =
    ()
()
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn comments_in_block_exprs() {
    let expr = r#"
// test
test 123

// test1

// test1

abc ""
// test2
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
#[ignore] // TODO
fn function_type_with_comments() {
    let expr = r#"
type Handler a =
    // Success continuation
    (a -> HttpState -> IO Response)
    // Failure continuation
    -> (Failure -> HttpState -> IO Response)
    -> IO Response
()
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn variant_type() {
    let expr = r#"
type TestCase a =
    | LoooooooooooooooooongTest String (() -> std.test.Test a)
    | LoooooooooooooooooooooooongGroup String (Array (std.test.TestCase a))
()
"#;
    assert_diff!(
        &format_expr(expr).unwrap_or_else(|err| panic!("{}", err)),
        expr,
        " ",
        0
    );
}

#[test]
fn multiline_string() {
    let expr = r#"
let x = "abc
        123
    "
x
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn derive_simple() {
    let expr = r#"
#[derive(Show)]
type Test =
    | Test
Test
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn derive_parameterized() {
    let expr = r#"
#[derive(Show)]
type Test a =
    | Test a
Test 1
"#;
    assert_diff!(&format_expr(expr).unwrap(), expr, " ", 0);
}

#[test]
fn derive_expanded() {
    let expr = r#"
#[derive(Show)]
type Test =
    | Test
Test
"#;
    let expected = r#"
#[derive(Show)]
type Test =
    | Test
rec let show_Test : Show Test =
    rec let show_ x : Test -> String =
        match x with
        | Test -> "Test"
    { show = show_ }
Test
"#;
    assert_diff!(&format_expr_expanded(expr).unwrap(), expected, "\n", 0);
}

#[test]
fn derive_eq_recursive_expanded() {
    let expr = r#"
#[derive(Eq)]
type Recursive = | End | Rec Recursive
End
"#;
    let expected = r#"
#[derive(Eq)]
type Recursive =
    | End
    | Rec Recursive
rec let eq_Recursive : Eq Recursive =
    rec let eq l r : Recursive -> Recursive -> _ =
        match (l, r) with
        | (End, End) -> True
        | (Rec arg_l, Rec arg_r) -> eq arg_l arg_r
        | _ -> False
    { (==) = eq }
End
"#;
    assert_diff!(&format_expr_expanded(expr).unwrap(), expected, "\n", 0);
}

#[test]
fn derive_parameterized_expanded() {
    let expr = r#"
#[derive(Show)]
type Test a =
    | Test a
Test 1
"#;
    let expected = r#"
#[derive(Show)]
type Test a =
    | Test a
rec let show_Test : [Show a] -> Show (Test a) =
    rec let show_ x : Test a -> String =
        match x with
        | Test arg_0 -> "Test" ++ " " ++ "(" ++ show arg_0 ++ ")"
    { show = show_ }
Test 1
"#;
    assert_diff!(&format_expr_expanded(expr).unwrap(), expected, "\n", 0);
}

#[test]
fn derive_show_recursive_expanded() {
    let expr = r#"
rec
#[derive(Show)]
type Test a =
    | Test (Test2 a)
#[derive(Show)]
type Test2 a =
    | Test2 (Test a)
    | Nil
in
Test 1
"#;
    let expected = r#"
rec
#[derive(Show)]
type Test a =
    | Test (Test2 a)
#[derive(Show)]
type Test2 a =
    | Test2 (Test a)
    | Nil
in
rec
let show_Test : [Show a] -> Show (Test a) =
    rec let show_ x : Test a -> String =
        match x with
        | Test arg_0 -> "Test" ++ " " ++ "(" ++ show arg_0 ++ ")"
    { show = show_ }
let show_Test2 : [Show a] -> Show (Test2 a) =
    rec let show_ x : Test2 a -> String =
        match x with
        | Test2 arg_0 -> "Test2" ++ " " ++ "(" ++ show arg_0 ++ ")"
        | Nil -> "Nil"
    { show = show_ }
Test 1
"#;
    assert_diff!(&format_expr_expanded(expr).unwrap(), expected, "\n", 0);
}

#[test]
fn derive_deserialize1() {
    let expr = r#"
#[derive(Deserialize)]
type Record = { x : Int }
()
"#;
    let expected = r#"
#[derive(Deserialize)]
type Record = { x : Int }
rec let deserialize_Record : Deserialize Record =
    let { ValueDeserializer, deserializer, field, ? } = import! std.json.de
    let { map } = import! std.functor
    let { (<*>) } = import! std.applicative
    let { (<|>) } = import! std.alternative
    let deserializer : ValueDeserializer Record = map (\x -> { x }) (field "x" deserializer)
    { deserializer = deserializer }
()
"#;
    assert_diff!(&format_expr_expanded(expr).unwrap(), expected, "\n", 0);
}

#[test]
fn derive_deserialize2() {
    let expr = r#"
#[derive(Deserialize)]
type Record = { x : Int, y : Float }
()
"#;
    let expected = r#"
#[derive(Deserialize)]
type Record = { x : Int, y : Float }
rec let deserialize_Record : Deserialize Record =
    let { ValueDeserializer, deserializer, field, ? } = import! std.json.de
    let { map } = import! std.functor
    let { (<*>) } = import! std.applicative
    let { (<|>) } = import! std.alternative
    let deserializer : ValueDeserializer Record
        = map (\x y -> { x, y }) (field "x" deserializer)
            <*> field "y" deserializer
    { deserializer = deserializer }
()
"#;
    assert_diff!(&format_expr_expanded(expr).unwrap(), expected, "\n", 0);
}

#[test]
fn derive_serialize1() {
    let expr = r#"
#[derive(Serialize)]
type Record = { x : Int }
()
"#;
    let expected = r#"
#[derive(Serialize)]
type Record = { x : Int }
rec let serialize_Record : Serialize Record =
    let { ? } = import! std.result
    let { ValueSerializer, Value, serialize, ? } = import! std.json.ser
    let { map } = import! std.functor
    let { (<*>) } = import! std.applicative
    let { singleton, empty, ? } = import! std.map
    let { (<>) } = import! std.semigroup
    let serialize_ x : Record -> _ =
        match x with
        | { x = x } -> map (\x -> Object (singleton "x" x)) (serialize x)
    { serialize = serialize_ }
()
"#;
    assert_diff!(&format_expr_expanded(expr).unwrap(), expected, "\n", 0);
}

#[test]
fn derive_serialize2() {
    let expr = r#"
#[derive(Serialize)]
type Variant = | Int Int | String String
()
"#;
    let expected = r#"
#[derive(Serialize)]
type Variant =
    | Int Int
    | String String
rec let serialize_Variant : Serialize Variant =
    let { ? } = import! std.result
    let { ValueSerializer, Value, serialize, ? } = import! std.json.ser
    let { map } = import! std.functor
    let { (<*>) } = import! std.applicative
    let { singleton, empty, ? } = import! std.map
    let { (<>) } = import! std.semigroup
    let serialize_ x : Variant -> _ =
        match x with
        | Int arg_0 -> serialize arg_0
        | String arg_0 -> serialize arg_0
    { serialize = serialize_ }
()
"#;
    assert_diff!(&format_expr_expanded(expr).unwrap(), expected, "\n", 0);
}
