extern crate env_logger;

extern crate base;
extern crate parser;
extern crate check;

use base::ast;
use base::ast::Location;
use base::types::{Type, TcType};

use check::completion::find;

mod functions;
use functions::*;

fn find_type(s: &str, location: Location) -> Result<TcType, ()> {
    let (mut expr, result) = typecheck_expr(s);
    assert!(result.is_ok(), "{}", result.unwrap_err());
    find(&ast::EmptyEnv::new(), &mut expr, location)
}

#[test]
fn identifier() {
    let (mut expr, result) = typecheck_expr("let abc = 1 in abc");
    assert!(result.is_ok(), "{}", result.unwrap_err());
    let result = find(&ast::EmptyEnv::new(), &mut expr, Location { row: 1, column: 16, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
    let result = find(&ast::EmptyEnv::new(), &mut expr, Location { row: 1, column: 17, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
    let result = find(&ast::EmptyEnv::new(), &mut expr, Location { row: 1, column: 18, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
    let result = find(&ast::EmptyEnv::new(), &mut expr, Location { row: 1, column: 19, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
}

#[test]
fn literal_string() {
    let result = find_type(r#" "asd" "#, Location { row: 1, column: 2, absolute: 0 });
    assert_eq!(result, Ok(typ("String")));
}

#[test]
fn in_let() {
    let result = find_type(
r#"
let f x = 1
and g x = "asd"
1
"#, Location { row: 3, column: 15, absolute: 0 });
    assert_eq!(result, Ok(typ("String")));
}

#[test]
fn function_call() {
    let result = find_type(
r#"
let f x = f x
1
"#, Location { row: 2, column: 11, absolute: 0 });
    assert_eq!(result, Ok(Type::function(vec![typ("a0")], typ("a1"))));
}

#[test]
fn binop() {
    let (mut expr, result) = typecheck_expr(
r#"
let (++) l r =
    l #Int+ 1
    r #Float+ 1.0
    l
1 ++ 2.0
"#);
    assert!(result.is_ok(), "{}", result.unwrap_err());
    let result = find(&ast::EmptyEnv::new(), &mut expr, Location { row: 6, column: 4, absolute: 0 });
    assert_eq!(result, Ok(Type::function(vec![typ("Int"), typ("Float")], typ("Int"))));
    let result = find(&ast::EmptyEnv::new(), &mut expr, Location { row: 6, column: 1, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
    let result = find(&ast::EmptyEnv::new(), &mut expr, Location { row: 6, column: 6, absolute: 0 });
    assert_eq!(result, Ok(typ("Float")));
}

#[test]
fn in_record() {
    let result = find_type(
r#"
{
    test = 123,
    s = "asd"
}
"#, Location { row: 3, column: 14, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
}
