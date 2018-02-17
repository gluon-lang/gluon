extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;

mod support;

use base::ast::*;
use parser::{parse_string, ParseErrors};
use support::MockEnv;

fn parse(text: &str) -> Result<SpannedExpr<String>, ParseErrors> {
    parse_string(&mut MockEnv::new(), text).map_err(|(_, err)| err)
}

#[test]
fn unclosed_let() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let y =
    let x = 1
y
"#,
    );

    assert!(result.is_err(), "{}", result.unwrap_err());
}

#[test]
fn sequence_expressions() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
f 1 2
g ""
"#,
    );

    match result {
        Ok(expr) => if let Expr::Block(ref exprs) = expr.value {
            assert_eq!(exprs.len(), 2);
        } else {
            assert!(false, "Expected block, found {:?}", expr);
        },
        Err(err) => assert!(false, "{}", err),
    }
}

#[test]
fn let_in_let_args() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let x =
    let y = 1
    let z = ""
    y + 1
in x
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());
}
#[test]
fn and_on_same_line_as_type() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
type M a = | M a
and M2 a = M a
and HKT m = { x: m Int }
in 1
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn close_brace_on_same_line_as_type() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
type M = {
    x: Int
}

{ M }
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());
}
#[test]
fn record_unindented_fields() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let monad_Test: Monad Test = {
    (>>=) = \ta f ->
        match ta with
            | T a -> f a,
    return = \x -> T x
}
in 1
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

// match clauses cannot be unindented past the enclosing block
#[test]
fn to_much_unindented_case_of() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let test x =
    match x with
  | Some y -> y
  | None -> 0
in test
"#,
    );

    assert!(result.is_err(), "{:?}", result.unwrap());
}

#[test]
fn match_with_alignment() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
match x with
    | Some y ->
        match x with
            | Some y2 -> y2
            | None -> 0
    | None -> 0
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());

    match result.as_ref().unwrap().value {
        Expr::Match(_, ref alts) => assert_eq!(alts.len(), 2),
        ref x => panic!("{:?}", x),
    }
}

#[test]
fn allow_unindented_lambda() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let f = \x ->
    let y = x + 1
    y

f
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn close_lambda_on_implicit_statement() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
\x -> x
1
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());

    match result.unwrap().value {
        Expr::Block(ref exprs) if exprs.len() == 2 => (),
        expr => assert!(false, "{:?}", expr),
    }
}

#[test]
fn if_expr_else_is_block() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let f x = ()
if True then
    1
else
    f 2
    2
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());

    if let Expr::LetBindings(_, ref expr) = result.as_ref().unwrap().value {
        if let Expr::IfElse(_, _, ref if_false) = expr.value {
            if let Expr::Block(_) = if_false.as_ref().value {
                return;
            }
        }
    }

    assert!(false, "{:?}", result.unwrap());
}

#[test]
fn if_else_if_else() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
if True then
    1
else if True then
    2
else
    3
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn block_match() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
match True with
| True -> 1
| False -> 0
2
"#,
    );

    assert!(result.is_ok(), "{}", result.unwrap_err());

    if let Expr::Block(ref exprs) = result.as_ref().unwrap().value {
        assert_eq!(2, exprs.len());
        return;
    }

    assert!(false, "{:?}", result.unwrap());
}
