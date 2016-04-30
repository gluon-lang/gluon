extern crate env_logger;
#[macro_use]
extern crate log;

extern crate base;
extern crate parser;
extern crate combine;

use combine::ParseError;
use combine::primitives::{Error, Info, SourcePosition};
use base::ast::*;
use parser::parse_string;
use parser::lexer::Token;

fn parse(text: &str) -> Result<LExpr<String>, ::parser::Error> {
    parse_string(None, &mut EmptyEnv::new(), text)
}

#[test]
fn unclosed_let() {
    let _ = ::env_logger::init();
    let text = r#"
let y =
    let x = 1
y
"#;
    let result = parse(text);
    assert!(result.is_err(), "{}", result.unwrap_err());
}

#[test]
fn sequence_expressions() {
    let _ = ::env_logger::init();
    let text = r#"
f 1 2
g ""
"#;
    let result = parse(text);
    match result {
        Ok(expr) => {
            match expr.value {
                Expr::Block(ref exprs) => {
                    assert_eq!(exprs.len(), 2);
                }
                _ => assert!(false, "Expected block, found {:?}", expr),
            }
        }
        Err(err) => assert!(false, "{}", err),
    }
}

#[test]
fn wrong_indent_expression() {
    let _ = ::env_logger::init();
    let text = r#"
let y =
    let x = 1
    x
   2
y
"#;
    let result = parse(text);
    assert_eq!(result, Err(ParseError {
        position: SourcePosition { column: 4, line: 5 },
        errors: vec![Error::Unexpected(Info::Token(Token::Integer(2))),
                     Error::Expected("`in` or an expression in the same column as the `let`".into())],
    }));
}

#[test]
fn let_in_let_args() {
    let _ = ::env_logger::init();
    let text = r#"
let x =
    let y = 1
    let z = ""
    y + 1
in x
"#;
    let result = parse(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}
#[test]
fn and_on_same_line_as_type() {
    let _ = ::env_logger::init();
    let text = r#"
type M a = | M a
and M2 a = M a
and HKT m = { x: m Int }
in 1
"#;
    let result = parse(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn close_brace_on_same_line_as_type() {
    let _ = ::env_logger::init();
    let text = r#"
type M = {
    x: Int
}

{ M }
"#;
    let result = parse(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}
#[test]
fn record_unindented_fields() {
    let _ = ::env_logger::init();
    let text = r#"
let monad_Test: Monad Test = {
    (>>=) = \ta f ->
        match ta with
            | T a -> f a,
    return = \x -> T x
}
in 1
"#;
    let result = parse(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

// match clauses cannot be unindented past the enclosing block
#[test]
fn to_much_unindented_case_of() {
    let _ = ::env_logger::init();
    let text = r#"
let test x =
    match x with
  | Some y -> y
  | None -> 0
in test
"#;
    let result = parse(text);
    assert!(result.is_err(), "{:?}", result.unwrap());
}

#[test]
fn match_with_alignment() {
    let _ = ::env_logger::init();
    let text = r#"
match x with
    | Some y ->
        match x with
            | Some y2 -> y2
            | None -> 0
    | None -> 0
"#;
    let result = parse(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
    match result.as_ref().unwrap().value {
        Expr::Match(_, ref alts) => assert_eq!(alts.len(), 2),
        ref x => panic!("{:?}", x)
    }
}

#[test]
fn allow_unindented_lambda() {
    let _ = ::env_logger::init();
    let text = r#"
let f = \x ->
    let y = x + 1
    y

f
"#;
    let result = parse(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn close_lambda_on_implicit_statement() {
    let _ = ::env_logger::init();
    let text = r#"
\x -> x
1
"#;
    let result = parse(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
    match result.unwrap().value {
        Expr::Block(ref exprs) if exprs.len() == 2 => (),
        expr => assert!(false, "{:?}", expr),
    }
}
