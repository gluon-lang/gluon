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
