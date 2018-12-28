extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;

use crate::base::ast::Expr;
use crate::base::types::Type;
use crate::support::{clear_span, parse, typ};

mod support;

#[test]
fn function_type() {
    let _ = env_logger::try_init();

    let input = "let _ : Int -> Float -> String = 1 in 1";
    let expr = parse(input).unwrap_or_else(|err| panic!("{}", err.1));
    match clear_span(expr).value {
        Expr::LetBindings(ref bindings, _) => {
            assert_eq!(
                bindings[0].typ,
                Some(Type::function(
                    vec![typ("Int"), typ("Float")],
                    typ("String"),
                ),)
            );
        }
        _ => panic!("Expected let"),
    }
}
