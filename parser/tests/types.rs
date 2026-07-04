extern crate gluon_base as base;
extern crate gluon_parser as parser;

use crate::base::{ast::Expr, types::TypeContext};
use crate::support::{clear_span, parse, typ};

mod support;

#[test]
fn function_type() {
    let _ = env_logger::try_init();

    let input = "let _ : Int -> Float -> String = 1 in 1";
    let expr = parse(input).unwrap_or_else(|err| panic!("{}", err.1));
    let mut expr = clear_span(expr);
    expr.with_arena(|arena, expr| {
        let mut arena = arena.borrow();
        match &expr.value {
            Expr::LetBindings(bindings, _) => {
                assert_eq!(
                    bindings[0].typ.as_ref(),
                    Some(&arena.function(
                        vec![typ(arena, "Int"), typ(arena, "Float")],
                        typ(arena, "String"),
                    ),)
                );
            }
            _ => panic!("Expected let"),
        }
    });
}
