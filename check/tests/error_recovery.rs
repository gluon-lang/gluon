extern crate gluon_base as base;

mod support;

use crate::support::*;

use crate::base::ast::Typed;

#[test]
fn partial_let() {
    let src = r#"
/// Alias of `or`
#[infix(left, 3)]
let (<|>) : () = ()
let a
{
    (<|>)
}
        "#;
    let (expr, result) = typecheck_partial_expr(src);
    assert_req!(result.map(|t| t.to_string()), Ok("{ (<|>) : () }"));
    assert_eq!(
        expr.env_type_of(&MockEnv::new()).to_string(),
        "{ (<|>) : () }"
    );
}
