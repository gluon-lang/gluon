extern crate env_logger;
extern crate gluon_base as base;
extern crate gluon_parser as parser;

#[macro_use]
mod support;

use crate::support::*;

#[test]
fn any_tokens() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[test(ident "string" 42 = 'a' + )]
let (+) x y = error ""
{ }
"#;
    parse_clear_span!(text);
}

#[test]
fn bindings() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[infix(left, 6)]
let (+) x y = error ""
#[implicit]
type Test = Int

{
    #[abc()]
    Test,
    #[test]
    t = \_ -> True
}
"#;
    parse_clear_span!(text);
}
