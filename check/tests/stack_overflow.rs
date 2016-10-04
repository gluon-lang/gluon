#[macro_use]
extern crate collect_mac;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;

mod support;

#[test]
fn dont_stack_overflow_on_let_bindings() {
    let text = r#"
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in
let _ = 1
in 1
"#;
    support::typecheck(text).unwrap();
}
