extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;

use base::types::{Field, Type, TcType};

mod support;
use support::{intern, typ};

macro_rules! assert_pass {
    ($e: expr) => {{
        if !$e.is_ok() {
            panic!("assert_pass: {}", $e.unwrap_err());
        }
    }};
}

#[test]
fn if_else_different_records() {
    let text = r#"
if True then
    { y = "" }
else
    { x = 1 }
"#;
    let result = support::typecheck(text);

    assert_eq!(result,
               Ok(TcType::from(Type::Record {
                   types: vec![],
                   row: Type::extend_row(vec![Field {
                                                  name: intern("x"),
                                                  typ: typ("Int"),
                                              },
                                              Field {
                                                  name: intern("y"),
                                                  typ: typ("String"),
                                              }],
                                         typ("a")),
               })));
}


#[test]
fn infer_fields() {
    let text = r#"
let f vec = vec.x #Int+ vec.y
f
"#;
    let result = support::typecheck(text);
    let record = TcType::from(Type::Record {
        types: vec![],
        row: Type::extend_row(vec![Field {
                                       name: intern("x"),
                                       typ: typ("Int"),
                                   },
                                   Field {
                                       name: intern("y"),
                                       typ: typ("Int"),
                                   }],
                              typ("a")),
    });
    assert_eq!(result, Ok(Type::function(vec![record], typ("Int"))));
}

#[test]
fn missing_field() {
    let text = r#"
let f vec = vec.x #Int+ vec.y
f { x = 1 }
"#;
    let result = support::typecheck(text);

    assert!(result.is_err());
}
