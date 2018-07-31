extern crate gluon;
extern crate gluon_doc as doc;
extern crate handlebars;

use gluon::check::metadata::metadata;
use gluon::{Compiler, RootedThread};

fn new_vm() -> RootedThread {
    ::gluon::VmBuilder::new()
        .import_paths(Some(vec!["..".into()]))
        .build()
}

fn doc_check(module: &str, expected: doc::Record) {
    let vm = new_vm();
    let (expr, typ) = Compiler::new()
        .typecheck_str(&vm, "basic", module, None)
        .unwrap();
    let (meta, _) = metadata(&*vm.get_env(), &expr);

    let out = doc::record("basic", &typ, &meta);
    assert_eq!(out, expected,);
}

#[test]
fn basic() {
    let module = r#"
/// This is the test function
let test x = x
{ test }
"#;
    doc_check(
        module,
        doc::Record {
            types: Vec::new(),
            values: vec![doc::Field {
                name: "test".to_string(),
                args: vec![doc::Argument {
                    implicit: false,
                    name: "x".to_string(),
                }],
                typ: handlebars::html_escape("forall a . a -> a"),
                comment: "This is the test function".to_string(),
            }],
        },
    );
}

#[test]
fn doc_hidden() {
    let module = r#"
#[doc(hidden)]
type Test = Int
#[doc(hidden)]
let test x = x
{ Test, test }
"#;
    doc_check(
        module,
        doc::Record {
            types: Vec::new(),
            values: vec![],
        },
    );
}
