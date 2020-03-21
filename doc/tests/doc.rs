use std::{fs, path::Path};

use {itertools::Itertools, rayon::prelude::*};

use gluon_doc as doc;

use gluon::{check::metadata::metadata, RootedThread, ThreadExt};

fn new_vm() -> RootedThread {
    ::gluon::VmBuilder::new()
        .import_paths(Some(vec!["..".into()]))
        .build()
}

fn doc_check(module: &str, expected: doc::Record) {
    let vm = new_vm();
    let (expr, typ) = vm.typecheck_str("basic", module, None).unwrap();
    let (meta, _) = metadata(&vm.get_env(), &expr.expr());

    let out = doc::record(
        "basic",
        &typ,
        &Default::default(),
        &<() as gluon::base::source::Source>::new(""),
        &meta,
    );
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
                attributes: "".to_string(),
                comment: "This is the test function".to_string(),
                definition_line: None,
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

#[test]
fn check_links() {
    let _ = env_logger::try_init();

    let out = Path::new("../target/doc_test");
    if out.exists() {
        fs::remove_dir_all(out).unwrap_or_else(|err| panic!("{}", err));
    }
    doc::generate_for_path(&new_vm(), "../std", out).unwrap_or_else(|err| panic!("{}", err));

    let out = fs::canonicalize(out).unwrap();
    let errors = cargo_deadlinks::unavailable_urls(
        &out,
        &cargo_deadlinks::CheckContext { check_http: true },
    )
    .collect::<Vec<_>>();

    assert!(errors.is_empty(), "{}", errors.iter().format("\n"));
}
