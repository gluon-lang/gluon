#![cfg(feature = "serialization")]
extern crate env_logger;
#[macro_use]
extern crate serde_derive;

use gluon::{
    base::{
        symbol::Symbol,
        types::{ArcType, Field, Type},
    },
    new_vm,
    vm::{
        api::{
            de::{self, De},
            Getable, Hole, OpaqueValue, VmType,
        },
        thread::Thread,
    },
    ThreadExt,
};

#[test]
fn bool() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let (De(b), _) = thread
        .run_expr::<De<bool>>("test", r#"let { Bool } = import! std.bool in True"#)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(b, true);
}

#[derive(Debug, PartialEq, Deserialize)]
struct Record {
    test: i32,
    string: String,
}

impl VmType for Record {
    type Type = Self;

    fn make_type(thread: &Thread) -> ArcType {
        Type::poly_record(
            vec![],
            vec![
                Field {
                    name: Symbol::from("test"),
                    typ: i32::make_type(thread),
                },
                Field {
                    name: Symbol::from("string"),
                    typ: str::make_type(thread),
                },
            ],
            Type::hole(),
        )
    }
}

#[test]
fn option() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let (De(opt), _) = thread
        .run_expr::<De<Option<f64>>>(
            "test",
            r#"let { Option } = import! std.option in Some 1.0 "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(opt, Some(1.0));
}

#[test]
fn partial_record() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    let (De(record), _) = thread
        .run_expr::<De<Record>>("test", r#" { test = 1, extra = 1.0, string = "test", } "#)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(
        record,
        Record {
            test: 1,
            string: "test".to_string(),
        }
    );
}

#[derive(Debug, PartialEq, Deserialize)]
struct OptionalFieldRecord {
    test: Option<i32>,
}

impl VmType for OptionalFieldRecord {
    type Type = Self;

    fn make_type(thread: &Thread) -> ArcType {
        Type::poly_record(
            vec![],
            vec![Field {
                name: Symbol::from("test"),
                typ: Option::<i32>::make_type(thread),
            }],
            Type::hole(),
        )
    }
}

#[test]
fn optional_field() {
    let _ = env_logger::try_init();

    let thread = new_vm();

    let (value, _) = thread
        .run_expr::<OpaqueValue<&Thread, Hole>>("test", r#" { } "#)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(
        De::<OptionalFieldRecord>::from_value(&thread, value.get_variant()).0,
        OptionalFieldRecord { test: None }
    );

    let (value, _) = thread
        .run_expr::<OpaqueValue<&Thread, Hole>>(
            "test",
            r#"let { Option } = import! std.option in { test = Some 2 } "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(
        De::<OptionalFieldRecord>::from_value(&thread, value.get_variant()).0,
        OptionalFieldRecord { test: Some(2) }
    );

    let (value, _) = thread
        .run_expr::<OpaqueValue<&Thread, Hole>>("test", r#" { test = 1 } "#)
        .unwrap_or_else(|err| panic!("{}", err));

    let typ = Type::poly_record(
        vec![],
        vec![Field {
            name: Symbol::from("test"),
            typ: i32::make_type(&thread),
        }],
        Type::hole(),
    );
    assert_eq!(
        de::from_value(&thread, value.get_variant(), &typ).ok(),
        Some(OptionalFieldRecord { test: Some(1) })
    );
}

#[derive(Debug, PartialEq, Deserialize)]
enum Enum {
    A(String),
    B { string: String, test: f64 },
    C(i32, i32),
}

impl VmType for Enum {
    type Type = Self;

    fn make_type(thread: &Thread) -> ArcType {
        thread.find_type_info("test.Enum").unwrap().into_type()
    }
}

#[test]
fn enum_() {
    let _ = env_logger::try_init();

    let thread = new_vm();
    thread.get_database_mut().set_implicit_prelude(false);
    thread
        .load_script(
            "test",
            r#" type Enum = | A String | B String Float | C Int Int in { Enum } "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let (De(enum_), _) = thread
        .run_expr::<De<Enum>>("test", r#" let { Enum } = import! "test" in A "abc" "#)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(enum_, Enum::A("abc".to_string()));

    let (De(enum_), _) = thread
        .run_expr::<De<Enum>>("test", r#" let { Enum } = import! "test" in C 0 1 "#)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(enum_, Enum::C(0, 1));
}
