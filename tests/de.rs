extern crate env_logger;
#[macro_use]
extern crate serde_derive;

extern crate gluon;
#[macro_use]
extern crate gluon_vm;

use gluon::base::types::ArcType;
use gluon::vm::api::VmType;
use gluon::vm::api::de::De;
use gluon::vm::thread::Thread;
use gluon::{Compiler, new_vm};

#[test]
fn bool() {
    let _ = env_logger::init();

    let thread = new_vm();
    let (De(b), _) = Compiler::new()
        .run_expr::<De<bool>>(&thread, "test", "True")
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
        fn type_of<T: VmType>(thread: &Thread, _: T) -> ArcType {
            T::make_type(thread)
        }
        type_of(
            thread,
            record!{
            test => 0,
            string => ""
        },
        )
    }
}

#[test]
fn record() {
    let _ = env_logger::init();

    let thread = new_vm();
    let (De(record), _) = Compiler::new()
        .run_expr::<De<Record>>(&thread, "test", r#" { test = 1, string = "test" } "#)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(
        record,
        Record {
            test: 1,
            string: "test".to_string(),
        }
    );
}
