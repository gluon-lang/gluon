use gluon::{
    vm::api::{FunctionRef, Hole, OpaqueValue},
    Thread, ThreadExt,
};

use crate::support::make_vm;

#[macro_use]
mod support;

test_expr! { polymorphic_field_access,
r#"
let f record = record.x
f { y = 1, x = 123 }
"#,
123
}

test_expr! { polymorphic_record_unpack,
r#"
let f record =
    let { x, y } = record
    x #Int- y
f { y = 1, z = 0, x = 123 }
"#,
122
}

#[test]
fn polymorphic_record_access_from_child_thread() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();
    let child = vm.new_thread().unwrap();

    vm.run_expr::<OpaqueValue<&Thread, Hole>>("", "import! std.function")
        .unwrap();

    let result = child.run_expr::<FunctionRef<fn(i32) -> i32>>(
        "test",
        r#"
        let function = import! std.function
        let f r = r.id in
        f function
        "#,
    );
    assert!(result.is_ok(), "{}", result.err().unwrap());
    assert_eq!(result.unwrap().0.call(123), Ok(123));
}

// FIXME Add this test back when order no longer matters for fields
// test_expr! { prelude different_order_on_fields,
// r#"
// let x =
// if False then
// { x = 1, y = "a" }
// else
// { y = "b", x = 2 }
// x.y
// "#,
// String::from("a")
// }
//
