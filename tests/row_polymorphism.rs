extern crate env_logger;
extern crate gluon;

#[macro_use]
mod support;

use support::*;

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
