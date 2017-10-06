extern crate env_logger;

extern crate gluon;

#[macro_use]
mod support;

use gluon::Compiler;
use support::*;

test_expr!{ prelude match_on_bool,
r#"
let { Bool } = import! "std/bool.glu"
match True with
| False -> 10
| True -> 11
"#,
11i32
}

#[test]
fn non_exhaustive_pattern() {
    let _ = ::env_logger::init();
    let text = r"
type AB = | A | B in
match A with
| B -> True
";
    let mut vm = make_vm();
    let result = Compiler::new()
        .run_expr_async::<bool>(&mut vm, "<top>", text)
        .sync_or_error();
    assert!(result.is_err());
}

test_expr!{ match_record_pattern,
r#"
let string_prim = import! "string_prim"
match { x = 1, y = "abc" } with
| { x, y = z } -> x #Int+ string_prim.len z
"#,
4i32
}

test_expr!{ match_stack,
r#"
let string_prim = import! "string_prim"
1 #Int+ (match string_prim with
         | { len } -> len "abc")
"#,
4i32
}

test_expr!{ let_record_pattern,
r#"
let string_prim = import! "string_prim"
let (+) x y = x #Int+ y
in
let a = { x = 10, y = "abc" }
in
let {x, y = z} = a
in x + string_prim.len z
"#,
13i32
}

test_expr!{ partial_record_pattern,
r#"
type A = { x: Int, y: Float } in
let x = { x = 1, y = 2.0 }
in match x with
| { y } -> y
"#,
2.0f64
}

test_expr!{ record_let_adjust,
r#"
let x = \z -> let { x, y } = { x = 1, y = 2 } in z in
let a = 3
in a
"#,
3i32
}

test_expr!{ match_on_zero_argument_variant,
r#"
type Test = | A Int | B
match B with
| A x -> x
| B -> 0
"#,
0i32
}

// Without a slide instruction after the alternatives code this code would try to call `x 1`
// instead of `id 1`
test_expr!{ slide_down_case_alternative,
r#"
type Test = | Test Int
let id x = x
id (match Test 0 with
    | Test x -> 1)
"#,
1i32
}

test_expr!{ nested_pattern,
r#"
type Option a = | Some a | None
match Some (Some 123) with
| None -> 0
| Some None -> 1
| Some (Some x) -> x
"#,
123i32
}

test_expr!{ nested_pattern2,
r#"
type Option a = | Some a | None
match Some None with
| None -> 0
| Some None -> 1
| Some (Some x) -> x
"#,
1i32
}

test_expr!{ nested_record_pattern,
r#"
type Test a = | A a | B
match { x = A 1 } with
| { x = A y } -> y
| { x = B } -> 100
"#,
1i32
}

test_expr!{ nested_record_pattern2,
r#"
type Test a = | A a | B
match { x = B } with
| { x = A y } -> y
| { x = B } -> 100
"#,
100i32
}

test_expr!{ access_only_a_few_fields_from_large_record,
r#"
let record = { a = 0, b = 1, c = 2, d = 3, e = 4, f = 5, g = 6,
               h = 7, i = 8, j = 9, k = 10, l = 11, m = 12 }
let { a } = record
let { i, m } = record

a #Int+ i #Int+ m
"#,
20i32
}
