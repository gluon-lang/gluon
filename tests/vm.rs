extern crate env_logger;
extern crate gluon;

#[macro_use]
mod support;

use support::*;

use gluon::base::pos::BytePos;
use gluon::base::types::Type;
use gluon::check::completion;
use gluon::vm::api::{FunctionRef, Hole, OpaqueValue, ValueRef, IO};
use gluon::vm::thread::{Thread, ThreadInternal};
use gluon::vm::internal::Value;
use gluon::vm::internal::Value::{Float, Int};
use gluon::vm::stack::{StackFrame, State};
use gluon::vm::channel::Sender;
use gluon::{Compiler, Error};


test_expr!{ pass_function_value,
r"
let lazy: () -> Int = \x -> 42 in
let test: (() -> Int) -> Int = \f -> f () #Int+ 10
in test lazy
",
52i32
}

test_expr!{ lambda,
r"
let y = 100 in
let f = \x -> y #Int+ x #Int+ 1
in f(22)
",
123i32
}

test_expr!{ add_operator,
r"
let (+) = \x y -> x #Int+ y in 1 + 2 + 3
",
6i32
}
test_expr!{ divide_int,
r" 120 #Int/ 4
",
30i32
}

test_expr!{ divide_float,
r" 120.0 #Float/ 4.0
",
30.0f64
}

#[test]
fn record() {
    let _ = ::env_logger::init();
    let text = r"
{ x = 0, y = 1.0, z = {} }
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    assert_eq!(
        value.get_ref(),
        vm.context()
            .new_record(&vm, 0, &mut [Int(0), Float(1.0), Value::Tag(0)])
            .unwrap()
    );
}

#[test]
fn add_record() {
    let _ = ::env_logger::init();
    let text = r"
type T = { x: Int, y: Int } in
let add = \l r -> { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
add { x = 0, y = 1 } { x = 1, y = 1 }
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    assert_eq!(
        value.get_ref(),
        vm.context()
            .new_record(&vm, 0, &mut [Int(1), Int(2)])
            .unwrap()
    );
}
#[test]
fn script() {
    let _ = ::env_logger::init();
    let text = r"
type T = { x: Int, y: Int } in
let add l r = { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
let sub l r = { x = l.x #Int- r.x, y = l.y #Int- r.y } in
{ T, add, sub }
";
    let mut vm = make_vm();
    load_script(&mut vm, "vec", text).unwrap_or_else(|err| panic!("{}", err));

    let script = r#"
let { T, add, sub } = vec
in add { x = 10, y = 5 } { x = 1, y = 2 }
"#;
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&mut vm, script);
    match value.get_ref() {
        ValueRef::Data(data) => {
            assert_eq!(data.get(0), Some(ValueRef::Int(11)));
            assert_eq!(data.get(1), Some(ValueRef::Int(7)));
        }
        _ => panic!(),
    }
}
#[test]
fn adt() {
    let _ = ::env_logger::init();
    let text = r"
type Option a = | None | Some a
in Some 1
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    assert_eq!(
        value.get_ref(),
        vm.context().new_data(&vm, 1, &mut [Int(1)]).unwrap()
    );
}


test_expr!{ recursive_function,
r"
let fib x = if x #Int< 3
        then 1
        else fib (x #Int- 1) #Int+ fib (x #Int- 2)
in fib 7
",
13i32
}

test_expr!{ mutually_recursive_function,
r"
let f x = if x #Int< 0
      then x
      else g x
and g x = f (x #Int- 1)
in g 3
",
-1
}

test_expr!{ no_capture_self_function,
r"
let x = 2 in
let f y = x
in f 4
",
2i32
}

#[test]
fn insert_stack_slice() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    let mut context = vm.context();
    let mut stack = StackFrame::current(&mut context.stack);
    stack.push(Int(0));
    stack.insert_slice(0, &[Int(2), Int(1)]);
    assert_eq!(&stack[..], [Int(2), Int(1), Int(0)]);
    stack.enter_scope(2, State::Unknown);
    stack.insert_slice(1, &[Int(10)]);
    assert_eq!(&stack[..], [Int(1), Int(10), Int(0)]);
    stack.insert_slice(1, &[]);
    assert_eq!(&stack[..], [Int(1), Int(10), Int(0)]);
    stack.insert_slice(2, &[Int(4), Int(5), Int(6)]);
    assert_eq!(
        &stack[..],
        [Int(1), Int(10), Int(4), Int(5), Int(6), Int(0)]
    );
}


test_expr!{ primitive_char_eq,
r"
'a' #Char== 'a'
",
true
}

test_expr!{ primitive_char_lt,
r"
'a' #Char< 'a'
",
false
}

test_expr!{ primitive_byte_arithmetic,
r"
let x = 100b #Byte+ 13b
x #Byte* 2b #Byte/ 3b
",
75u8
}

test_expr!{ primitive_byte_eq,
r"
100b #Byte== 100b
",
true
}

test_expr!{ primitive_byte_lt,
r"
100b #Byte< 100b
",
false
}

test_expr!{ partial_application,
r"
let f x y = x #Int+ y in
let g = f 10
in g 2 #Int+ g 3
",
25i32
}

test_expr!{ partial_application2,
r"
let f x y z = x #Int+ y #Int+ z in
let g = f 10 in
let h = g 20
in h 2 #Int+ g 10 3
",
55i32
}

test_expr!{ to_many_args_application,
r"
let f x = \y -> x #Int+ y in
let g = f 20
in f 10 2 #Int+ g 3
",
35i32
}

test_expr!{ to_many_args_partial_application_twice,
r"
let f x = \y z -> x #Int+ y #Int+ z in
let g = f 20 5
in f 10 2 1 #Int+ g 2
",
40i32
}

test_expr!{ excess_arguments_larger_than_stack,
r#"
let f a b c = c
(\x -> f) 1 2 3 4
"#,
4i32
}

test_expr!{ no_io_eval,
r#"
let x = io_flat_map (\x -> error "NOOOOOOOO") (io.println "1")
in { x }
"#
}

test_expr!{ char,
r#"
'a'
"#,
'a'
}

test_expr!{ any zero_argument_variant_is_int,
r#"
type Test = | A Int | B
B
"#,
Value::Tag(1)
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

test_expr!{ any marshalled_option_none_is_int,
r#"
string_prim.find "a" "b"
"#,
Value::Tag(0)
}

test_expr!{ any marshalled_ordering_is_int,
r#"
string_prim.compare "a" "b"
"#,
Value::Tag(0)
}

test_expr!{ prelude match_on_bool,
r#"
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
match { x = 1, y = "abc" } with
| { x, y = z } -> x #Int+ string_prim.len z
"#,
4i32
}

test_expr!{ match_stack,
r#"
1 #Int+ (match string_prim with
         | { len } -> len "abc")
"#,
4i32
}

test_expr!{ let_record_pattern,
r#"
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

test_expr!{ unit_expr,
r#"
let x = ()
and y = 1
in y
"#,
1i32
}

test_expr!{ return_unit,
"()",
()
}

test_expr!{ let_not_in_tail_position,
r#"
1 #Int+ (let x = 2 in x)
"#,
3i32
}

test_expr!{ field_access_not_in_tail_position,
r#"
let id x = x
in (id { x = 1 }).x
"#,
1i32
}

test_expr!{ module_function,
r#"let x = string_prim.len "test" in x"#,
4i32
}

test_expr!{ io_print,
r#"io.print "123" "#
}

test_expr!{ array,
r#"
let arr = [1,2,3]

array.index arr 0 #Int== 1
    && array.len arr #Int== 3
    && array.len (array.append arr arr) #Int== array.len arr #Int* 2"#,
true
}

test_expr!{ array_byte,
r#"
let arr = [1b,2b,3b]

let b = array.index arr 2 #Byte== 3b && array.len arr #Int== 3
let arr2 = array.append arr arr
b && array.len arr2 #Int== array.len arr #Int* 2
  && array.index arr2 1 #Byte== array.index arr2 4
"#,
true
}

test_expr!{ array_float,
r#"
let arr = [1.0,2.0,3.0]

let b = array.index arr 2 #Float== 3.0 && array.len arr #Int== 3
let arr2 = array.append arr arr
b && array.len arr2 #Int== array.len arr #Int* 2
  && array.index arr2 1 #Float== array.index arr2 4
"#,
true
}

test_expr!{ array_data,
r#"
let arr = [{x = 1, y = "a" }, { x = 2, y = "b" }]

let b = (array.index arr 1).x #Int== 2 && array.len arr #Int== 2
let arr2 = array.append arr arr
b && array.len arr2 #Int== array.len arr #Int* 2
"#,
true
}

test_expr!{ array_array,
r#"
let arr = [[], [1], [2, 3]]

let b = array.len (array.index arr 1) #Int== 1 && array.len arr #Int== 3
let arr2 = array.append arr arr
b && array.len arr2 #Int== array.len arr #Int* 2
"#,
true
}

test_expr!{ prelude true_branch_not_affected_by_false_branch,
r#"
if True then
    let x = 1
    x
else
    0
"#,
1i32
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

test_expr!{ prelude and_operator_stack,
r#"
let b = True && True
let b2 = False
b
"#,
true
}

test_expr!{ prelude or_operator_stack,
r#"
let b = False || True
let b2 = False
b
"#,
true
}

// Test that empty variants are handled correctly in arrays
test_expr!{ array_empty_variant,
r#"
type Test = | Empty | Some Int
let arr = [Empty, Some 1]
match array.index arr 0 with
| Empty -> 0
| Some x -> x
"#,
0i32
}

// Test that array append handles array types correctly
test_expr!{ array_empty_append,
r#"
type Test = | Empty | Some Int
let arr = array.append [] [Empty, Some 1]
match array.index arr 0 with
| Empty -> 0
| Some x -> x
"#,
0i32
}

test_expr!{ overload_resolution_with_record_pattern,
r#"
let f =
    \x g ->
        let { x } = g x
        x
f 0 (\r -> { x = r #Int+ 1 })
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


#[test]
fn overloaded_bindings() {
    let _ = ::env_logger::init();
    let text = r#"
let (+) x y = x #Int+ y
in
let (+) x y = x #Float+ y
in
{ x = 1 + 2, y = 1.0 + 2.0 }
"#;
    let vm = make_vm();
    let result = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    assert_eq!(
        result.get_ref(),
        vm.context()
            .new_record(&vm, 0, &mut [Int(3), Float(3.0)])
            .unwrap()
    );
}

test_expr!{ through_overloaded_alias,
r#"
type Test a = { id : a -> a }
in
let test_Int: Test Int = { id = \x -> 0 }
in
let test_String: Test String = { id = \x -> "" }
in
let { id } = test_Int
in
let { id } = test_String
in id 1
"#,
0i32
}

#[test]
fn run_expr_int() {
    let _ = ::env_logger::init();

    let text = r#"io.run_expr "123" "#;
    let mut vm = make_vm();
    let (result, _) = Compiler::new()
        .run_io_expr_async::<IO<String>>(&mut vm, "<top>", text)
        .sync_or_error()
        .unwrap();
    match result {
        IO::Value(result) => {
            let expected = "123 : Int";
            assert_eq!(result, expected);
        }
        IO::Exception(err) => panic!("{}", err),
    }
}

test_expr!{ io run_expr_io,
r#"io_flat_map (\x -> io_wrap 100) (io.run_expr "io.print \"123\" ") "#,
100i32
}

#[test]
fn rename_types_after_binding() {
    let _ = ::env_logger::init();

    let text = r#"
let list  = import! "std/list.glu"
in
let { List } = list
and { (==) }: Eq (List Int) = list.eq { (==) }
in Cons 1 Nil == Nil
"#;
    let mut vm = make_vm();
    let (result, _) = Compiler::new()
        .run_expr_async::<bool>(&mut vm, "<top>", text)
        .sync_or_error()
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = false;

    assert_eq!(result, expected);
}

#[test]
fn test_implicit_prelude() {
    let _ = ::env_logger::init();
    let text = r#"1.0 + 3.0 - 2.0"#;
    let mut vm = make_vm();
    Compiler::new()
        .run_expr_async::<OpaqueValue<&Thread, Hole>>(&mut vm, "<top>", text)
        .sync_or_error()
        .unwrap_or_else(|err| panic!("{}", err));
}

#[test]
fn access_field_through_vm() {
    let _ = ::env_logger::init();
    let text = r#" { x = 0, inner = { y = 1.0 } } "#;
    let mut vm = make_vm();
    load_script(&mut vm, "test", text).unwrap_or_else(|err| panic!("{}", err));
    let test_x = vm.get_global("test.x");
    assert_eq!(test_x, Ok(0));
    let test_inner_y = vm.get_global("test.inner.y");
    assert_eq!(test_inner_y, Ok(1.0));
}

#[test]
fn access_operator_without_parentheses() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    Compiler::new()
        .run_expr_async::<OpaqueValue<&Thread, Hole>>(
            &vm,
            "example",
            r#" import! "std/prelude.glu" "#,
        )
        .sync_or_error()
        .unwrap();
    let result: Result<FunctionRef<fn(i32, i32) -> i32>, _> =
        vm.get_global("std.prelude.num_Int.+");
    assert!(result.is_err());
}

#[test]
fn get_binding_with_alias_type() {
    let _ = ::env_logger::init();
    let text = r#"
        type Test = Int
        let x: Test = 0
        { Test, x }
        "#;
    let mut vm = make_vm();
    load_script(&mut vm, "test", text).unwrap_or_else(|err| panic!("{}", err));
    let test_x = vm.get_global("test.x");
    assert_eq!(test_x, Ok(0));
}

#[test]
fn get_binding_with_generic_params() {
    let _ = ::env_logger::init();

    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! "std/prelude.glu" "#);
    let mut id: FunctionRef<fn(String) -> String> = vm.get_global("std.prelude.id")
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(id.call("test".to_string()), Ok("test".to_string()));
}

#[test]
fn test_prelude() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! "std/prelude.glu" "#);
}

#[test]
fn access_types_by_path() {
    let _ = ::env_logger::init();

    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! "std/option.glu" "#);
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! "std/result.glu" "#);

    assert!(vm.find_type_info("std.option.Option").is_ok());
    assert!(vm.find_type_info("std.result.Result").is_ok());

    let text = r#" type T a = | T a in { x = 0, inner = { T, y = 1.0 } } "#;
    load_script(&vm, "test", text).unwrap_or_else(|err| panic!("{}", err));
    let result = vm.find_type_info("test.inner.T");
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn opaque_value_type_mismatch() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    let expr = r#"
let { sender, receiver } = channel 0
send sender 1
sender
"#;
    let result = Compiler::new()
        .implicit_prelude(false)
        .run_expr_async::<OpaqueValue<&Thread, Sender<f64>>>(&vm, "<top>", expr)
        .sync_or_error();
    match result {
        Err(Error::Typecheck(..)) => (),
        Err(err) => panic!("Unexpected error `{}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}

#[test]
fn invalid_string_slice_dont_panic() {
    let _ = ::env_logger::init();
    let text = r#"
let string = import! "std/string.glu"
let s = "åäö"
string.slice s 1 (string.len s)
"#;
    let mut vm = make_vm();
    let result = Compiler::new()
        .run_expr_async::<String>(&mut vm, "<top>", text)
        .sync_or_error();
    match result {
        Err(Error::VM(..)) => (),
        Err(err) => panic!("Unexpected error `{}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}

#[test]
fn dont_execute_io_in_run_expr_async() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    let expr = r#"
let prelude  = import! "std/prelude.glu"
let { wrap } = prelude.applicative_IO
wrap 123
"#;
    let value = Compiler::new()
        .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, "example", expr)
        .sync_or_error()
        .unwrap_or_else(|err| panic!("{}", err));
    assert!(
        value.0.get_ref() != Value::Int(123),
        "Unexpected {:?}",
        value.0
    );
}

#[test]
fn partially_applied_constructor_is_lambda() {
    let _ = ::env_logger::init();
    let vm = make_vm();

    let result = Compiler::new().run_expr::<FunctionRef<fn(i32) -> Option<i32>>>(
        &vm,
        "test",
        r#"let { Option } = import! "std/option.glu" in Some"#,
    );
    assert!(result.is_ok(), "{}", result.err().unwrap());
    assert_eq!(result.unwrap().0.call(123), Ok(Some(123)));
}

#[test]
fn stacktrace() {
    use gluon::vm::stack::StacktraceFrame;
    let _ = ::env_logger::init();
    let text = r#"
let end _ = 1 + error "test"
let f x =
    if x == 0 then
        3 + end ()
    else
        1 + g (x - 1)
and g x = 1 + f (x / 2)
g 10
"#;
    let mut vm = make_vm();
    let result = Compiler::new()
        .run_expr_async::<i32>(&mut vm, "<top>", text)
        .sync_or_error();
    match result {
        Err(Error::VM(..)) => {
            let stacktrace = vm.context().stack.stacktrace(1);
            let g = stacktrace.frames[0].as_ref().unwrap().name.clone();
            let f = stacktrace.frames[1].as_ref().unwrap().name.clone();
            let end = stacktrace.frames[6].as_ref().unwrap().name.clone();
            assert_eq!(
                stacktrace.frames,
                vec![
                    // Removed due to being a tail call
                    // Some(StacktraceFrame { name: f.clone(), line: 9 }),
                    Some(StacktraceFrame {
                        name: g.clone(),
                        line: 7.into(),
                    }),
                    Some(StacktraceFrame {
                        name: f.clone(),
                        line: 6.into(),
                    }),
                    Some(StacktraceFrame {
                        name: g.clone(),
                        line: 7.into(),
                    }),
                    Some(StacktraceFrame {
                        name: f.clone(),
                        line: 6.into(),
                    }),
                    Some(StacktraceFrame {
                        name: g.clone(),
                        line: 7.into(),
                    }),
                    Some(StacktraceFrame {
                        name: f.clone(),
                        line: 4.into(),
                    }),
                    Some(StacktraceFrame {
                        name: end.clone(),
                        line: 1.into(),
                    }),
                ]
            );
        }
        Err(err) => panic!("Unexpected error `{}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}
#[test]
fn completion_with_prelude() {
    let _ = ::env_logger::init();
    let vm = make_vm();

    let expr = r#"
let prelude  = import! "std/prelude.glu"
and { Option } = import! "std/option.glu"
and { Num } = prelude
and { (+) } = prelude.num_Int

type Stream_ a =
    | Value a (Stream a)
    | Empty
and Stream a = Lazy (Stream_ a)

let from f : (Int -> Option a) -> Stream a =
        let from_ i =
                lazy (\_ ->
                    match f i with
                        | Some x -> Value x (from_ (i + 1))
                        | None -> Empty
                )
        in from_ 0

{ from }
"#;

    let (expr, _) = Compiler::new()
        .typecheck_str(&vm, "example", expr, None)
        .unwrap_or_else(|err| panic!("{}", err));

    let result = completion::find(&*vm.get_env(), &expr, BytePos::from(348));
    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn completion_with_prelude_at_0() {
    let _ = ::env_logger::init();
    let vm = make_vm();

    let expr = "1";

    let (expr, _) = Compiler::new()
        .typecheck_str(&vm, "example", expr, None)
        .unwrap_or_else(|err| panic!("{}", err));

    let result = completion::find(&*vm.get_env(), &expr, BytePos::from(0));
    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn suggestion_from_implicit_prelude() {
    let _ = ::env_logger::init();
    let vm = make_vm();

    let expr = "1 ";

    let (expr, _) = Compiler::new()
        .typecheck_str(&vm, "example", expr, None)
        .unwrap_or_else(|err| panic!("{}", err));

    let result = completion::suggest(&*vm.get_env(), &expr, BytePos::from(2));
    assert!(!result.is_empty());
}

/// Would cause panics in `Source` as the spans from the implicit prelude were used with the
/// `Source` from the normal expression
#[test]
fn dont_use_the_implicit_prelude_span_in_the_top_expr() {
    let _ = ::env_logger::init();
    let vm = make_vm();

    let expr = "1";

    Compiler::new()
        .typecheck_str(&vm, "example", expr, Some(&Type::float()))
        .unwrap_err();
}

#[test]
fn value_size() {
    assert!(::std::mem::size_of::<Value>() <= 16);
}
