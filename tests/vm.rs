extern crate env_logger;
#[macro_use]
extern crate pretty_assertions;

extern crate gluon;
extern crate gluon_completion as completion;

#[macro_use]
mod support;

use support::*;

use gluon::base::pos::BytePos;
use gluon::base::types::Type;
use gluon::base::source;
use gluon::vm::api::{FunctionRef, Hole, OpaqueValue, ValueRef};
use gluon::vm::thread::{RootedThread, Thread, ThreadInternal};
use gluon::vm::internal::Value;
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
    let _ = ::env_logger::try_init();
    let text = r"
{ x = 0, y = 1.0, z = {} }
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    match value.get_ref() {
        ValueRef::Data(data) => {
            assert_eq!(data.get(0).unwrap(), ValueRef::Int(0));
            assert_eq!(data.get(1).unwrap(), ValueRef::Float(1.0));
            match data.get(2).unwrap() {
                ValueRef::Data(data) if data.tag() == 0 => (),
                _ => panic!(),
            }
        }
        _ => panic!(),
    }
}

#[test]
fn add_record() {
    let _ = ::env_logger::try_init();
    let text = r"
type T = { x: Int, y: Int } in
let add = \l r -> { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
add { x = 0, y = 1 } { x = 1, y = 1 }
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    match value.get_ref() {
        ValueRef::Data(data) => {
            assert_eq!(data.get(0).unwrap(), ValueRef::Int(1));
            assert_eq!(data.get(1).unwrap(), ValueRef::Int(2));
        }
        _ => panic!(),
    }
}
#[test]
fn script() {
    let _ = ::env_logger::try_init();
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
    let _ = ::env_logger::try_init();
    let text = r"
type Option a = | None | Some a
in Some 1
";
    let vm = make_vm();
    let value = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    match value.get_ref() {
        ValueRef::Data(ref data) if data.tag() == 1 && data.get(0) == Some(ValueRef::Int(1)) => (),
        _ => panic!("{:?}", value),
    }
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

test_expr!{ prelude overloaded_compare_int,
r"
99 < 100
",
true
}

test_expr!{ prelude overloaded_compare_float,
r"
99.0 < 100.0
",
true
}

test_expr!{ implicit_call_without_type_in_scope,
r"
let int @ { ? } = import! std.int
let prelude @ { (==) } = import! std.prelude
99 == 100
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

test_expr!{ char,
r#"
'a'
"#,
'a'
}

test_expr!{ prelude handle_fields_being_ignored_in_optimize,
    r#"
let large_record = { x = 1, y = 2 }
large_record.x
"#,
1
}

test_expr!{ any zero_argument_variant_is_int,
r#"
type Test = | A Int | B
B
"#,
Value::tag(1)
}

test_expr!{ any marshalled_option_none_is_int,
r#"
let string_prim = import! std.string.prim
string_prim.find "a" "b"
"#,
Value::tag(0)
}

test_expr!{ any marshalled_ordering_is_int,
r#"
let { string_compare } = import! std.prim
string_compare "a" "b"
"#,
Value::tag(0)
}

test_expr!{ discriminant_value,
r#"
type Variant a = | A | B Int | C String
let prim = import! std.prim
prim.discriminant_value (C "")
"#,
2
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
r#"
let string_prim = import! std.string.prim
let x = string_prim.len "test" in x
"#,
4i32
}

test_expr!{ prelude true_branch_not_affected_by_false_branch,
r#"
let { Bool } = import! std.bool
if True then
    let x = 1
    x
else
    0
"#,
1i32
}

test_expr!{ prelude and_operator_stack,
r#"
let { Bool } = import! std.bool
let b = True && True
let b2 = False
b
"#,
true
}

test_expr!{ prelude or_operator_stack,
r#"
let { Bool } = import! std.bool
let b = False || True
let b2 = False
b
"#,
true
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

#[test]
fn overloaded_bindings() {
    let _ = ::env_logger::try_init();
    let text = r#"
/// @implicit
let add_int x y = x #Int+ y
/// @implicit
let add_float x y = x #Float+ y

let add ?f: [a -> a -> a] -> a -> a -> a = f

{ x = add 1 2, y = add 1.0 2.0 }
"#;
    let vm = make_vm();
    let result = run_expr::<OpaqueValue<&Thread, Hole>>(&vm, text);
    match result.get_ref() {
        ValueRef::Data(data) => {
            assert_eq!(data.get(0).unwrap(), ValueRef::Int(3));
            assert_eq!(data.get(1).unwrap(), ValueRef::Float(3.0));
        }
        _ => panic!(),
    }
}

test_expr!{ record_base_duplicate_fields,
r#"
{ x = "" ..  { x = 1 } }.x
"#,
""
}

test_expr!{ record_base_duplicate_fields2,
r#"
{ x = "" ..  { x = 1, y = 2 } }.y
"#,
2
}

test_expr!{ prelude do_expression_option_some,
r#"
let { monad = { flat_map } } = import! std.option
do x = Some 1
Some (x + 2)
"#,
Some(3)
}

test_expr!{ prelude do_expression_option_none,
r#"
let { monad = { flat_map } } = import! std.option
do x = None
Some 1
"#,
None::<i32>
}

test_expr!{ function_with_implicit_argument_from_record,
r#"
let f ?t x: [Int] -> () -> Int = t
let x @ { ? } =
    /// @implicit
    let test = 1
    { test }
f ()
"#,
1
}

test_expr!{ prelude not_equal_operator,
r#"
1 /= 2
"#,
true
}

test_expr!{ implicit_argument_selection1,
r#"
/// @implicit
type Test = | Test ()
let f y: [a] -> a -> () = ()
let i = Test ()
f (Test ())
"#,
()
}

test_expr!{ prelude implicit_argument_selection2,
r#"
let string = import! std.string
let { append = (++) } = string.semigroup

let equality l r : [Eq a] -> a -> a -> String =
    if l == r then " == " else " != "

let cmp l r : [Show a] -> [Eq a] -> a -> a -> String =
    (show l) ++ (equality l r) ++ (show r)

cmp 5 6
"#,
String::from("5 != 6")
}

#[test]
fn rename_types_after_binding() {
    let _ = ::env_logger::try_init();

    let text = r#"
let list = import! std.list
in
let { List } = list
and eq_list: Eq (List Int) = list.eq
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
fn record_splat_ice() {
    let _ = ::env_logger::try_init();

    let text = r#"
let large_record = { x = 1 }
{
    field = 123,
    ..
    large_record
}
"#;
    let mut vm = make_vm();
    let result = Compiler::new()
        .implicit_prelude(false)
        .run_expr::<OpaqueValue<&Thread, Hole>>(&mut vm, "example", text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn test_implicit_prelude() {
    let _ = ::env_logger::try_init();
    let text = r#"1.0 + 3.0 - 2.0"#;
    let mut vm = make_vm();
    Compiler::new()
        .run_expr_async::<OpaqueValue<&Thread, Hole>>(&mut vm, "<top>", text)
        .sync_or_error()
        .unwrap_or_else(|err| panic!("{}", err));
}

#[test]
fn access_field_through_vm() {
    let _ = ::env_logger::try_init();
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
    let _ = ::env_logger::try_init();
    let vm = make_vm();
    Compiler::new()
        .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, "example", r#" import! std.prelude "#)
        .sync_or_error()
        .unwrap();
    let result: Result<FunctionRef<fn(i32, i32) -> i32>, _> =
        vm.get_global("std.prelude.num_Int.+");
    assert!(result.is_err());
}

#[test]
fn get_binding_with_alias_type() {
    let _ = ::env_logger::try_init();
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
    let _ = ::env_logger::try_init();

    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! std.function "#);
    let mut id: FunctionRef<fn(String) -> String> = vm.get_global("std.function.id")
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(id.call("test".to_string()), Ok("test".to_string()));
}

#[test]
fn test_prelude() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! std.prelude "#);
}

#[test]
fn access_types_by_path() {
    let _ = ::env_logger::try_init();

    let vm = make_vm();
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! std.option "#);
    run_expr::<OpaqueValue<&Thread, Hole>>(&vm, r#" import! std.result "#);

    assert!(vm.find_type_info("std.option.Option").is_ok());
    assert!(vm.find_type_info("std.result.Result").is_ok());

    let text = r#" type T a = | T a in { x = 0, inner = { T, y = 1.0 } } "#;
    load_script(&vm, "test", text).unwrap_or_else(|err| panic!("{}", err));
    let result = vm.find_type_info("test.inner.T");
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn opaque_value_type_mismatch() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();

    Compiler::new()
        .implicit_prelude(false)
        .run_expr_async::<()>(&vm, "<top>", "let _ = import! std.channel in ()")
        .sync_or_error()
        .unwrap();

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
    let _ = ::env_logger::try_init();
    let text = r#"
let string = import! std.string
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
fn partially_applied_constructor_is_lambda() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();

    let result = Compiler::new().run_expr::<FunctionRef<fn(i32) -> Option<i32>>>(
        &vm,
        "test",
        r#"let { Option } = import! std.option in Some"#,
    );
    assert!(result.is_ok(), "{}", result.err().unwrap());
    assert_eq!(result.unwrap().0.call(123), Ok(Some(123)));
}

#[test]
fn stacktrace() {
    use gluon::vm::stack::StacktraceFrame;
    let _ = ::env_logger::try_init();
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
            let error = stacktrace.frames[7].as_ref().unwrap().name.clone();
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
                    Some(StacktraceFrame {
                        name: error.clone(),
                        line: 0.into(),
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
    let _ = ::env_logger::try_init();
    let vm = make_vm();

    let source = r#"
let prelude  = import! std.prelude
and { Option } = import! std.option
and { Num } = prelude
let { lazy } = import! std.lazy

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
        .typecheck_str(&vm, "example", source, None)
        .unwrap_or_else(|err| panic!("{}", err));

    let lines = source::Lines::new(source.as_bytes().iter().cloned());
    let result = completion::find(
        &*vm.get_env(),
        &expr,
        lines.offset(14.into(), 29.into()).unwrap(),
    );
    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn completion_with_prelude_at_0() {
    let _ = ::env_logger::try_init();
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
    let _ = ::env_logger::try_init();
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
    let _ = ::env_logger::try_init();
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

#[test]
fn deep_clone_partial_application() {
    use gluon::base::symbol::Symbol;
    use gluon::base::metadata::Metadata;

    let _ = ::env_logger::try_init();
    let vm = RootedThread::new();

    assert_eq!(vm.context().gc.allocated_memory(), 0);

    let child = vm.new_thread().unwrap();

    assert_eq!(child.context().gc.allocated_memory(), 0);

    let result = Compiler::new()
        .implicit_prelude(false)
        .run_expr::<OpaqueValue<&Thread, Hole>>(
            &child,
            "test",
            r#"
                let f x y = y
                f 1
            "#,
        );
    assert!(result.is_ok(), "{}", result.err().unwrap());

    let global_memory_without_closures = vm.global_env().gc.lock().unwrap().allocated_memory();
    let memory_for_closures = child.context().gc.allocated_memory();

    vm.set_global(
        Symbol::from("@test"),
        Type::hole(),
        Metadata::default(),
        unsafe { result.unwrap().0.get_value() },
    ).unwrap();

    let global_memory_with_closures = vm.global_env().gc.lock().unwrap().allocated_memory();

    assert_eq!(
        global_memory_without_closures + memory_for_closures,
        global_memory_with_closures
    );
}
