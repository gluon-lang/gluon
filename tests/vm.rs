extern crate env_logger;
extern crate embed_lang;

use embed_lang::vm::vm::{VM, Value};
use embed_lang::vm::vm::Value::{Float, Int};
use embed_lang::import::Import;

pub fn load_script(vm: &VM, filename: &str, input: &str) -> ::embed_lang::Result<()> {
    ::embed_lang::load_script2(vm, filename, input, false)
}

pub fn run_expr<'a>(vm: &VM<'a>, s: &str) -> Value<'a> {
    *::embed_lang::run_expr2(vm, "<top>", s, false).unwrap_or_else(|err| panic!("{}", err))
}

macro_rules! test_expr {
    ($name: ident, $expr: expr, $value: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::init();
            let mut vm = make_vm();
            let value = run_expr(&mut vm, $expr);
            assert_eq!(value, $value);
        }
    };
    ($name: ident, $expr: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::init();
            let mut vm = make_vm();
            run_expr(&mut vm, $expr);
        }
    }
}

test_expr!{ pass_function_value,
r"
let lazy: () -> Int = \x -> 42 in
let test: (() -> Int) -> Int = \f -> f () #Int+ 10
in test lazy
",
Int(52)
}

test_expr!{ lambda,
r"
let y = 100 in
let f = \x -> y #Int+ x #Int+ 1
in f(22)
",
Int(123)
}

test_expr!{ add_operator,
r"
let (+) = \x y -> x #Int+ y in 1 + 2 + 3
",
Int(6)
}
test_expr!{ divide_int,
r" 120 #Int/ 4
",
Int(30)
}

test_expr!{ divide_float,
r" 120.0 #Float/ 4.0
",
Float(30.)
}

#[test]
fn record() {
    let _ = ::env_logger::init();
    let text = r"
{ x = 0, y = 1.0, z = {} }
";
    let mut vm = make_vm();
    let value = run_expr(&mut vm, text);
    let unit = vm.new_data(0, &mut []);
    assert_eq!(value, vm.new_data(0, &mut [Int(0), Float(1.0), unit]));
}

#[test]
fn add_record() {
    let _ = ::env_logger::init();
    let text = r"
type T = { x: Int, y: Int } in
let add = \l r -> { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
add { x = 0, y = 1 } { x = 1, y = 1 }
";
    let mut vm = make_vm();
    let value = run_expr(&mut vm, text);
    assert_eq!(value, vm.new_data(0, &mut [Int(1), Int(2)]));
}
#[test]
fn script() {
    let _ = ::env_logger::init();
    let text = r"
type T = { x: Int, y: Int } in
let add = \l r -> { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
let sub = \l r -> { x = l.x #Int- r.x, y = l.y #Int- r.y } in
{ T, add, sub }
";
    let mut vm = make_vm();
    load_script(&mut vm, "Vec", text).unwrap_or_else(|err| panic!("{}", err));

    let script = r#"
let { T, add, sub } = Vec
in add { x = 10, y = 5 } { x = 1, y = 2 }
"#;
    let value = run_expr(&mut vm, script);
    assert_eq!(value, vm.new_data(0, &mut [Int(11), Int(7)]));
}
#[test]
fn adt() {
    let _ = ::env_logger::init();
    let text = r"
type Option a = | None | Some a
in Some 1
";
    let mut vm = make_vm();
    let value = run_expr(&mut vm, text);
    assert_eq!(value, vm.new_data(1, &mut [Int(1)]));
}


test_expr!{ recursive_function,
r"
let fib x = if x #Int< 3
        then 1
        else fib (x #Int- 1) #Int+ fib (x #Int- 2)
in fib 7
",
Int(13)
}

test_expr!{ mutually_recursive_function,
r"
let f x = if x #Int< 0
      then x
      else g x
and g x = f (x #Int- 1)
in g 3
",
Int(-1)
}

test_expr!{ no_capture_self_function,
r"
let x = 2 in
let f y = x
in f 4
",
Int(2)
}

#[test]
fn insert_stack_slice() {
    use std::cell::Cell;

    let _ = ::env_logger::init();
    let vm = make_vm();
    let mut stack = vm.current_frame();
    stack.push(Int(0));
    stack.insert_slice(0, &[Cell::new(Int(2)), Cell::new(Int(1))]);
    assert_eq!(&stack[..], [Int(2), Int(1), Int(0)]);
    stack = stack.enter_scope(2, None);
    stack.insert_slice(1, &[Cell::new(Int(10))]);
    assert_eq!(&stack[..], [Int(1), Int(10), Int(0)]);
    stack.insert_slice(1, &[]);
    assert_eq!(&stack[..], [Int(1), Int(10), Int(0)]);
    stack.insert_slice(2,
                       &[Cell::new(Int(4)), Cell::new(Int(5)), Cell::new(Int(6))]);
    assert_eq!(&stack[..],
               [Int(1), Int(10), Int(4), Int(5), Int(6), Int(0)]);
}

test_expr!{ partial_application,
r"
let f x y = x #Int+ y in
let g = f 10
in g 2 #Int+ g 3
",
Int(25)
}

test_expr!{ partial_application2,
r"
let f x y z = x #Int+ y #Int+ z in
let g = f 10 in
let h = g 20
in h 2 #Int+ g 10 3
",
Int(55)
}

test_expr!{ to_many_args_application,
r"
let f x = \y -> x #Int+ y in
let g = f 20
in f 10 2 #Int+ g 3
",
Int(35)
}

test_expr!{ to_many_args_partial_application_twice,
r"
let f x = \y z -> x #Int+ y #Int+ z in
let g = f 20 5
in f 10 2 1 #Int+ g 2
",
Int(40)
}

test_expr!{ print_int,
r"
io.print_int 123
"
}

test_expr!{ no_io_eval,
r#"
let x = io_bind (io.print_int 1) (\x -> error "NOOOOOOOO")
in { x }
"#
}

test_expr!{ char,
r#"
'a'
"#,
Int('a' as isize)
}

#[test]
fn non_exhaustive_pattern() {
    let _ = ::env_logger::init();
    let text = r"
type AB = | A | B in
case A of
| B -> True
";
    let mut vm = make_vm();
    let result = ::embed_lang::run_expr(&mut vm, "<top>", text);
    assert!(result.is_err());
}

test_expr!{ record_pattern,
r#"
case { x = 1, y = "abc" } of
| { x, y = z } -> x #Int+ string_prim.length z
"#,
Int(4)
}

test_expr!{ let_record_pattern,
r#"
let (+) x y = x #Int+ y
in
let a = { x = 10, y = "abc" }
in
let {x, y = z} = a
in x + string_prim.length z
"#,
Int(13)
}

test_expr!{ partial_record_pattern,
r#"
type A = { x: Int, y: Float } in
let x = { x = 1, y = 2.0 }
in case x of
| { y } -> y
"#,
Float(2.0)
}

test_expr!{ record_let_adjust,
r#"
let x = \z -> let { x, y } = { x = 1, y = 2 } in z in
let a = 3
in a
"#,
Int(3)
}

test_expr!{ unit_expr,
r#"
let x = ()
and y = 1
in y
"#,
Int(1)
}

test_expr!{ let_not_in_tail_position,
r#"
1 #Int+ let x = 2 in x
"#,
Int(3)
}

test_expr!{ field_access_not_in_tail_position,
r#"
let id x = x
in (id { x = 1 }).x
"#,
Int(1)
}

test_expr!{ module_function,
r#"let x = string_prim.length "test" in x"#,
Int(4)
}

test_expr!{ io_print,
r#"io.print "123" "#
}

test_expr!{ array,
r#"
let arr = [1,2,3]

array.index arr 0 #Int== 1
    && array.length arr #Int== 3
    && array.length (array.append arr arr) #Int== array.length arr #Int* 2"#,
Int(1)
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
    let mut vm = make_vm();
    let result = run_expr(&mut vm, text);
    assert_eq!(result, vm.new_data(0, &mut [Int(3), Float(3.0)]));
}

#[test]
fn through_overloaded_alias() {
    let _ = ::env_logger::init();
    let text = r#"
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
"#;
    let mut vm = make_vm();
    let result = run_expr(&mut vm, text);
    assert_eq!(result, Int(0));
}

#[test]
fn run_expr_int() {
    let _ = ::env_logger::init();
    let text = r#"io.run_expr "123" "#;
    let mut vm = make_vm();
    let result = run_expr(&mut vm, text);
    assert_eq!(result, Value::String(vm.alloc(&vm.current_frame().stack, "123")));
}

test_expr!{ run_expr_io,
r#"io_bind (io.run_expr "io.print_int 123") (\x -> io_return 100) "#,
Int(100)
}

#[test]
fn rename_types_after_binding() {
    let _ = ::env_logger::init();
    let text = r#"
let prelude = import "std/prelude.hs"
in
let { List } = prelude
and { (==) }: Eq (List Int) = prelude.eq_List { (==) }
in Cons 1 Nil == Nil
"#;
    let mut vm = make_vm();
    let value = ::embed_lang::run_expr(&mut vm, "<top>", text).unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(*value, Int(0));
}

#[test]
fn test_implicit_prelude() {
    let _ = ::env_logger::init();
    let text = r#"Ok (Some (1.0 + 3.0 - 2.0)) "#;
    let mut vm = make_vm();
    ::embed_lang::run_expr(&mut vm, "<top>", text).unwrap_or_else(|err| panic!("{}", err));
}

#[test]
fn access_field_through_vm() {
    let _ = ::env_logger::init();
    let text = r#" { x = 0, inner = { y = 1.0 } } "#;
    let mut vm = make_vm();
    load_script(&mut vm, "test", text)
        .unwrap_or_else(|err| panic!("{}", err));
    let test_x = vm.get_global("test.x");
    assert_eq!(test_x, Ok(0));
    let test_inner_y = vm.get_global("test.inner.y");
    assert_eq!(test_inner_y, Ok(1.0));
}

/// Creates a VM for testing which has the correct paths to import the std library properly
fn make_vm<'a>() -> VM<'a> {
    let vm = ::embed_lang::new_vm();
    let import_symbol = vm.symbol("import");
    let import = vm.get_macros().get(import_symbol);
    import.as_ref()
          .and_then(|import| import.downcast_ref::<Import>())
          .expect("Import macro")
          .add_path("..");
    vm
}

#[test]
fn test_prelude() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    run_expr(&vm, r#" import "std/prelude.hs" "#);
}

#[test]
fn access_types_by_path() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    run_expr(&vm, r#" import "std/prelude.hs" "#);
    assert!(vm.find_type_info("std.prelude.Option").is_ok());
    assert!(vm.find_type_info("std.prelude.Result").is_ok());
}

#[test]
fn value_size() {
    assert!(::std::mem::size_of::<Value>() <= 16);
}
