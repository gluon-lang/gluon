extern crate env_logger;
extern crate gluon;
#[macro_use]
extern crate gluon_vm;

use gluon::base::types::Type;
use gluon::vm::api::{FunctionRef, Hole, OpaqueValue};
use gluon::vm;
use gluon::{RootedThread, Thread};
use gluon::import::{add_extern_module, Import};
use gluon::Compiler;

fn new_vm() -> RootedThread {
    let vm = ::gluon::new_vm();
    let import = vm.get_macros().get("import");
    import
        .as_ref()
        .and_then(|import| import.downcast_ref::<Import>())
        .expect("Import macro")
        .add_path("..");
    vm
}

#[test]
fn access_field_through_alias() {
    let _ = ::env_logger::try_init();
    let vm = new_vm();
    Compiler::new()
        .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, "example", r#" import! std.int "#)
        .sync_or_error()
        .unwrap();
    let mut add: FunctionRef<fn(i32, i32) -> i32> = vm.get_global("std.int.num.(+)").unwrap();
    let result = add.call(1, 2);
    assert_eq!(result, Ok(3));
}

#[test]
fn call_rust_from_gluon() {
    let _ = ::env_logger::try_init();

    fn factorial(x: i32) -> i32 {
        if x <= 1 {
            1
        } else {
            x * factorial(x - 1)
        }
    }

    fn load_factorial(vm: &Thread) -> vm::Result<vm::ExternModule> {
        vm::ExternModule::new(vm, primitive!(1 factorial))
    }

    let vm = new_vm();

    // Introduce a module that can be loaded with `import! factorial`
    add_extern_module(&vm, "factorial", load_factorial);

    let expr = r#"
        let factorial = import! factorial
        factorial 5
    "#;

    let (result, _) = Compiler::new()
        .run_expr_async::<i32>(&vm, "factorial", expr)
        .sync_or_error()
        .unwrap();

    assert_eq!(result, 120);
}

#[test]
fn use_string_module() {
    let _ = ::env_logger::try_init();

    let vm = new_vm();
    let result = Compiler::new()
        .run_expr_async::<String>(
            &vm,
            "example",
            " let string  = import! \"std/string.glu\" in string.trim \"  \
             Hello world  \t\" ",
        )
        .sync_or_error()
        .unwrap();
    let expected = ("Hello world".to_string(), Type::string());

    assert_eq!(result, expected);
}
