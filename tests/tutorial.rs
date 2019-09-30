#[macro_use]
extern crate gluon_vm;

use gluon::base::types::Type;
use gluon::import::{add_extern_module, Import};
use gluon::vm;
use gluon::vm::api::{FunctionRef, Hole, OpaqueValue};
use gluon::{RootedThread, Thread, ThreadExt};

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
    vm.run_expr::<OpaqueValue<&Thread, Hole>>("example", r#" import! std.int "#)
        .unwrap();
    let mut add: FunctionRef<fn(i32, i32) -> i32> = vm
        .get_global("std.int.num.(+)")
        .unwrap_or_else(|err| panic!("{}", err));
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
        vm::ExternModule::new(vm, primitive!(1, factorial))
    }

    let vm = new_vm();

    // Introduce a module that can be loaded with `import! factorial`
    add_extern_module(&vm, "factorial", load_factorial);

    let expr = r#"
        let factorial = import! factorial
        factorial 5
    "#;

    let (result, _) = vm.run_expr::<i32>("factorial", expr).unwrap();

    assert_eq!(result, 120);
}

#[test]
fn use_string_module() {
    let _ = ::env_logger::try_init();

    let vm = new_vm();
    let result = vm
        .run_expr::<String>(
            "example",
            " let string  = import! \"std/string.glu\" in string.trim \"  \
             Hello world  \t\" ",
        )
        .unwrap();
    let expected = ("Hello world".to_string(), Type::string());

    assert_eq!(result, expected);
}
