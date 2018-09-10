extern crate env_logger;
extern crate futures;
#[macro_use]
extern crate serde_derive;

extern crate gluon;
#[macro_use]
extern crate gluon_vm;

use futures::future::lazy;
use futures::{Future, IntoFuture};

use gluon::base::types::{Alias, ArcType, Type};
use gluon::import::{add_extern_module, Import};
use gluon::vm::api::de::De;
use gluon::vm::api::{FunctionRef, FutureResult, OpaqueValue, Userdata, VmType, IO};
use gluon::vm::thread::{RootedThread, Thread, Traverseable};
use gluon::vm::types::VmInt;
use gluon::vm::{Error, ExternModule};
use gluon::Compiler;

fn load_script(vm: &Thread, filename: &str, input: &str) -> ::gluon::Result<()> {
    Compiler::new().load_script(vm, filename, input)
}

fn make_vm() -> RootedThread {
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
fn call_function() {
    let _ = ::env_logger::try_init();
    let add10 = r"
        let add10 : Int -> Int = \x -> x #Int+ 10 in add10
    ";
    let mul = r"
        let mul : Float -> Float -> Float = \x y -> x #Float* y in mul
    ";
    let mut vm = make_vm();
    load_script(&mut vm, "add10", &add10).unwrap_or_else(|err| panic!("{}", err));
    load_script(&mut vm, "mul", &mul).unwrap_or_else(|err| panic!("{}", err));
    {
        let mut f: FunctionRef<fn(VmInt) -> VmInt> = vm.get_global("add10").unwrap();
        let result = f.call(2).unwrap();
        assert_eq!(result, 12);
    }
    let mut f: FunctionRef<fn(f64, f64) -> f64> = vm.get_global("mul").unwrap();
    let result = f.call(4., 5.).unwrap();
    assert_eq!(result, 20.);
}

#[test]
fn root_data() {
    let _ = ::env_logger::try_init();

    #[derive(Debug)]
    struct Test(VmInt);
    impl Userdata for Test {}
    impl Traverseable for Test {}
    impl VmType for Test {
        type Type = Test;
    }

    let expr = r#"
        let test = import! test
        \x -> test x 1
    "#;
    let vm = make_vm();
    fn test(r: OpaqueValue<RootedThread, Test>, i: VmInt) -> VmInt {
        r.0 + i
    }
    vm.register_type::<Test>("Test", &[])
        .unwrap_or_else(|_| panic!("Could not add type"));

    add_extern_module(&vm, "test", |thread| {
        ExternModule::new(thread, primitive!(2, test))
    });

    load_script(&vm, "script_fn", expr).unwrap_or_else(|err| panic!("{}", err));
    let mut script_fn: FunctionRef<fn(Test) -> VmInt> = vm.get_global("script_fn").unwrap();
    let result = script_fn.call(Test(123)).unwrap();
    assert_eq!(result, 124);
}

#[test]
fn root_string() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let test = import! test
        test "hello"
    "#;
    fn test(s: OpaqueValue<&Thread, str>) -> String {
        let mut result = String::from(&s[..]);
        result.push_str(" world");
        result
    }

    let vm = make_vm();
    add_extern_module(&vm, "test", |thread| {
        ExternModule::new(thread, primitive!(1, test))
    });

    let result = Compiler::new()
        .run_expr::<String>(&vm, "<top>", expr)
        .unwrap();
    let expected = ("hello world".to_string(), Type::string());

    assert_eq!(result, expected);
}

#[test]
fn array() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let sum_bytes = import! sum_bytes
        sum_bytes [100b, 42b, 3b, 15b]
    "#;
    fn sum_bytes(s: &[u8]) -> u8 {
        s.iter().fold(0, |acc, b| acc + b)
    }

    let vm = make_vm();
    add_extern_module(&vm, "sum_bytes", |thread| {
        ExternModule::new(thread, primitive!(1, sum_bytes))
    });

    let result = Compiler::new()
        .run_expr::<u8>(&vm, "<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = (160, Type::byte());

    assert_eq!(result, expected);
}

#[test]
fn return_finished_future() {
    let _ = ::env_logger::try_init();

    fn add(x: i32, y: i32) -> FutureResult<impl Future<Item = i32, Error = Error>> {
        FutureResult(Ok(x + y).into_future())
    }

    let expr = r#"
        let add = import! add
        add 1 2
    "#;

    let vm = make_vm();
    add_extern_module(&vm, "add", |thread| {
        ExternModule::new(thread, primitive!(2, add))
    });

    let result = Compiler::new()
        .run_expr::<i32>(&vm, "<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = (3, Type::int());

    assert_eq!(result, expected);
}

fn poll_n(s: String) -> FutureResult<impl Future<Item = IO<String>, Error = Error>> {
    use futures::sync::oneshot::channel;
    use std::thread::spawn;

    let (ping_c, ping_p) = channel();
    let (pong_c, pong_p) = channel();
    spawn(move || {
        ping_p.wait().expect("wait");
        pong_c.send(s).expect("send");
    });
    FutureResult(
        lazy(move || {
            ping_c.send(()).unwrap();
            Ok(())
        }).and_then(|_| {
            pong_p
                .map(IO::Value)
                .map_err(|err| Error::Message(format!("{}", err)))
        }),
    )
}

#[test]
fn return_delayed_future_simple() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let poll_n = import! poll_n
        poll_n "test"
    "#;

    let vm = make_vm();
    add_extern_module(&vm, "poll_n", |thread| {
        ExternModule::new(thread, primitive!(1, poll_n))
    });

    let (result, _) = Compiler::new()
        .run_io(true)
        .run_expr::<IO<String>>(&vm, "<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = IO::Value("test".to_string());

    assert_eq!(result, expected);
}

#[test]
fn return_delayed_future_in_catch() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let io = import! std.io
        let poll_n = import! poll_n
        io.catch (poll_n "test") (\_ -> io.applicative.wrap "error")
    "#;

    let vm = make_vm();
    add_extern_module(&vm, "poll_n", |thread| {
        ExternModule::new(thread, primitive!(1, poll_n))
    });

    let (result, _) = Compiler::new()
        .run_io(true)
        .run_expr::<IO<String>>(&vm, "<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = IO::Value("test".to_string());

    assert_eq!(result, expected);
}

#[test]
fn io_future() {
    use gluon_vm::api::IO;

    let _ = ::env_logger::try_init();

    fn test(_: ()) -> FutureResult<impl Future<Item = IO<i32>, Error = Error>> {
        FutureResult(Ok(IO::Value(123)).into_future())
    }

    let expr = r#"
        let test = import! test
        let { applicative, monad }  = import! std.io
        monad.flat_map (\x -> applicative.wrap (x + 1)) (test ())
    "#;

    let vm = make_vm();
    add_extern_module(&vm, "test", |thread| {
        ExternModule::new(thread, primitive!(1, test))
    });

    let result = Compiler::new()
        .run_io(true)
        .run_expr::<IO<i32>>(&vm, "<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));

    assert_eq!(result.0, IO::Value(124));
}

#[test]
fn generic_record_type() {
    use gluon::base::types::ArcType;
    use gluon::vm::api::generic::A;
    use gluon::vm::api::Generic;

    fn type_of<T: VmType>(thread: &Thread, _: &T) -> ArcType {
        T::make_forall_type(thread)
    }
    fn test(_: Generic<A>) {}

    let record = record! {
        test => primitive!(1, test)
    };
    assert_eq!(
        type_of(&make_vm(), &record).to_string(),
        "{ test : forall a . a -> () }"
    )
}

#[test]
fn tuples_start_at_0() {
    let thread = make_vm();
    assert_eq!(<(i32, f64)>::make_type(&thread).to_string(), "(Int, Float)");
    assert_eq!(
        <(i32, f64, String)>::make_type(&thread).to_string(),
        "(Int, Float, String)"
    );
}

#[test]
fn use_type_from_type_field() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();

    #[derive(Serialize, Deserialize, PartialEq, Debug)]
    enum Test {
        A(i32),
        B(String),
        C,
    }
    impl VmType for Test {
        type Type = Self;
        fn make_type(vm: &Thread) -> ArcType {
            if let Some(typ) = vm.get_type::<Self>() {
                return typ;
            }

            let (name, typ) = gluon::vm::api::typ::from_rust::<Self>(vm).unwrap();
            vm.register_type_as(
                name.clone(),
                Alias::new(name, typ),
                ::std::any::TypeId::of::<Self>(),
            ).unwrap()
        }
    }

    add_extern_module(&vm, "test_types", |vm| {
        ExternModule::new(vm, record!{ type Test => Test })
    });
    let text = r#"
        let { Test } = import! test_types
        B "abc"
    "#;
    let (De(actual), _) = Compiler::new()
        .run_expr::<De<Test>>(&vm, "test", text)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(actual, Test::B("abc".to_string()));
}

#[test]
fn use_rust_created_record_as_polymorphic() {
    let _ = ::env_logger::try_init();
    let test = r"\x -> x.x";
    let mut vm = make_vm();
    load_script(&mut vm, "test", test).unwrap_or_else(|err| panic!("{}", err));

    field_decl! { x }
    type Test = record_type!{
        x => i32
    };

    let mut f: FunctionRef<fn(Test) -> VmInt> = vm.get_global("test").unwrap();
    let result = f.call(record_no_decl!{ x => 1 }).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn get_value_boxed_or_unboxed() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();

    let text = r#"
        27
    "#;

    // The user should be able to decide whether or not any gluon value should
    // be boxed on the rust side.
    let (unboxed, _) = Compiler::new()
        .run_expr::<i32>(&vm, "test", text)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(unboxed, 27);
    let (boxed, _) = Compiler::new()
        .run_expr::<Box<i32>>(&vm, "test", text)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(boxed, Box::new(27));
}
