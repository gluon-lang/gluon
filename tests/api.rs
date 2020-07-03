#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate gluon_vm;
#[macro_use]
extern crate gluon_codegen;

use std::{collections::BTreeMap, sync::Arc};

use futures::prelude::*;

use gluon::{
    base::types::{Alias, ArcType, Type},
    import::{add_extern_module, add_extern_module_with_deps, Import},
    query::Compilation,
    vm::{
        api::{
            de::De,
            scoped::{Ref, RefMut},
            FunctionRef, FutureResult, Hole, OpaqueValue, OwnedFunction, RuntimeResult, VmType, IO,
        },
        gc,
        thread::{RootedThread, Thread},
        types::VmInt,
        Error, ExternModule,
    },
    ThreadExt,
};

fn load_script(vm: &Thread, filename: &str, input: &str) -> ::gluon::Result<()> {
    vm.load_script(filename, input)
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

#[derive(Debug, Userdata, Trace)]
struct Test(VmInt);
impl VmType for Test {
    type Type = Test;
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

    let result = vm.run_expr::<String>("<top>", expr).unwrap();
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

    let result = vm
        .run_expr::<u8>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = (160, Type::byte());

    assert_eq!(result, expected);
}

#[test]
fn return_finished_future() {
    let _ = ::env_logger::try_init();

    fn add(x: i32, y: i32) -> FutureResult<impl Future<Output = i32>> {
        FutureResult(async move { x + y })
    }

    let expr = r#"
        let add = import! add
        add 1 2
    "#;

    let vm = make_vm();
    add_extern_module(&vm, "add", |thread| {
        ExternModule::new(thread, primitive!(2, add))
    });

    let result = vm
        .run_expr::<i32>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = (3, Type::int());

    assert_eq!(result, expected);
}

fn poll_n(s: String) -> FutureResult<impl Future<Output = IO<String>>> {
    use futures::channel::oneshot::channel;
    use std::thread::spawn;

    let (ping_c, ping_p) = channel();
    let (pong_c, pong_p) = channel();
    spawn(move || {
        futures::executor::block_on(ping_p).expect("wait");
        pong_c.send(s).expect("send");
    });
    FutureResult(async move {
        ping_c.send(()).unwrap();
        IO::from(
            pong_p
                .await
                .map_err(|err| Error::Message(format!("{}", err))),
        )
    })
}

#[test]
fn return_delayed_future_simple() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let poll_n = import! poll_n
        poll_n "test"
    "#;

    let vm = make_vm();
    vm.get_database_mut().run_io(true);
    add_extern_module(&vm, "poll_n", |thread| {
        ExternModule::new(thread, primitive!(1, poll_n))
    });

    let (result, _) = vm
        .run_expr::<IO<String>>("<top>", expr)
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
    vm.get_database_mut().run_io(true);
    add_extern_module(&vm, "poll_n", |thread| {
        ExternModule::new(thread, primitive!(1, poll_n))
    });

    let (result, _) = vm
        .run_expr::<IO<String>>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = IO::Value("test".to_string());

    assert_eq!(result, expected);
}

#[test]
fn io_future() {
    use gluon_vm::api::IO;

    let _ = ::env_logger::try_init();

    fn test(_: ()) -> FutureResult<impl Future<Output = IO<i32>>> {
        FutureResult(async { IO::Value(123) })
    }

    let expr = r#"
        let test = import! test
        let { applicative, monad }  = import! std.io
        monad.flat_map (\x -> applicative.wrap (x + 1)) (test ())
    "#;

    let vm = make_vm();
    vm.get_database_mut().run_io(true);
    add_extern_module(&vm, "test", |thread| {
        ExternModule::new(thread, primitive!(1, test))
    });

    let result = vm
        .run_expr::<IO<i32>>("<top>", expr)
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
                Alias::new(name, Vec::new(), typ),
                ::std::any::TypeId::of::<Self>(),
            )
            .unwrap()
        }
    }

    add_extern_module(&vm, "test_types", |vm| {
        ExternModule::new(vm, record! { type Test => Test })
    });
    let text = r#"
        let { Test } = import! test_types
        B "abc"
    "#;
    let (De(actual), _) = vm
        .run_expr::<De<Test>>("test", text)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(actual, Test::B("abc".to_string()));
}

#[test]
fn use_rust_created_tuple_as_polymorphic() {
    let _ = ::env_logger::try_init();
    let test = r"\x -> x._0";
    let mut vm = make_vm();
    load_script(&mut vm, "test", test).unwrap_or_else(|err| panic!("{}", err));

    let mut f: FunctionRef<fn((i32, String)) -> VmInt> = vm.get_global("test").unwrap();
    let result = f.call((1, "".to_string())).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn use_rust_created_record_as_polymorphic() {
    let _ = ::env_logger::try_init();
    let test = r"\x -> x.x";
    let mut vm = make_vm();
    load_script(&mut vm, "test", test).unwrap_or_else(|err| panic!("{}", err));

    field_decl! { x }
    type Test = record_type! {
        x => i32
    };

    let mut f: FunctionRef<fn(Test) -> VmInt> = vm.get_global("test").unwrap();
    let result = f.call(record_no_decl! { x => 1 }).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn return_btreemap() {
    let _ = ::env_logger::try_init();

    let vm = make_vm();

    add_extern_module_with_deps(
        &vm,
        "test",
        |vm| {
            ExternModule::new(
                vm,
                primitive!(1, "test", |()| {
                    vec![("a".to_string(), 1), ("b".to_string(), 2)]
                        .into_iter()
                        .collect::<BTreeMap<_, _>>()
                }),
            )
        },
        vec!["std.map".into(), "std.json.de".into()],
    );

    vm.run_expr::<()>("", "let _ = import! test in ()")
        .unwrap_or_else(|err| panic!("{}", err));
    let (result, _) = vm
        .run_expr::<BTreeMap<_, _>>("", "(import! test) ()")
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(
        result,
        vec![("a".to_string(), 1), ("b".to_string(), 2)]
            .into_iter()
            .collect::<BTreeMap<_, _>>()
    );
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
    let (unboxed, _) = vm
        .run_expr::<i32>("test", text)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(unboxed, 27);
    let (boxed, _) = vm
        .run_expr::<Box<i32>>("test", text)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(boxed, Box::new(27));
}

#[test]
fn runtime_result_vm_type_forwarding() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();
    vm.get_database_mut().run_io(true);

    add_extern_module(&vm, "test", |vm| {
        ExternModule::new(
            vm,
            record! {
                primes => primitive!(1, |_: ()| -> RuntimeResult<IO<()>, String> {
                    RuntimeResult::Return(IO::Value(()))
                })
            },
        )
    });

    let text = r#"
        let { primes } = import! test
        let { ? } = import! std.io
        let { wrap } = import! std.applicative

        do primes = primes ()
        wrap ()
    "#;

    let _ = vm
        .run_expr::<IO<()>>("test", text)
        .unwrap_or_else(|err| panic!("{}", err));
}

#[test]
fn scoped_reference_basic() {
    let _ = ::env_logger::try_init();

    fn function(r: &Test, i: VmInt) -> VmInt {
        r.0 + i
    }

    let expr = r#"
        let function = import! function
        \x -> function x 1
    "#;

    let vm = make_vm();
    vm.register_type::<Test>("Test", &[])
        .unwrap_or_else(|_| panic!("Could not add type"));
    add_extern_module(&vm, "function", |thread| {
        ExternModule::new(thread, primitive!(2, function))
    });

    let (mut result, _) = vm
        .run_expr::<OwnedFunction<fn(_) -> VmInt>>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));

    assert_eq!(
        result
            .call(&mut Ref::new(&Test(2)))
            .unwrap_or_else(|err| panic!("{}", err)),
        3
    );
}

#[test]
fn scoped_reference_out_of_scope() {
    let _ = ::env_logger::try_init();

    fn recursive<'a, 'b>(
        f: OwnedFunction<fn(OpaqueValue<RootedThread, Test>) -> OpaqueValue<RootedThread, Test>>,
    ) -> OpaqueValue<RootedThread, Test> {
        let mut f: OwnedFunction<fn(_) -> OpaqueValue<RootedThread, Test>> = f.cast().unwrap();
        f.call(&mut Ref::new(&Test(1))).unwrap()
    }

    fn function(r: &Test, i: VmInt) -> VmInt {
        r.0 + i
    }

    let expr = r#"
        let { recursive, function } = import! module
        function (recursive (\t -> t)) 1
    "#;

    let vm = make_vm();
    vm.register_type::<Test>("Test", &[])
        .unwrap_or_else(|_| panic!("Could not add type"));
    add_extern_module(&vm, "module", |thread| {
        ExternModule::new(
            thread,
            record! {
                recursive => primitive!(1, recursive),
                function => primitive!(2, function)
            },
        )
    });

    let result = vm.run_expr::<VmInt>("<top>", expr);
    match result {
        Err(gluon::Error::VM(Error::Panic(ref m, _))) if m == "Scoped pointer is invalidated" => (),
        Err(err) => panic!("Wrong error: {:#?}", err),
        Ok(_) => panic!("Unexpected success"),
    }
}

#[test]
fn scoped_mutable_reference() {
    let _ = ::env_logger::try_init();

    fn write(r: &mut Test, i: VmInt) -> IO<()> {
        r.0 = i;
        IO::Value(())
    }

    fn read(r: &mut Test) -> IO<VmInt> {
        IO::Value(r.0)
    }

    let expr = r#"
        let { read, write } = import! function
        let { ? } = import! std.io
        \t i ->
            seq write t (i + 10)
            read t
    "#;

    let vm = make_vm();
    vm.register_type::<Test>("Test", &[])
        .unwrap_or_else(|_| panic!("Could not add type"));
    add_extern_module(&vm, "function", |thread| {
        ExternModule::new(
            thread,
            record! {
                write => primitive!(2, write),
                read => primitive!(1, read)
            },
        )
    });

    let (mut result, _) = vm
        .run_expr::<OwnedFunction<fn(_, _) -> IO<VmInt>>>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));

    assert_eq!(
        result
            .call(&mut RefMut::new(&mut Test(2)), 3)
            .unwrap_or_else(|err| panic!("{}", err)),
        IO::Value(13)
    );
}

#[derive(Clone, Debug, Default, Userdata, Trace)]
struct NoisyDrop(Arc<()>);
impl VmType for NoisyDrop {
    type Type = NoisyDrop;
}

#[test]
fn cyclic_userdata_simple() {
    let _ = ::env_logger::try_init();

    #[derive(Debug, Userdata, Trace)]
    struct Cyclic(OpaqueValue<RootedThread, NoisyDrop>);
    impl VmType for Cyclic {
        type Type = Cyclic;
    }

    let mut noisy_drop = NoisyDrop::default();
    {
        let vm = make_vm();

        vm.register_type::<NoisyDrop>("NoisyDrop", &[])
            .unwrap_or_else(|_| panic!("Could not add type"));
        vm.register_type::<Cyclic>("Cyclic", &[])
            .unwrap_or_else(|_| panic!("Could not add type"));

        add_extern_module(&vm, "function", |thread| {
            ExternModule::new(
                thread,
                record! {
                    mk_cyclic => primitive!(1, Cyclic)
                },
            )
        });
        vm.run_expr::<OpaqueValue<RootedThread, Hole>>("<top>", "import! function")
            .unwrap();

        // Allocate a `Cyclic` value in the vm
        let mut f: FunctionRef<fn(NoisyDrop) -> OpaqueValue<RootedThread, Cyclic>> = vm
            .get_global("function.mk_cyclic")
            .unwrap_or_else(|err| panic!("{}", err));
        f.call(noisy_drop.clone()).unwrap();

        // When dropping the vm here, the `OpaqueValue<RootedThread, NoisyDrop>` field should not
        // keep the vm alive
    }

    assert!(
        Arc::get_mut(&mut noisy_drop.0).is_some(),
        "The virtual machine and its values were not dropped"
    );
}

#[test]
fn cyclic_userdata_mutable() {
    let _ = ::env_logger::try_init();

    #[derive(Debug, Default, Userdata, Trace)]
    struct Cyclic(gc::mutex::Mutex<Option<OpaqueValue<RootedThread, NoisyDrop>>>);
    impl VmType for Cyclic {
        type Type = Cyclic;
    }

    let mut noisy_drop = NoisyDrop::default();
    {
        let vm = make_vm();

        vm.register_type::<NoisyDrop>("NoisyDrop", &[])
            .unwrap_or_else(|_| panic!("Could not add type"));
        vm.register_type::<Cyclic>("Cyclic", &[])
            .unwrap_or_else(|_| panic!("Could not add type"));

        add_extern_module(&vm, "function", |thread| {
            ExternModule::new(
                thread,
                record! {
                    mk_cyclic => primitive!(1, |()| Cyclic::default()),
                    set => primitive!(2, |cyclic: &Cyclic, noisy| *cyclic.0.lock().unwrap() = Some(noisy))
                },
            )
        });

        let expr = r#"
            let f = import! function
            \noisy ->
                let cyclic = f.mk_cyclic ()
                f.set cyclic noisy
        "#;
        vm.load_script("test", expr).unwrap();

        // Allocate a `Cyclic` value in the vm
        let mut f: FunctionRef<fn(NoisyDrop)> = vm
            .get_global("test")
            .unwrap_or_else(|err| panic!("{}", err));
        f.call(noisy_drop.clone()).unwrap();

        // When dropping the vm here, the `OpaqueValue<RootedThread, NoisyDrop>` field should not
        // keep the vm alive
    }

    assert!(
        Arc::get_mut(&mut noisy_drop.0).is_some(),
        "The virtual machine and its values were not dropped"
    );
}

#[test]
fn child_vm_do_not_cause_undroppable_cycle_normal_drop_order() {
    let _ = ::env_logger::try_init();

    let mut noisy_drop = NoisyDrop::default();
    {
        let vm = RootedThread::new();
        let import = Import::new(gluon::import::DefaultImporter);
        import.add_path("..");
        vm.get_macros().insert(String::from("import"), import);

        let child_vm = vm.new_thread().unwrap();

        vm.register_type::<NoisyDrop>("NoisyDrop", &[])
            .unwrap_or_else(|_| panic!("Could not add type"));

        {
            let mut db = vm.get_database_mut();
            db.set_implicit_prelude(false);
            assert!(!db.compiler_settings().implicit_prelude);
        }
        assert!(!vm.get_database().compiler_settings().implicit_prelude);
        vm.load_script("function", "\\x -> ()")
            .unwrap_or_else(|err| panic!("{}", err));

        {
            let mut f: FunctionRef<fn(NoisyDrop)> = vm
                .get_global("function")
                .unwrap_or_else(|err| panic!("{}", err));
            f.call(noisy_drop.clone())
                .unwrap_or_else(|err| panic!("{}", err));
        }

        drop(child_vm);
        drop(vm);
    }

    assert!(
        Arc::get_mut(&mut noisy_drop.0).is_some(),
        "The virtual machine and its values were not dropped"
    );
}

#[test]
fn child_vm_do_not_cause_undroppable_cycle_reverse_drop_order() {
    let _ = ::env_logger::try_init();

    let mut noisy_drop = NoisyDrop::default();
    {
        let vm = make_vm();
        let child_vm = vm.new_thread().unwrap();

        vm.register_type::<NoisyDrop>("NoisyDrop", &[])
            .unwrap_or_else(|_| panic!("Could not add type"));

        vm.load_script("function", "\\x -> ()").unwrap();

        {
            let mut f: FunctionRef<fn(NoisyDrop)> = vm
                .get_global("function")
                .unwrap_or_else(|err| panic!("{}", err));
            f.call(noisy_drop.clone()).unwrap();
        }

        drop(vm);
        drop(child_vm);
    }

    assert!(
        Arc::get_mut(&mut noisy_drop.0).is_some(),
        "The virtual machine and its values were not dropped"
    );
}

#[test]
fn clone_userdata() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        import! test
    "#;

    #[derive(Debug, Userdata, Trace, VmType, Clone, PartialEq)]
    #[gluon(vm_type = "Test")]
    #[gluon_userdata(clone)]
    struct Test(VmInt);

    let vm = make_vm();
    vm.register_type::<Test>("Test", &[])
        .unwrap_or_else(|_| panic!("Could not add type"));
    add_extern_module(&vm, "test", |thread| ExternModule::new(thread, Test(123)));

    let (result, _) = vm
        .run_expr::<OpaqueValue<RootedThread, Test>>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));

    assert_eq!(*result, Test(123));
}
