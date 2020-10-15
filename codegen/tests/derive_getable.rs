extern crate env_logger;
#[macro_use]
extern crate gluon_codegen;
extern crate gluon;
extern crate serde;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate gluon_vm;

mod init;

use gluon::{
    import,
    vm::{
        self,
        api::{
            self,
            generic::{self, L, R},
            OpaqueValue,
        },
        ExternModule,
    },
    RootedThread, Thread, ThreadExt,
};
use init::new_vm;

#[derive(Getable, VmType, Debug, Serialize, Deserialize)]
#[gluon(vm_type = "types.TupleEnum")]
enum TupleEnum {
    Variant,
    OtherVariant,
    One(u32),
    LotsOfTupleThings(i32, String, f64),
}

fn load_tuple_enum_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        tuple_enum_to_str => primitive!(1, tuple_enum_to_str),
    };

    ExternModule::new(vm, module)
}

fn tuple_enum_to_str(val: TupleEnum) -> String {
    format!("{:?}", val)
}

#[test]
fn enum_tuple_variants() {
    let vm = new_vm();

    let src = api::typ::make_source::<TupleEnum>(&vm).unwrap();
    vm.load_script("types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_tuple_enum_mod);

    let script = r#"
        let { TupleEnum } = import! types
        let { tuple_enum_to_str } = import! functions
        let { assert } = import! std.test

        let _ = assert (tuple_enum_to_str Variant == "Variant")
        let _ = assert (tuple_enum_to_str OtherVariant == "OtherVariant")
        let _ = assert (tuple_enum_to_str (One 1) == "One(1)")
        assert (tuple_enum_to_str (LotsOfTupleThings 42 "Text" 0.0) == "LotsOfTupleThings(42, \"Text\", 0.0)")
    "#;

    if let Err(why) = vm.run_expr::<()>("test", script) {
        panic!("{}", why);
    }
}

#[derive(Getable, VmType, Debug, Serialize, Deserialize)]
#[gluon(vm_type = "types.StructEnum")]
enum StructEnum {
    OneField { field: i32 },
    TwoFields { name: String, val: f64 },
}

fn load_struct_enum_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        struct_enum_to_str => primitive!(1, struct_enum_to_str),
    };

    ExternModule::new(vm, module)
}

fn struct_enum_to_str(val: StructEnum) -> String {
    format!("{:?}", val)
}

#[test]
fn enum_struct_variants() {
    let vm = new_vm();

    let src = api::typ::make_source::<StructEnum>(&vm).unwrap();
    println!("Types:\n{}", src);
    vm.load_script("types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_struct_enum_mod);

    let script = r#"
        let { StructEnum } = import! types
        let { struct_enum_to_str } = import! functions
        let { assert } = import! std.test

        let _ = assert (struct_enum_to_str (OneField { field = 1337 }) == "OneField { field: 1337 }")
        assert (struct_enum_to_str (TwoFields { name = "Pi", val = 3.14 }) == "TwoFields { name: \"Pi\", val: 3.14 }")
    "#;

    if let Err(why) = vm.run_expr::<()>("test", script) {
        panic!("{}", why);
    }
}

#[derive(Getable, VmType)]
enum Either<L, R> {
    Left(L),
    Right(R),
}

fn load_either_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        type Either l r => Either<L, R>,
        left => primitive!(1, left),
        extract_str => primitive!(1, extract_str),
    };

    ExternModule::new(vm, module)
}

type GenericL = OpaqueValue<RootedThread, generic::L>;
type GenericR = OpaqueValue<RootedThread, generic::R>;

fn left(either: Either<GenericL, GenericR>) -> Option<GenericL> {
    match either {
        Either::Left(left) => Some(left),
        _ => None,
    }
}

fn extract_str(either: Either<String, String>) -> String {
    match either {
        Either::Left(string) => string,
        Either::Right(string) => string,
    }
}

#[test]
fn enum_generic_variants() {
    let _ = env_logger::try_init();

    let vm = new_vm();

    import::add_extern_module(&vm, "functions", load_either_mod);

    let script = r#"
        let { Either, left, extract_str } = import! functions
        let { assert } = import! std.test

        let l: Either Int Float  = Left 42
        let _ = assert (left l == Some 42)
        let r: Either Int Float  = Right 0.0
        let _ = assert (left r == None)

        let _ = assert (extract_str (Left "left") == "left")
        assert (extract_str (Right "right") == "right")
    "#;

    if let Err(why) = vm.run_expr::<()>("test", script) {
        panic!("{}", why);
    }
}

#[derive(Getable, Pushable, VmType)]
enum Enum {
    TestVariant,
    TestVariant2(i32),
}

#[test]
fn derive_generates_same_type_as_gluon_define() {
    let _ = env_logger::try_init();

    let vm = new_vm();
    vm.get_database_mut().implicit_prelude(false);

    import::add_extern_module(&vm, "test", |vm| {
        ExternModule::new(vm, primitive!(1, "test", |_: Enum| ()))
    });

    let script = r#"
        let test = import! test

        type Enum = | TestVariant | TestVariant2 Int

        let _ = test TestVariant
        test (TestVariant2 123)
    "#;

    if let Err(why) = vm.run_expr::<()>("test", script) {
        panic!("{}", why);
    }
}

#[derive(Getable)]
struct LifetimeStruct<'a> {
    _str: &'a str,
}

// TODO: impl tests for lifetimes, this requires
// a safe interface for Getable::from_value()

#[derive(Getable, VmType, Debug, Serialize, Deserialize)]
#[gluon(vm_type = "types.Struct")]
struct Struct {
    string: String,
    int: i32,
    tuple: (f64, f64),
}

fn load_struct_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        struct_to_str => primitive!(1, struct_to_str),
    };

    ExternModule::new(vm, module)
}

fn struct_to_str(val: Struct) -> String {
    format!("{:?}", val)
}

#[test]
fn struct_derive() {
    let vm = new_vm();

    let src = api::typ::make_source::<Struct>(&vm).unwrap();
    vm.load_script("types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_struct_mod);

    let script = r#"
        let { Struct } = import! types
        let { struct_to_str } = import! functions
        let { assert } = import! std.test

        assert (struct_to_str { string = "test", int = 55, tuple = (0.0, 1.0) } == "Struct { string: \"test\", int: 55, tuple: (0.0, 1.0) }")
    "#;

    if let Err(why) = vm.run_expr::<()>("test", script) {
        panic!("{}", why);
    }
}

#[derive(Serialize, Deserialize, Debug, VmType, Getable)]
#[gluon(vm_type = "types.TupleStruct")]
struct TupleStruct(i32, i32);

fn load_tuple_struct_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        tuple_struct_to_str => primitive!(1, tuple_struct_to_str),
    };

    ExternModule::new(vm, module)
}

fn tuple_struct_to_str(val: TupleStruct) -> String {
    format!("{:?}", val)
}

#[test]
fn tuple_struct_derive() {
    let vm = new_vm();

    let src = r#"
        type TupleStruct = (Int, Int)
        { TupleStruct }
    "#;

    vm.load_script("types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_tuple_struct_mod);

    let script = r#"
        let { TupleStruct } = import! types
        let { tuple_struct_to_str } = import! functions
        let { assert } = import! std.test

        assert (tuple_struct_to_str (1, 2) == "TupleStruct(1, 2)")
    "#;

    if let Err(why) = vm.run_expr::<()>("test", script) {
        panic!("{}", why);
    }
}
