#[macro_use]
extern crate gluon_codegen;
extern crate gluon;
extern crate serde;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate gluon_vm;

mod init;

use gluon::base::types::{AppVec, ArcType, Type};
use gluon::vm::api::{self, generic, Generic, VmType};
use gluon::vm::{self, thread::ThreadInternal, ExternModule};
use gluon::{import, Compiler, Thread};
use init::new_vm;

#[derive(Getable, Debug, Serialize, Deserialize)]
enum TupleEnum {
    Variant,
    OtherVariant,
    One(u32),
    LotsOfTupleThings(i32, String, f64),
}

impl VmType for TupleEnum {
    type Type = TupleEnum;

    fn make_type(vm: &Thread) -> ArcType {
        vm.global_env()
            .get_env()
            .find_type_info("types.TupleEnum")
            .unwrap()
            .into_owned()
            .into_type()
    }
}

fn load_tuple_enum_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        tuple_enum_to_str => primitive!(1 tuple_enum_to_str),
    };

    ExternModule::new(vm, module)
}

fn tuple_enum_to_str(val: TupleEnum) -> String {
    format!("{:?}", val)
}

#[test]
fn enum_tuple_variants() {
    let vm = new_vm();
    let mut compiler = Compiler::new();

    let src = api::typ::make_source::<TupleEnum>(&vm).unwrap();
    compiler.load_script(&vm, "types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_tuple_enum_mod);

    let script = r#"
        let { TupleEnum } = import! types
        let { tuple_enum_to_str } = import! functions
        let { assert } = import! std.test

        assert (tuple_enum_to_str Variant == "Variant")
        assert (tuple_enum_to_str OtherVariant == "OtherVariant")
        assert (tuple_enum_to_str (One 1) == "One(1)")
        assert (tuple_enum_to_str (LotsOfTupleThings 42 "Text" 0.0) == "LotsOfTupleThings(42, \"Text\", 0.0)")
    "#;

    if let Err(why) = compiler.run_expr::<()>(&vm, "test", script) {
        panic!("{}", why);
    }
}

#[derive(Getable, Debug, Serialize, Deserialize)]
enum StructEnum {
    OneField { field: i32 },
    TwoFields { name: String, val: f64 },
}

impl VmType for StructEnum {
    type Type = StructEnum;

    fn make_type(vm: &Thread) -> ArcType {
        vm.global_env()
            .get_env()
            .find_type_info("types.StructEnum")
            .unwrap()
            .into_owned()
            .into_type()
    }
}

fn load_struct_enum_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        struct_enum_to_str => primitive!(1 struct_enum_to_str),
    };

    ExternModule::new(vm, module)
}

fn struct_enum_to_str(val: StructEnum) -> String {
    format!("{:?}", val)
}

#[test]
fn enum_struct_variants() {
    let vm = new_vm();
    let mut compiler = Compiler::new();

    let src = api::typ::make_source::<StructEnum>(&vm).unwrap();
    compiler.load_script(&vm, "types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_struct_enum_mod);

    let script = r#"
        let { StructEnum } = import! types
        let { struct_enum_to_str } = import! functions
        let { assert } = import! std.test

        assert (struct_enum_to_str (OneField 1337) == "OneField { field: 1337 }")
        assert (struct_enum_to_str (TwoFields "Pi" 3.14) == "TwoFields { name: \"Pi\", val: 3.14 }")
    "#;

    if let Err(why) = compiler.run_expr::<()>(&vm, "test", script) {
        panic!("{}", why);
    }
}

#[derive(Getable)]
enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<L, R> VmType for Either<L, R>
where
    L: 'static + VmType,
    R: 'static + VmType,
{
    type Type = Either<L, R>;

    fn make_type(vm: &Thread) -> ArcType {
        let ty = vm.global_env()
            .get_env()
            .find_type_info("types.Either")
            .unwrap()
            .into_owned()
            .into_type();

        let mut vec = AppVec::new();
        vec.push(L::make_type(vm));
        vec.push(R::make_type(vm));
        Type::app(ty, vec)
    }
}

fn load_either_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        left => primitive!(1 left),
        extract_str => primitive!(1 extract_str),
    };

    ExternModule::new(vm, module)
}

type GenericL = Generic<generic::L>;
type GenericR = Generic<generic::R>;

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
    let vm = new_vm();
    let mut compiler = Compiler::new();

    let src = r#"
        type Either l r = | Left l | Right r
        { Either }
    "#;

    compiler.load_script(&vm, "types", src).unwrap();
    import::add_extern_module(&vm, "functions", load_either_mod);

    let script = r#"
        let { Either } = import! types
        let { left, extract_str } = import! functions
        let { assert } = import! std.test

        assert (left (Left 42) == Some 42)
        assert (left (Right 0.0) == None)

        assert (extract_str (Left "left") == "left")
        assert (extract_str (Right "right") == "right")
    "#;

    if let Err(why) = compiler.run_expr::<()>(&vm, "test", script) {
        panic!("{}", why);
    }
}

#[derive(Getable)]
struct LifetimeStruct<'a> {
    _str: &'a str,
}

// TODO: impl tests for lifetimes, this requires
// a safe interface for Getable::from_value()

#[derive(Getable, Debug, Serialize, Deserialize)]
struct Struct {
    string: String,
    int: i32,
    tuple: (f64, f64),
}

impl VmType for Struct {
    type Type = Struct;

    fn make_type(vm: &Thread) -> ArcType {
        vm.global_env()
            .get_env()
            .find_type_info("types.Struct")
            .unwrap()
            .into_owned()
            .into_type()
    }
}

fn load_struct_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        struct_to_str => primitive!(1 struct_to_str),
    };

    ExternModule::new(vm, module)
}

fn struct_to_str(val: Struct) -> String {
    format!("{:?}", val)
}

#[test]
fn struct_derive() {
    let vm = new_vm();
    let mut compiler = Compiler::new();

    let src = api::typ::make_source::<Struct>(&vm).unwrap();
    compiler.load_script(&vm, "types", &src).unwrap();
    import::add_extern_module(&vm, "functions", load_struct_mod);

    let script = r#"
        let { Struct } = import! types
        let { struct_to_str } = import! functions
        let { assert } = import! std.test

        assert (struct_to_str { string = "test", int = 55, tuple = (0.0, 1.0) } == "Struct { string: \"test\", int: 55, tuple: (0.0, 1.0) }")
    "#;

    if let Err(why) = compiler.run_expr::<()>(&vm, "test", script) {
        panic!("{}", why);
    }
}
