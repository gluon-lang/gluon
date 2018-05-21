#[macro_use]
extern crate gluon_codegen;
extern crate gluon;
extern crate serde;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate gluon_vm;

use gluon::vm::api::{self, VmType};
use gluon::vm::{self, ExternModule, thread::ThreadInternal};
use gluon::{new_vm, Compiler, import, Thread};
use gluon::base::types::ArcType;

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
