extern crate gluon;
#[macro_use]
extern crate gluon_codegen;
#[macro_use]
extern crate gluon_vm;

mod init;

use gluon::{
    import,
    vm::{self, ExternModule},
    Thread, ThreadExt,
};
use init::new_vm;

#[derive(Debug, PartialEq, Getable, Pushable, VmType)]
struct Struct {
    string: String,
    number: u32,
    vec: Vec<f64>,
}

fn load_struct_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        new_struct => primitive!(1, new_struct),
    };

    ExternModule::new(vm, module)
}

fn new_struct(_: ()) -> Struct {
    Struct {
        string: "hello".to_owned(),
        number: 1,
        vec: vec![1.0, 2.0, 3.0],
    }
}

#[test]
fn normal_struct() {
    let vm = new_vm();
    import::add_extern_module(&vm, "functions", load_struct_mod);

    let script = r#"
        let { new_struct } = import! functions
        
        new_struct ()
    "#;

    let (s, _) = vm
        .run_expr::<Struct>("test", script)
        .unwrap_or_else(|why| panic!("{}", why));

    assert_eq!(
        s,
        Struct {
            string: "hello".into(),
            number: 1,
            vec: vec![1.0, 2.0, 3.0],
        }
    );
}

#[derive(Debug, PartialEq, VmType, Pushable, Getable)]
struct Newtype(pub Struct);

fn load_newtype_mod(vm: &Thread) -> vm::Result<ExternModule> {
    let module = record! {
        newtype_id => primitive!(1, newtype_id),
    };

    ExternModule::new(vm, module)
}

fn newtype_id(val: Newtype) -> Newtype {
    val
}

#[test]
fn newtype() {
    let vm = new_vm();
    import::add_extern_module(&vm, "functions", load_newtype_mod);

    // newtypes should map to the inner type
    let script = r#"
        let { newtype_id } = import! functions

        newtype_id { string = "test", number = 42, vec = [1.0, 1.0, 2.0, 3.0, 5.0] }
    "#;

    let (s, _) = vm
        .run_expr::<Newtype>("test", script)
        .unwrap_or_else(|why| panic!("{}", why));

    assert_eq!(
        s,
        Newtype(Struct {
            string: "test".into(),
            number: 42,
            vec: vec![1.0, 1.0, 2.0, 3.0, 5.0],
        })
    );
}
