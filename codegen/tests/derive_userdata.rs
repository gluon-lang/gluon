#[macro_use]
extern crate gluon_codegen;
extern crate gluon;
#[macro_use]
extern crate gluon_vm;

mod init;

use std::sync::Arc;

use gluon::{
    import,
    vm::{self, ExternModule},
    Thread, ThreadExt,
};

use init::new_vm;

#[derive(Userdata, Trace, Debug, VmType)]
#[gluon(vm_type = "WindowHandle")]
struct WindowHandle {
    id: Arc<u64>,
    metadata: Arc<str>,
}

fn load_mod(vm: &Thread) -> vm::Result<ExternModule> {
    vm.register_type::<WindowHandle>("WindowHandle", &[])?;

    let module = record! {
        create_hwnd => primitive!(2, create_hwnd),
        id => primitive!(1, id),
        metadata => primitive!(1, metadata),
    };

    ExternModule::new(vm, module)
}

fn create_hwnd(id: u64, metadata: String) -> WindowHandle {
    WindowHandle {
        id: Arc::new(id),
        metadata: Arc::from(metadata),
    }
}

fn id(hwnd: &WindowHandle) -> u64 {
    *hwnd.id
}

fn metadata(hwnd: &WindowHandle) -> String {
    String::from(&*hwnd.metadata)
}

#[test]
fn userdata() {
    let vm = new_vm();

    import::add_extern_module(&vm, "hwnd", load_mod);

    let script = r#"
        let { assert } = import! std.test
        let { create_hwnd, id, metadata } = import! hwnd

        let hwnd = create_hwnd 0 "Window1"

        let _ = assert (id hwnd == 0)
        assert (metadata hwnd == "Window1")
    "#;

    if let Err(why) = vm.run_expr::<()>("test", script) {
        panic!("{}", why);
    }
}

#[derive(Userdata, Trace, Debug, VmType)]
#[gluon(vm_type = "Empty")]
struct Empty;
