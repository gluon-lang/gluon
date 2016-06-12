extern crate env_logger;
extern crate gluon;

use gluon::vm::thread::RootedThread;
use gluon::import::Import;
use gluon::Compiler;

fn make_vm() -> RootedThread {
    let vm = ::gluon::new_vm();
    let import = vm.get_macros().get("import");
    import.as_ref()
          .and_then(|import| import.downcast_ref::<Import>())
          .expect("Import macro")
          .add_path("..");
    vm
}

#[test]
fn metadata_from_other_module() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    let text = r#"
let { List, id } = import "std/prelude.hs"
{ List, id }
"#;
    Compiler::new().load_script(&vm, "test", text).unwrap();
    
    let env = vm.get_env();
    assert!(env.get_metadata("test.id").is_ok());
    assert!(env.get_metadata("test.List").is_ok());
}
