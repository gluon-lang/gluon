use gluon::{import::Import, vm::thread::RootedThread, ThreadExt};

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
fn metadata_from_other_module() {
    let _ = ::env_logger::try_init();
    let vm = make_vm();
    let text = r#"
let { List, of }  = import! std.list
{ List, of }
"#;
    vm.load_script("test", text)
        .unwrap_or_else(|err| panic!("{}", err));

    let env = vm.get_env();
    assert!(env.get_metadata("test.of").is_ok());
    assert!(env.get_metadata("test.List").is_ok());
}
