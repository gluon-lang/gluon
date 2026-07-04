use gluon::{self, RootedThread, import::Import};

pub fn new_vm() -> RootedThread {
    let vm = gluon::VmBuilder::new()
        .import_paths(Some(vec!["..".into()]))
        .build();
    let import = vm.get_macros().get("import");
    import
        .as_ref()
        .and_then(|import| import.downcast_ref::<Import>())
        .expect("Import macro")
        .add_path("..");

    vm
}
