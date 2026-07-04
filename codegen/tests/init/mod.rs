use gluon::{self, RootedThread, import::Import};

pub fn new_vm() -> RootedThread {
    if ::std::env::var("GLUON_PATH").is_err() {
        // FIXME: Audit that the environment access only happens in single-threaded code.
        unsafe { ::std::env::set_var("GLUON_PATH", "..") };
    }

    let vm = gluon::new_vm();
    let import = vm.get_macros().get("import");
    import
        .as_ref()
        .and_then(|import| import.downcast_ref::<Import>())
        .expect("Import macro")
        .add_path("..");

    vm
}
