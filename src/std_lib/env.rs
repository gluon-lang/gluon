//! Module containing bindings to rust's `std::env` module.
use crate::real_std::{
    env,
    path::{Path, PathBuf},
};

use crate::vm::{self, ExternModule, api::IO, thread::Thread};

fn args() -> IO<Vec<String>> {
    IO::Value(env::args().collect())
}

fn current_dir() -> IO<PathBuf> {
    env::current_dir().into()
}

fn current_exe() -> IO<PathBuf> {
    env::current_exe().into()
}

fn join_paths(paths: Vec<&Path>) -> IO<PathBuf> {
    env::join_paths(paths).map(PathBuf::from).into()
}

fn set_current_dir(dir: &str) -> IO<()> {
    env::set_current_dir(dir).into()
}

fn split_paths(path: &str) -> IO<Vec<PathBuf>> {
    IO::Value(env::split_paths(path).collect())
}

fn temp_dir() -> IO<PathBuf> {
    IO::Value(env::temp_dir())
}

fn var(key: &str) -> IO<String> {
    env::var(key).into()
}

field_decl! { key, value }

type Entry = record_type! {
    key => String,
    value => String
};

fn vars() -> IO<Vec<Entry>> {
    IO::Value(
        env::vars()
            .map(|(key, value)| record_no_decl! { key => key, value => value })
            .collect(),
    )
}

mod std {
    pub mod env {
        pub use crate::std_lib::env as prim;
    }
}

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            consts => record! {
                arch => crate::real_std::env::consts::ARCH,
                dll_extension => crate::real_std::env::consts::DLL_EXTENSION,
                dll_prefix => crate::real_std::env::consts::DLL_PREFIX,
                dll_suffix => crate::real_std::env::consts::DLL_SUFFIX,
                exe_extension => crate::real_std::env::consts::EXE_EXTENSION,
                family => crate::real_std::env::consts::FAMILY,
                os => crate::real_std::env::consts::OS,
            },
            args => primitive!(0, std::env::prim::args),
            current_dir => primitive!(0, std::env::prim::current_dir),
            current_exe => primitive!(0, std::env::prim::current_exe),
            join_paths => primitive!(1, std::env::prim::join_paths),
            set_current_dir => primitive!(1, std::env::prim::set_current_dir),
            split_paths => primitive!(1, std::env::prim::split_paths),
            temp_dir => primitive!(0, std::env::prim::temp_dir),
            var => primitive!(1, std::env::prim::var),
            vars => primitive!(0, std::env::prim::vars),
        },
    )
}
