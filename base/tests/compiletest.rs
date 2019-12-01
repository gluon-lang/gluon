#![cfg(feature = "nightly")]
extern crate compiletest_rs as compiletest;
extern crate env_logger;

use std::fs;
use std::path::{Path, PathBuf};

fn lib_dir(out_dir: &Path, lib_name: &str) -> PathBuf {
    // Just loading gluon through -L dir does not work as we compile gluon with different sets of
    // flags which gives ambiguity errors.
    // Instead retrieve the latest compiled gluon library which should usually be the correct one
    let mut gluon_rlibs: Vec<_> = fs::read_dir(out_dir.join("deps"))
        .unwrap()
        .filter_map(|entry| {
            let entry = entry.expect("dir entry");
            if entry
                .path()
                .to_str()
                .map_or(false, |name| name.contains(lib_name))
            {
                Some(entry)
            } else {
                None
            }
        })
        .collect();
    gluon_rlibs.sort_by(|l, r| {
        l.metadata()
            .unwrap()
            .modified()
            .unwrap()
            .cmp(&r.metadata().unwrap().modified().unwrap())
    });
    gluon_rlibs.last().expect("libgluon not found").path()
}

fn run_mode(mode: &'static str) {
    // Retrieve the path where library dependencies are output
    let out_dir = PathBuf::from("../target/debug");
    let gluon_base_rlib = lib_dir(&out_dir, "libgluon_base-");

    let mut config = compiletest::Config::default();
    let cfg_mode = mode.parse().ok().expect("Invalid mode");

    config.verbose = true;
    config.mode = cfg_mode;
    config.src_base = PathBuf::from(format!("tests/{}", mode));
    config.target_rustcflags = Some(format!(
        "-L {}/deps --extern gluon_base={}",
        out_dir.display(),
        gluon_base_rlib.display(),
    ));
    println!("{}", config.target_rustcflags.as_ref().unwrap());
    compiletest::run_tests(&config);
}

#[test]
fn compile_test() {
    let _ = env_logger::try_init();
    run_mode("compile-fail");
}
