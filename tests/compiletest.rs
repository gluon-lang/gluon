#![cfg(feature = "nightly")]
extern crate compiletest_rs as compiletest;

use std::env;
use std::path::PathBuf;

fn run_mode(mode: &'static str) {
    // Retrieve the path where library dependencies are output
    let mut out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    loop {
        match out_dir.file_name() {
            Some(name) => {
                match name.to_str() {
                    Some(name) if name == "deps" || name == "debug" => break,
                    _ => (),
                }
            }
            None => break,
        }
        out_dir.pop();
    }

    let mut config = compiletest::default_config();
    let cfg_mode = mode.parse().ok().expect("Invalid mode");

    config.mode = cfg_mode;
    config.src_base = PathBuf::from(format!("tests/{}", mode));
    let dir = out_dir.to_str().unwrap();
    config.target_rustcflags = Some(format!("-L {} -L {}/deps", dir, dir));

    compiletest::run_tests(&config);
}

#[test]
fn compile_test() {
    run_mode("compile-fail");
}
