#![cfg(feature = "nightly")]
extern crate compiletest_rs as compiletest;

use std::path::PathBuf;

fn run_mode(mode: &'static str) {
    let mut config = compiletest::default_config();
    let cfg_mode = mode.parse().ok().expect("Invalid mode");

    config.mode = cfg_mode;
    config.src_base = PathBuf::from(format!("tests/{}", mode));
    // Pass flags for both c-api and without so both `cargo test ...` and
    // `(cd c-api && cargo test ... )` works
    config.target_rustcflags = Some("-L c-api/target/debug -L c-api/target/debug/deps \
                                     -L target/debug -L target/debug/deps".to_string());

    compiletest::run_tests(&config);
}

#[test]
fn compile_test() {
    run_mode("compile-fail");
}
