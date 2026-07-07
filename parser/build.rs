extern crate lalrpop;

fn main() {
    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .process()
        .unwrap();

    println!("cargo:rerun-if-changed=src/grammar.lalrpop");
}
