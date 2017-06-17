extern crate lalrpop;

fn main() {
    lalrpop::Configuration::new().process_current_dir().unwrap();
    println!("cargo:rerun-if-changed=src/grammar.lalrpop");
}
