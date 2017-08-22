extern crate lalrpop;

fn main() {
    ::std::env::set_var("LALRPOP_LANE_TABLE", "disabled");

    lalrpop::Configuration::new().process_current_dir().unwrap();
    println!("cargo:rerun-if-changed=src/grammar.lalrpop");
}
