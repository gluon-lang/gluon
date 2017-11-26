extern crate lalrpop;

fn main() {
    ::std::env::set_var("LALRPOP_LANE_TABLE", "disabled");

    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .process_file("src/grammar.lalrpop")
        .unwrap();
    println!("cargo:rerun-if-changed=grammar.lalrpop");
}
