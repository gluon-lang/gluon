#[cfg(feature = "test")]
mod build {
    extern crate lalrpop;

    pub fn main() {
        lalrpop::Configuration::new()
            .use_cargo_dir_conventions()
            .process_file("src/core/grammar.lalrpop")
            .unwrap();

        println!("cargo:rerun-if-changed=src/core/grammar.lalrpop");
    }
}

#[cfg(not(feature = "test"))]
mod build {
    pub fn main() {}
}

fn main() {
    build::main();
}
