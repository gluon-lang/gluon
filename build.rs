use std::fs::File;
use std::io::{Read, Write};

#[cfg(feature = "skeptic")]
mod gen_skeptic {
    extern crate skeptic;

    use std::env;
    use std::fs::File;
    use std::io::prelude::*;
    use std::path::Path;

    /// skeptic templates look for `rust` after the opening code fences so writing
    /// ```f#,rust
    /// ```
    /// gives f# syntax highlight while still running the tests through the template
    const TEMPLATE: &'static str = r##"
```rust,skeptic-template
extern crate env_logger;
extern crate gluon;

use gluon::vm::api::{{Hole, OpaqueValue}};
use gluon::{{new_vm, Compiler, Thread}};

fn main() {{
    let _ = ::env_logger::init();
    let text = r#\"{}\"#;
    let vm = new_vm();
    match Compiler::new().run_expr::<OpaqueValue<&Thread, Hole>>(&vm, \"example\", text) .sync_or_error() {{
        Ok(_value) => (),
        Err(err) => {{
            panic!(\"{{}}\", err);
        }}
    }}
    return;
}}
```

"##;

    fn generate_skeptic_tests(file: &str) -> String {
        // Preprocess the readme to inject the skeptic template needed to to run the examples
        let out_file_name = Path::new(&env::var("OUT_DIR").unwrap()).join(file);
        let mut contents = TEMPLATE.as_bytes().into();
        File::open(file)
            .and_then(|mut raw_file| raw_file.read_to_end(&mut contents))
            .unwrap();
        File::create(&out_file_name)
            .and_then(|mut out_file| out_file.write(&contents))
            .unwrap();
        out_file_name.to_str().expect("UTF-8 string").into()
    }

    pub fn generate() {
        let test_locations: Vec<_> = ["README.md", "TUTORIAL.md"]
            .iter()
            .cloned()
            .map(generate_skeptic_tests)
            .collect();

        let str_vec: Vec<_> = test_locations.iter().map(|s| &s[..]).collect();
        skeptic::generate_doc_tests(&str_vec);
    }
}

#[cfg(not(feature = "skeptic"))]
mod gen_skeptic {
    pub fn generate() {
        // If we dont run skeptic we do not need to rebuild anything unless the script itself is
        // changed
        println!("cargo:rerun-if-changed=build.rs");
    }
}

/// Safety check to make sure that all .rs files in `tests/` will run
fn check_test_declarations_in_cargo_file() {
    use std::collections::HashSet;
    use std::fs::{read_dir, File};
    use std::io::{BufRead, BufReader};
    use std::ffi::OsStr;

    let cargo_file = BufReader::new(File::open("Cargo.toml").unwrap());

    let tests_in_cargo_file: HashSet<_> = cargo_file
        .lines()
        .map(|line| line.unwrap())
        .filter(|line| line.starts_with("name = \""))
        .map(|line| line.split('"').nth(1).unwrap().to_string())
        .collect();

    for entry in read_dir("tests").unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        if path.extension() == Some(OsStr::new("rs")) {
            let filename = path.file_stem()
                .expect("file_stem")
                .to_str()
                .expect("utf-8 file_stem");
            if !tests_in_cargo_file.contains(filename) {
                panic!(
                    "Test `{}` must be declared in Cargo.toml, otherwise it does not run",
                    filename
                );
            }
        }
    }
}

fn example_24_up_to_date() {
    let mut readme = String::new();
    {
        let mut readme_file = File::open("README.md").unwrap();
        readme_file.read_to_string(&mut readme).unwrap();

        let offset = readme.find("[24 game]").expect("24 game tag");
        let block_start = readme[offset..].find("```").expect("block start") + offset;
        let inside_block_start =
            readme[block_start..].find('\n').expect("inner block start") + block_start + 1;
        let block_end =
            readme[(block_start + 3)..].find("```").expect("block end") + block_start + 3;

        let example_24_in_readme = readme
            .drain(inside_block_start..block_end)
            .collect::<String>();

        {
            let mut file = File::open("examples/24.glu").unwrap();
            let mut example = String::new();
            file.read_to_string(&mut example).unwrap();
            // No need to write anything if it is up to date
            if example == example_24_in_readme {
                return;
            }
            readme.insert_str(inside_block_start, &example);
        }
    }
    let mut readme_file = File::create("README.md").unwrap();
    readme_file.write_all(readme.as_bytes()).unwrap();
}

fn main() {
    gen_skeptic::generate();

    check_test_declarations_in_cargo_file();

    example_24_up_to_date();
    println!("cargo:rerun-if-changed=examples/24.glu");
}
