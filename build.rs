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
        println!("rerun-if-changed=build.rs");
    }
}

fn main() {
    gen_skeptic::generate();
}
