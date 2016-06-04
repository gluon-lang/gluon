extern crate skeptic;

use std::io::prelude::*;
use std::fs::File;
use std::path::Path;

const TEMPLATE: &'static str = r##"
```rust,skeptic-template
extern crate env_logger;
extern crate gluon;

use gluon::vm::api::generic::A;
use gluon::vm::api::Generic;
use gluon::{{new_vm, Compiler}};

fn main() {{
    let _ = ::env_logger::init();
    let text = r#\"{}\"#;
    let vm = new_vm();
    match Compiler::new().run_expr::<Generic<A>>(&vm, \"example\", text) {{
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
    let out_file_name = Path::new(env!("OUT_DIR")).join(file);
    let mut contents = TEMPLATE.as_bytes().into();
    File::open(file)
        .and_then(|mut raw_file| raw_file.read_to_end(&mut contents))
        .unwrap();
    File::create(&out_file_name)
        .and_then(|mut out_file| out_file.write(&contents))
        .unwrap();
    out_file_name.to_str().expect("UTF-8 string").into()
}

fn main() {
    let test_locations: Vec<_> = ["README.md", "TUTORIAL.md"]
                                     .iter()
                                     .cloned()
                                     .map(generate_skeptic_tests)
                                     .collect();

    let str_vec: Vec<_> = test_locations.iter().map(|s| &s[..]).collect();
    skeptic::generate_doc_tests(&str_vec);
}
