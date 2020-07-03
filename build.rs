use std::{
    env,
    fs::File,
    io::{Read, Write},
    path::Path,
};

use {itertools::Itertools, walkdir::WalkDir};

use gluon_base::filename_to_module;

#[cfg(feature = "test")]
mod gen_skeptic {
    use little_skeptic as skeptic;

    use std::{
        env,
        fs::{self, File},
        io::Read,
        path::{Path, PathBuf},
    };

    /// skeptic templates look for `rust` after the opening code fences so writing
    /// ```f#,rust
    /// ```
    /// gives f# syntax highlight while still running the tests through the template
    const TEMPLATE: &'static str = r##"
```rust,skeptic-template

use gluon::vm::api::{Hole, OpaqueValue};
use gluon::{VmBuilder, Thread, ThreadExt};

let _ = ::env_logger::try_init();
let text = r#"{{test}}"#;
let manifest_path = ::std::env::var("CARGO_MANIFEST_DIR").unwrap();
let vm = VmBuilder::new()
    .import_paths(Some(vec![".".into(), manifest_path.into()]))
    .build();
match vm.run_expr::<OpaqueValue<&Thread, Hole>>("example", text) {
    Ok(_value) => (),
    Err(err) => {
        panic!("{}", err);
    }
}
return;
```

"##;

    fn generate_skeptic_tests(file: &Path) -> String {
        println!("cargo:rerun-if-changed={}", file.display());

        // Preprocess the readme to inject the skeptic template needed to to run the examples
        let out_file_name = Path::new(&env::var("OUT_DIR").unwrap()).join(file);

        if let Some(parent_dir) = out_file_name.parent() {
            fs::create_dir_all(parent_dir).unwrap();
        }

        let mut contents = TEMPLATE.as_bytes().into();
        File::open(file)
            .and_then(|mut raw_file| raw_file.read_to_end(&mut contents))
            .unwrap();
        fs::write(&out_file_name, contents).unwrap();
        out_file_name.to_str().expect("UTF-8 string").into()
    }

    pub fn generate() {
        let test_locations: Vec<_> = walkdir::WalkDir::new("book/src")
            .into_iter()
            .filter_map(|e| {
                let e = e.unwrap();
                if e.path().extension().and_then(|p| p.to_str()) == Some("md") {
                    Some(e.path().to_owned())
                } else {
                    None
                }
            })
            .chain(Some(PathBuf::from("README.md")))
            .chain(Some(PathBuf::from("tests/skeptic-template.md")))
            .map(|p| generate_skeptic_tests(&p))
            .collect();

        assert!(
            test_locations.len() > 10,
            "Search for skeptic tests appear to have missed some files"
        );

        let str_vec: Vec<_> = test_locations.iter().map(|s| &s[..]).collect();
        skeptic::Config::default().generate_doc_tests(&str_vec);
    }
}

#[cfg(not(feature = "test"))]
mod gen_skeptic {
    pub fn generate() {
        // If we dont run skeptic we do not need to rebuild anything unless the script itself is
        // changed
        println!("cargo:rerun-if-changed=build.rs");
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

fn generate_std_include() {
    let tuples = WalkDir::new("std")
        .into_iter()
        .filter_map(|entry| entry.ok())
        .filter(|entry| {
            entry.file_type().is_file()
                && entry.path().extension() == Some(::std::ffi::OsStr::new("glu"))
        })
        .map(|entry| {
            let module_name = filename_to_module(entry.path().to_str().expect("Invalid path"));
            format!(
                r#"("{}", include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/{}"))),"#,
                module_name,
                entry.path().display().to_string().replace('\\', "/")
            )
        })
        .format("\n");

    let out_file_name = Path::new(&env::var("OUT_DIR").unwrap()).join("std_modules.rs");
    let mut file = File::create(&out_file_name).unwrap();

    writeln!(
        file,
        r#"
#[cfg(feature = "test")]
static STD_LIBS: &[(&str, &str)] = &[];"#
    )
    .unwrap();
    write!(
        file,
        r#"
#[cfg(not(feature = "test"))]
static STD_LIBS: &[(&str, &str)] = "#
    )
    .unwrap();
    writeln!(file, "&[{}];", tuples).unwrap();
}

fn main() {
    gen_skeptic::generate();

    example_24_up_to_date();
    println!("cargo:rerun-if-changed=examples/24.glu");

    generate_std_include();
    if !env::var("CARGO_FEATURE_TEST").is_ok() {
        println!("cargo:rerun-if-changed=std/");
    }
}
