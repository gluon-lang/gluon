#[macro_use]
extern crate clap;
extern crate env_logger;
extern crate failure;

extern crate gluon;
extern crate gluon_doc;

fn main() {
    if let Err(err) = main_() {
        eprintln!("{}", err);
    }
}

fn main_() -> Result<(), failure::Error> {
    env_logger::init();

    let matches = clap_app!(gluon_doc =>
        (version: crate_version!())
        (long_version:
            concat!(
                crate_version!(), "\n",
                "commit: ", env!("GIT_HASH")
            )
        )
        (about: "Documents gluon source code")
        (@arg INPUT: +required "Documents the file or directory")
        (@arg OUTPUT: +required "Outputs the documentation to this directory")
    ).get_matches();

    let input = matches.value_of("INPUT").expect("INPUT");
    let output = matches.value_of("OUTPUT").expect("OUTPUT");
    gluon_doc::generate_for_path(&gluon::new_vm(), input, output)?;
    Ok(())
}
