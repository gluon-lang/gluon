extern crate env_logger;
extern crate opener;
extern crate rayon;
extern crate structopt;

extern crate gluon;
extern crate gluon_doc;

use std::path::Path;

use structopt::StructOpt;

fn main() {
    if let Err(err) = main_() {
        eprintln!("{}", err);
    }
}

fn main_() -> Result<(), anyhow::Error> {
    env_logger::init();

    let opt = gluon_doc::Opt::from_args();

    if let Some(jobs) = opt.jobs {
        rayon::ThreadPoolBuilder::new()
            .num_threads(jobs)
            .build_global()?;
    }

    gluon_doc::generate(&gluon_doc::Options::from(&opt), &gluon::new_vm())?;

    if opt.open {
        let path = Path::new(&opt.output)
            .join(&opt.input)
            .with_extension("html");
        eprintln!("Opening {}", path.display());
        opener::open(path)?;
    }

    Ok(())
}
