extern crate walkdir;

use std::fmt;
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::Path;

use base::types::ArcType;
use base::metadata::Metadata;
use check::metadata::metadata;
use {new_vm, Compiler, Thread};

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        Io(err: io::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
        Fmt(err: fmt::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
        WalkDir(err: walkdir::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
    }
}

pub type Result<T> = ::std::result::Result<T, Error>;

pub fn generate<W>(out: &mut W, typ: &ArcType, meta: &Metadata) -> Result<()>
where
    W: ?Sized + fmt::Write,
{
    for field in typ.row_iter() {
        let field_name: &str = field.name.as_ref();
        let meta = meta.module.get(field_name).unwrap();
        let field_type = &field.typ;

        writeln!(out, "## {}", field_name)?;

        writeln!(out, "```gluon")?;
        writeln!(out, "{}", field_type)?;
        writeln!(out, "```")?;

        if let Some(ref comment) = meta.comment {
            writeln!(out, "{}", comment)?;
        }

        generate(out, &field.typ, meta)?;
    }
    Ok(())
}

pub fn generate_for_path<P, Q>(thread: &Thread, path: &P, out_path: &Q) -> Result<()>
where
    P: ?Sized + AsRef<Path>,
    Q: ?Sized + AsRef<Path>,
{
    for entry in walkdir::WalkDir::new(path) {
        let entry = entry?;
        if !entry.file_type().is_file() {
            continue;
        }
        let mut input = File::open(entry.path())?;
        let mut content = String::new();
        input.read_to_string(&mut content)?;

        let (expr, typ) = Compiler::new()
            .typecheck_str(thread, "basic", &content, None)
            .unwrap();
        let (meta, _) = metadata(&*thread.get_env(), &expr);

        let mut out = String::new();
        generate(&mut out, &typ, &meta)?;
        let mut doc_file = File::create(out_path.as_ref().join(entry.path().with_extension("md")))?;
        doc_file.write_all(out.as_bytes())?;
    }
    Ok(())
}
