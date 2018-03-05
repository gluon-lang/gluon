extern crate failure;
extern crate walkdir;

use std::fmt::{self, Write as WriteFmt};
use std::fs::{create_dir_all, File};
use std::io::{Read, Write};
use std::path::Path;

use self::failure::ResultExt;

use base::filename_to_module;
use base::types::ArcType;
use base::metadata::Metadata;
use check::metadata::metadata;
use {Compiler, Thread};

pub type Error = failure::Error;
pub type Result<T> = ::std::result::Result<T, Error>;

fn generate_field<W>(
    out: &mut W,
    field_name: &str,
    typ: &ArcType,
    comment: Option<&str>,
) -> Result<()>
where
    W: ?Sized + fmt::Write,
{
    writeln!(out, "### {}", field_name)?;

    writeln!(out, "```gluon")?;
    writeln!(out, "{}", typ)?;
    writeln!(out, "```")?;

    if let Some(comment) = comment {
        writeln!(out, "{}", comment)?;
    }
    writeln!(out)?;
    Ok(())
}

pub fn generate<W>(out: &mut W, typ: &ArcType, meta: &Metadata) -> Result<()>
where
    W: ?Sized + fmt::Write,
{
    if typ.type_field_iter().next().is_some() {
        writeln!(out, "## Types")?;
        writeln!(out)?;
    }
    for field in typ.type_field_iter() {
        let field_name: &str = field.name.as_ref();
        let field_type = &field.typ.unresolved_type();
        let comment = meta.module
            .get(field_name)
            .and_then(|meta| meta.comment.as_ref().map(|s| &s[..]));
        generate_field(out, field_name, field_type, comment)?;
    }

    if typ.row_iter().next().is_some() {
        writeln!(out, "## Values")?;
        writeln!(out)?;
    }

    for field in typ.row_iter() {
        let field_name: &str = field.name.as_ref();
        let field_type = &field.typ;
        let comment = meta.module
            .get(field_name)
            .and_then(|meta| meta.comment.as_ref().map(|s| &s[..]));
        generate_field(out, field_name, field_type, comment)?;
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
        if !entry.file_type().is_file()
            || entry.path().extension().and_then(|ext| ext.to_str()) != Some("glu")
        {
            continue;
        }
        let mut input = File::open(&*entry.path()).with_context(|err| {
            format!(
                "Unable to open gluon file `{}`: {}",
                entry.path().display(),
                err
            )
        })?;
        let mut content = String::new();
        input.read_to_string(&mut content)?;

        let (expr, typ) = Compiler::new().typecheck_str(thread, "basic", &content, None)?;
        let (meta, _) = metadata(&*thread.get_env(), &expr);

        let mut out = String::new();
        if let Some(module_path) = entry.path().to_str() {
            writeln!(out, "# {}", filename_to_module(module_path))?;
            writeln!(out)?;
        }
        generate(&mut out, &typ, &meta)?;

        create_dir_all(
            out_path
                .as_ref()
                .join(entry.path().parent().unwrap_or(Path::new(""))),
        )?;

        let out_path = out_path.as_ref().join(entry.path().with_extension("md"));
        let mut doc_file = File::create(&*out_path).with_context(|err| {
            format!(
                "Unable to open output file `{}`: {}",
                out_path.display(),
                err
            )
        })?;
        doc_file.write_all(out.as_bytes())?;
    }
    Ok(())
}
