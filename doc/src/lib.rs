#[macro_use]
extern crate clap;
extern crate failure;
extern crate handlebars;
extern crate itertools;
extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;
#[macro_use]
extern crate structopt;
#[macro_use]
extern crate lazy_static;
extern crate pretty;
extern crate pulldown_cmark;
extern crate regex;
extern crate walkdir;

#[macro_use]
extern crate log;

extern crate gluon;

use std::fs::{create_dir_all, File};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use failure::ResultExt;

use itertools::Itertools;

use handlebars::{Handlebars, Helper, Output, RenderContext, RenderError};

use serde::Deserialize;

use pretty::{Arena, DocAllocator};

use gluon::base::filename_to_module;
use gluon::base::metadata::Metadata;
use gluon::base::types::{ArcType, ArgType, Type};
use gluon::check::metadata::metadata;
use gluon::{Compiler, Thread};

pub type Error = failure::Error;
pub type Result<T> = ::std::result::Result<T, Error>;

#[derive(Serialize, PartialEq, Debug)]
pub struct Module {
    pub name: String,
    pub comment: String,
    pub record: Record,
}

#[derive(Serialize, PartialEq, Debug)]
pub struct Record {
    pub types: Vec<Field>,
    pub values: Vec<Field>,
}

#[derive(Serialize, PartialEq, Debug)]
pub struct Argument {
    pub implicit: bool,
    pub name: String,
}

#[derive(Serialize, PartialEq, Debug)]
pub struct Field {
    pub name: String,
    pub args: Vec<Argument>,
    #[serde(rename = "type")]
    pub typ: String,
    pub comment: String,
}

fn print_type(typ: &ArcType) -> String {
    let arena = Arena::new();
    let mut doc = typ.pretty(&arena);
    match **typ {
        Type::Record(_) => (),
        Type::Variant(_) => doc = arena.newline().append(doc).nest(4),
        _ => {
            doc = doc.nest(4);
        }
    }
    doc.group().1.pretty(80).to_string()
}

pub fn record(typ: &ArcType, meta: &Metadata) -> Record {
    Record {
        types: typ
            .type_field_iter()
            .map(|field| Field {
                name: field.name.definition_name().to_string(),
                args: field
                    .typ
                    .params()
                    .iter()
                    .map(|gen| Argument {
                        implicit: false,
                        name: gen.id.to_string(),
                    })
                    .collect(),
                typ: print_type(&field.typ.unresolved_type().remove_forall()),
                comment: meta
                    .module
                    .get(AsRef::<str>::as_ref(&field.name))
                    .and_then(|meta| meta.comment.as_ref().map(|s| &s.content[..]))
                    .unwrap_or("")
                    .to_string(),
            })
            .collect(),

        values: typ
            .row_iter()
            .map(|field| {
                let meta_opt = meta.module.get(AsRef::<str>::as_ref(&field.name));
                Field {
                    name: field.name.definition_name().to_string(),
                    args: meta_opt
                        .map(|meta| {
                            meta.args
                                .iter()
                                .map(|arg| Argument {
                                    implicit: arg.arg_type == ArgType::Implicit,
                                    name: arg.name.definition_name().to_string(),
                                })
                                .collect()
                        })
                        .unwrap_or_default(),
                    typ: print_type(&field.typ),

                    comment: meta_opt
                        .and_then(|meta| meta.comment.as_ref().map(|s| &s.content[..]))
                        .unwrap_or("")
                        .to_string(),
                }
            })
            .collect(),
    }
}

#[derive(Serialize, Debug)]
pub struct TemplateModule<'a> {
    pub name: &'a str,
    pub comment: &'a str,
    pub record: &'a Record,
    pub sibling_modules: Vec<&'a str>,
}

const INDEX_TEMPLATE: &str = "index";
const MODULE_TEMPLATE: &str = "module";

fn handlebars() -> Result<Handlebars> {
    let mut reg = Handlebars::new();

    reg.register_template_string(INDEX_TEMPLATE, include_str!("doc/index.html"))?;
    reg.register_template_string(MODULE_TEMPLATE, include_str!("doc/module.html"))?;

    fn symbol_link(
        h: &Helper,
        _: &Handlebars,
        rc: &mut RenderContext,
        out: &mut Output,
    ) -> ::std::result::Result<(), RenderError> {
        let current_module = &rc.context().data()["name"]
            .as_str()
            .expect("name")
            .to_string();

        let param = String::deserialize(h.param(0).unwrap().value())?;
        let skipped = if rc.get_root_template_name().map(|s| &s[..]) == Some(INDEX_TEMPLATE) {
            0
        } else {
            1
        };
        out.write(&format!(
            "{}{}.html",
            current_module
                .split('.')
                .skip(skipped)
                .map(|_| "../")
                .format(""),
            param.replace(".", "/")
        ))?;
        Ok(())
    }
    reg.register_helper("symbol_link", Box::new(symbol_link));

    fn breadcrumbs(
        h: &Helper,
        _: &Handlebars,
        _: &mut RenderContext,
        out: &mut Output,
    ) -> ::std::result::Result<(), RenderError> {
        let param = String::deserialize(h.param(0).unwrap().value())?;
        let parts: Vec<_> = param.split(".").collect();
        for (i, part) in parts.iter().enumerate() {
            out.write(&format!(
                r##"<li class="breadcrumb-item{}">{}</li>"##,
                if i + 1 == parts.len() { " active" } else { "" },
                if i + 1 == parts.len() {
                    handlebars::html_escape(&part)
                } else {
                    let path = (0..(parts.len() - i - 2)).map(|_| "../").format("");
                    format!(
                        r##"<a href="{}index.html">{}</a>"##,
                        path,
                        handlebars::html_escape(&part)
                    )
                },
            ))?;
        }
        Ok(())
    }
    reg.register_helper("breadcrumbs", Box::new(breadcrumbs));

    fn style(
        _: &Helper,
        _: &Handlebars,
        rc: &mut RenderContext,
        out: &mut Output,
    ) -> ::std::result::Result<(), RenderError> {
        let current_module = &rc.context().data()["name"]
            .as_str()
            .expect("name")
            .to_string();
        let relative_path = current_module.split('.').map(|_| "../").format("");

        out.write(&format!(r#"
<link rel="stylesheet" href="https://maxcdn.bootstrapcdn.com/bootstrap/4.0.0/css/bootstrap.min.css" integrity="sha384-Gn5384xqQ1aoWXA+058RXPxPg6fy4IWvTNh0E263XmFcJlSAwiGgFAW/dAiS6JXm" crossorigin="anonymous">
<link rel="stylesheet" href="{}style.css">
               "#, relative_path))?;
        Ok(())
    }
    reg.register_helper("style", Box::new(style));

    fn markdown(
        h: &Helper,
        _: &Handlebars,
        _: &mut RenderContext,
        out: &mut Output,
    ) -> ::std::result::Result<(), RenderError> {
        let param = String::deserialize(h.param(0).unwrap().value())?;

        let parser = pulldown_cmark::Parser::new(&param);
        let mut buf = String::new();
        pulldown_cmark::html::push_html(&mut buf, parser);

        // HACK
        // This markdown is embedded so shrink the headings found in the markdown
        lazy_static! {
            static ref REGEX: regex::Regex = regex::Regex::new(r#"<(/?)h(\d)>"#).unwrap();
        }
        let buf = REGEX.replace_all(&buf, |captures: &regex::Captures| {
            format!(
                "<{}h{}>",
                &captures[1],
                captures[2].parse::<i32>().expect("Digit from regex") + 4
            )
        });

        out.write(&buf)?;

        Ok(())
    }
    reg.register_helper("markdown", Box::new(markdown));

    fn markdown_first_paragraph(
        h: &Helper,
        _: &Handlebars,
        _: &mut RenderContext,
        out: &mut Output,
    ) -> ::std::result::Result<(), RenderError> {
        let param = String::deserialize(h.param(0).unwrap().value())?;

        let first_paragraph: String = param.lines().take_while(|s| !s.is_empty()).collect();

        let parser = pulldown_cmark::Parser::new(&first_paragraph);
        let mut buf = String::new();
        pulldown_cmark::html::push_html(&mut buf, parser);
        let buf = buf
            .trim()
            .trim_left_matches("<p>")
            .trim_right_matches("</p>");
        out.write(buf)?;

        Ok(())
    }
    reg.register_helper(
        "markdown_first_paragraph",
        Box::new(markdown_first_paragraph),
    );

    Ok(reg)
}

fn generate_module<W>(reg: &Handlebars, out: &mut W, module: &TemplateModule) -> Result<()>
where
    W: io::Write,
{
    trace!("DOC: {:?}", module);

    reg.render_to_write(MODULE_TEMPLATE, &module, out)
        .with_context(|err| format!("Unable to render {}: {}", module.name, err))?;
    Ok(())
}

pub fn generate_for_path<P, Q>(thread: &Thread, path: &P, out_path: &Q) -> Result<()>
where
    P: ?Sized + AsRef<Path>,
    Q: ?Sized + AsRef<Path>,
{
    generate_for_path_(thread, path.as_ref(), out_path.as_ref())
}

pub fn generate_for_path_(thread: &Thread, path: &Path, out_path: &Path) -> Result<()> {
    let mut directories = Vec::new();
    for entry in walkdir::WalkDir::new(path) {
        let entry = entry?;
        if !entry.file_type().is_file()
            || entry.path().extension().and_then(|ext| ext.to_str()) != Some("glu")
        {
            if entry.file_type().is_dir() {
                directories.push((entry.path().to_owned(), Vec::new()));
            }
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

        let name = filename_to_module(
            entry
                .path()
                .to_str()
                .ok_or_else(|| failure::err_msg("Non-UTF-8 filename"))?,
        );

        let (expr, typ) = Compiler::new().typecheck_str(thread, &name, &content, None)?;
        let (meta, _) = metadata(&*thread.get_env(), &expr);

        create_dir_all(out_path.join(entry.path().parent().unwrap_or(Path::new(""))))?;

        let comment = content
            .lines()
            .map(|s| s.trim())
            .skip_while(|s| s.is_empty() || s.starts_with("//@"))
            .take_while(|s| s.starts_with("//!"))
            .map(|s| &s["//!".len()..])
            .format("\n")
            .to_string();

        let module = Module {
            name,
            comment,
            record: record(&typ, &meta),
        };

        directories
            .last_mut()
            .expect("Directory before this file")
            .1
            .push(module);
    }

    #[derive(Serialize)]
    struct Index<'a> {
        name: String,
        modules: &'a [Module],
    }

    let reg = handlebars()?;

    for (path, modules) in directories {
        for module in &modules {
            let out_path =
                out_path.join(PathBuf::from(module.name.replace(".", "/")).with_extension("html"));
            let mut doc_file = File::create(&*out_path).with_context(|err| {
                format!(
                    "Unable to open output file `{}`: {}",
                    out_path.display(),
                    err
                )
            })?;

            generate_module(
                &reg,
                &mut doc_file,
                &TemplateModule {
                    name: &module.name,
                    comment: &module.comment,
                    record: &module.record,
                    sibling_modules: modules.iter().map(|sibling| &*sibling.name).collect(),
                },
            )?;
        }

        let index_path = out_path.join(&*path).join("index.html");
        trace!("Rendering index: {}", index_path.display());
        let mut doc_file = File::create(&*index_path).with_context(|err| {
            format!(
                "Unable to open output file `{}`: {}",
                index_path.display(),
                err
            )
        })?;

        let name = filename_to_module(
            path.to_str()
                .ok_or_else(|| failure::err_msg("Non-UTF-8 filename"))?,
        );

        reg.render_to_write(
            INDEX_TEMPLATE,
            &Index {
                name,
                modules: &modules,
            },
            &mut doc_file,
        ).with_context(|err| {
            format!("Unable to render index {}: {}", index_path.display(), err)
        })?;
    }

    let mut style_sheet = File::create(out_path.join("style.css"))?;
    style_sheet.write_all(include_bytes!("doc/style.css"))?;

    Ok(())
}

const LONG_VERSION: &str = concat!(crate_version!(), "\n", "commit: ", env!("GIT_HASH"));
#[derive(StructOpt)]
#[structopt(about = "Documents gluon source code", raw(long_version = "LONG_VERSION"))]
pub struct Opt {
    #[structopt(help = "Documents the file or directory")]
    pub input: String,
    #[structopt(help = "Outputs the documentation to this directory")]
    pub output: String,
}
