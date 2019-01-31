#[macro_use]
extern crate clap;
extern crate failure;
extern crate handlebars;
extern crate itertools;
extern crate rayon;
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

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, create_dir_all, File},
    io::{self, Read},
    path::{Path, PathBuf},
    result::Result as StdResult,
};

use failure::ResultExt;

use itertools::Itertools;

use handlebars::{Context, Handlebars, Helper, Output, RenderContext, RenderError};

use rayon::prelude::*;

use serde::Deserialize;

use pretty::{Arena, DocAllocator};

use gluon::{
    base::{
        filename_to_module,
        metadata::Metadata,
        symbol::{Name, Symbol},
        types::{ArcType, ArgType, Type, TypeExt},
    },
    check::metadata::metadata,
    Compiler, Thread,
};

pub type Error = failure::Error;
pub type Result<T> = ::std::result::Result<T, Error>;

#[derive(Serialize, PartialEq, Debug, Default)]
pub struct Module {
    pub name: String,
    pub comment: String,
    pub record: Record,
}

#[derive(Serialize, PartialEq, Debug, Default)]
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

struct SymbolLinkRenderer {
    escaped: String,
    un_escaped: String,
}

impl SymbolLinkRenderer {
    fn flush_to_escaped(&mut self) {
        self.escaped
            .push_str(&handlebars::html_escape(&self.un_escaped));
        self.un_escaped.clear();
    }
    fn finish(mut self) -> String {
        self.escaped
            .push_str(&handlebars::html_escape(&self.un_escaped));
        self.escaped
    }
}

impl pretty::Render for SymbolLinkRenderer {
    type Error = ();
    fn write_str(&mut self, s: &str) -> StdResult<usize, Self::Error> {
        self.un_escaped.push_str(s);
        Ok(s.len())
    }
}

impl pretty::RenderAnnotated<String> for SymbolLinkRenderer {
    fn push_annotation(&mut self, annotation: &String) -> StdResult<(), Self::Error> {
        self.flush_to_escaped();
        self.escaped
            .push_str(&format!(r#"<a href="{}">"#, annotation));
        Ok(())
    }
    fn pop_annotation(&mut self) -> StdResult<(), Self::Error> {
        self.flush_to_escaped();
        self.escaped.push_str("</a>");
        Ok(())
    }
}

fn print_type(current_module: &str, typ: &ArcType) -> String {
    let annotate_symbol =
        |symbol: &Symbol| Some(symbol_link(false, current_module, symbol.as_ref()));
    let arena = Arena::new();
    let mut doc = typ
        .display(80)
        .annotate_symbol(&annotate_symbol)
        .pretty(&arena);
    match **typ {
        Type::Record(_) => (),
        Type::Variant(_) => doc = arena.newline().append(doc).nest(4),
        _ => {
            doc = doc.nest(4);
        }
    }

    let mut renderer = SymbolLinkRenderer {
        un_escaped: String::new(),
        escaped: String::new(),
    };
    doc.group().1.render_raw(80, &mut renderer).unwrap();
    renderer.finish()
}

fn hidden(meta: &Metadata, field: &str) -> bool {
    meta.module.get(field).map_or(false, |meta| {
        meta.attributes().any(|attr| {
            attr.name == "doc" && attr.arguments.as_ref().map_or(false, |arg| arg == "hidden")
        })
    })
}

pub fn record(current_module: &str, typ: &ArcType, meta: &Metadata) -> Record {
    Record {
        types: typ
            .type_field_iter()
            .filter(|field| !hidden(meta, field.name.as_ref()))
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
                typ: print_type(current_module, &field.typ.unresolved_type().remove_forall()),
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
            .filter(|field| !hidden(meta, field.name.as_ref()))
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
                    typ: print_type(current_module, &field.typ),

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
    pub sub_modules: Vec<&'a Module>,
    pub sibling_modules: Vec<&'a str>,
}

const MODULE_TEMPLATE: &str = "module";

fn symbol_link(index: bool, current_module: &str, param: &str) -> String {
    let skipped = if index { 0 } else { 1 };

    let parts: Vec<_> = param.split('.').collect();
    let (typ, module_parts) = parts.split_last().unwrap();

    format!(
        "{}{}.html#type.{}",
        current_module
            .split('.')
            .skip(skipped)
            .map(|_| "../")
            .format(""),
        module_parts.iter().format("/"),
        typ
    )
}

fn module_link(current_module: &str, param: &str) -> String {
    format!(
        "{}{}.html",
        current_module.split('.').skip(1).map(|_| "../").format(""),
        param.replace(".", "/"),
    )
}

fn handlebars() -> Result<Handlebars> {
    let mut reg = Handlebars::new();

    reg.register_template_string(MODULE_TEMPLATE, include_str!("doc/module.html"))?;

    fn module_link_helper(
        h: &Helper,
        _: &Handlebars,
        context: &Context,
        _rc: &mut RenderContext,
        out: &mut Output,
    ) -> ::std::result::Result<(), RenderError> {
        let current_module = &context.data()["name"].as_str().expect("name").to_string();

        let param = String::deserialize(h.param(0).unwrap().value())?;
        out.write(&module_link(current_module, &param))?;
        Ok(())
    }
    reg.register_helper("module_link", Box::new(module_link_helper));

    fn breadcrumbs(
        h: &Helper,
        _: &Handlebars,
        context: &Context,
        _rc: &mut RenderContext,
        out: &mut Output,
    ) -> ::std::result::Result<(), RenderError> {
        let current_module = context.data()["name"].as_str().expect("name");
        let current_module_level = current_module.split('.').count();

        let param = String::deserialize(h.param(0).unwrap().value())?;
        let parts: Vec<_> = param.split(".").collect();
        for (i, part) in parts.iter().enumerate() {
            out.write(&format!(
                r##"<li class="breadcrumb-item{}">{}</li>"##,
                if i + 1 == parts.len() { " active" } else { "" },
                if i + 1 == parts.len() {
                    handlebars::html_escape(&part)
                } else {
                    let path = (0..(current_module_level - i - 1))
                        .map(|_| "../")
                        .format("");
                    format!(
                        r##"<a href="{}{}.html">{}</a>"##,
                        path,
                        current_module.split('.').rev().nth(1).unwrap_or(""),
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
        context: &Context,
        _: &mut RenderContext,
        out: &mut Output,
    ) -> ::std::result::Result<(), RenderError> {
        let current_module = &context.data()["name"].as_str().expect("name").to_string();
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
        _: &Context,
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
        _: &Context,
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
            .trim_start_matches("<p>")
            .trim_end_matches("</p>");
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
    let mut directories = BTreeMap::<_, BTreeMap<_, Module>>::new();
    let mut modules = BTreeSet::new();
    let mut content = String::new();

    for entry in walkdir::WalkDir::new(path) {
        let entry = entry?;
        if !entry.file_type().is_file()
            || entry.path().extension().and_then(|ext| ext.to_str()) != Some("glu")
        {
            continue;
        }
        debug!("Indexing module: {}", entry.path().display());

        let mut input = File::open(&*entry.path()).with_context(|err| {
            format!(
                "Unable to open gluon file `{}`: {}",
                entry.path().display(),
                err
            )
        })?;
        content.clear();
        input.read_to_string(&mut content)?;

        let name = filename_to_module(
            entry
                .path()
                .to_str()
                .ok_or_else(|| failure::err_msg("Non-UTF-8 filename"))?,
        );

        let (expr, typ) = Compiler::new()
            .full_metadata(true)
            .typecheck_str(thread, &name, &content, None)?;
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
            record: record(&name, &typ, &meta),
            name,
            comment,
        };

        modules.insert(module.name.clone());
        let name = Name::new(&module.name);
        directories
            .entry(name.module().as_str().to_owned())
            .or_default()
            .insert(name.name().as_str().to_owned(), module);
    }

    let directory_modules = directories.keys().cloned().collect::<BTreeSet<_>>();
    for module_name in directory_modules {
        let name = Name::new(&module_name);
        directories
            .entry(name.module().as_str().to_owned())
            .or_default()
            .entry(name.name().as_str().to_owned())
            .or_insert_with(|| {
                trace!("Adding implicit module {}", module_name);

                Module {
                    name: module_name.into(),
                    comment: "".into(),
                    record: Record::default(),
                }
            });
    }

    let reg = handlebars()?;

    directories
        .values()
        .flat_map(|modules| modules.values().map(move |m| (modules, m)))
        .par_bridge()
        .try_for_each(|(modules, module)| -> Result<()> {
            let module_path = PathBuf::from(module.name.replace(".", "/"));
            let out_path = out_path.join(&module_path).with_extension("html");
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
                    sub_modules: directories
                        .get(&module.name)
                        .iter()
                        .flat_map(|sub_modules| sub_modules.values())
                        .collect(),
                    sibling_modules: modules.keys().map(|s| s as &str).collect(),
                },
            )?;

            debug!("Documented {}", module.name);

            Ok(())
        })?;

    fs::write(
        out_path.join("style.css"),
        &include_bytes!("doc/style.css")[..],
    )?;

    Ok(())
}

const LONG_VERSION: &str = concat!(crate_version!(), "\n", "commit: ", env!("GIT_HASH"));
#[derive(StructOpt)]
#[structopt(
    about = "Documents gluon source code",
    raw(long_version = "LONG_VERSION")
)]
pub struct Opt {
    #[structopt(long = "open")]
    #[structopt(help = "Opens the documentation after it has been generated")]
    pub open: bool,
    #[structopt(long = "jobs")]
    #[structopt(help = "How many threads to run in parallel")]
    pub jobs: Option<usize>,
    #[structopt(help = "Documents the file or directory")]
    pub input: String,
    #[structopt(help = "Outputs the documentation to this directory")]
    pub output: String,
}
