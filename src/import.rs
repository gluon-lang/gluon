//! Implementation of the `import!` macro.

use std::any::Any;
use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::sync::{Mutex, RwLock};
use std::fs::File;
use std::mem;
use std::io;
use std::io::Read;
use std::path::PathBuf;

use futures::sync::oneshot;
use futures::{future, Future};

use itertools::Itertools;

use base::filename_to_module;
use base::error::{Errors, InFile};
use base::ast::{expr_to_path, Expr, Literal, SpannedExpr, Typed, TypedIdent};
use base::fnv::FnvMap;
use base::pos::{self, BytePos, Span};
use base::symbol::Symbol;
use base::types::ArcType;

use vm::{ExternLoader, ExternModule};
use vm::macros::{Error as MacroError, Macro, MacroExpander, MacroFuture};
use vm::thread::{Thread, ThreadInternal};

use super::Compiler;

quick_error! {
    /// Error type for the import macro
    #[derive(Debug)]
    pub enum Error {
        /// The importer found a cyclic dependency when loading files
        CyclicDependency(module: String, cycle: Vec<String>) {
            description("Cyclic dependency")
            display(
                "Module '{}' occurs in a cyclic dependency: `{}`",
                module,
                cycle.iter().chain(Some(module)).format(" -> ")
            )
        }
        /// Generic message error
        String(message: String) {
            description(message)
            display("{}", message)
        }
        /// The importer could not load the imported file
        IO(err: io::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
    }
}

macro_rules! std_libs {
    ($($file: expr,)*) => {
        [$((concat!("std.", $file), include_str!(concat!("../std/", $file, ".glu")))),*]
    }
}
// Include the standard library distribution in the binary
#[cfg(not(feature = "test"))]
static STD_LIBS: &[(&str, &str)] = &std_libs!(
    "prelude",
    "types",
    "function",
    "bool",
    "float",
    "int",
    "byte",
    "char",
    "io",
    "list",
    "map",
    "option",
    "parser",
    "result",
    "state",
    "stream",
    "string",
    "thread",
    "test",
    "unit",
    "writer",
    "array",
    "functor",
    "applicative",
    "cmp",
    "foldable",
    "monad",
    "monoid",
    "semigroup",
);

// When testing we use the files as-is in the repository to avoid recompiling after they are
// changed
#[cfg(feature = "test")]
static STD_LIBS: &[(&str, &str)] = &std_libs!();

pub trait Importer: Any + Clone + Sync + Send {
    fn import(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        earlier_errors_exist: bool,
        modulename: &str,
        input: &str,
        expr: SpannedExpr<Symbol>,
    ) -> Result<(), (Option<ArcType>, MacroError)>;
}

#[derive(Clone)]
pub struct DefaultImporter;
impl Importer for DefaultImporter {
    fn import(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        earlier_errors_exist: bool,
        modulename: &str,
        input: &str,
        mut expr: SpannedExpr<Symbol>,
    ) -> Result<(), (Option<ArcType>, MacroError)> {
        use compiler_pipeline::*;

        let result = {
            let expr = &mut expr;
            let result = MacroValue { expr }
                .typecheck(compiler, vm, modulename, input)
                .map_err(|err| err.into());

            if result.is_ok() && earlier_errors_exist {
                // We must not pass error patterns or expressions to the core translator so break
                // early. An error will be returned by the macro expander so we can just return Ok
                return Ok(());
            }

            result.and_then(|value| {
                value
                    .load_script(compiler, vm, modulename, input, ())
                    .sync_or_error()
            })
        };

        result.map_err(|err| (Some(expr.env_type_of(&*vm.get_env())), err.into()))
    }
}

enum UnloadedModule {
    Source(Cow<'static, str>),
    Extern(ExternModule),
}

/// Macro which rewrites occurances of `import! "filename"` to a load of that file if it is not
/// already loaded and then a global access to the loaded module
pub struct Import<I = DefaultImporter> {
    pub paths: RwLock<Vec<PathBuf>>,
    pub loaders: RwLock<FnvMap<String, ExternLoader>>,
    pub importer: I,

    /// Map of modules currently being loaded
    loading: Mutex<FnvMap<String, future::Shared<oneshot::Receiver<()>>>>,
}

impl<I> Import<I> {
    /// Creates a new import macro
    pub fn new(importer: I) -> Import<I> {
        Import {
            paths: RwLock::new(vec![PathBuf::from(".")]),
            loaders: RwLock::default(),
            importer: importer,
            loading: Mutex::default(),
        }
    }

    /// Adds a path to the list of paths which the importer uses to find files
    pub fn add_path<P: Into<PathBuf>>(&self, path: P) {
        self.paths.write().unwrap().push(path.into());
    }

    pub fn set_paths(&self, paths: Vec<PathBuf>) {
        *self.paths.write().unwrap() = paths;
    }

    pub fn add_loader(&self, module: &str, loader: ExternLoader) {
        self.loaders
            .write()
            .unwrap()
            .insert(String::from(module), loader);
    }

    pub fn modules(&self) -> Vec<Cow<'static, str>> {
        STD_LIBS
            .iter()
            .map(|t| Cow::Borrowed(t.0))
            .chain(self.loaders.read().unwrap().keys().cloned().map(Cow::Owned))
            .collect()
    }

    fn get_unloaded_module(
        &self,
        vm: &Thread,
        module: &str,
        filename: &str,
    ) -> Result<UnloadedModule, MacroError> {
        let mut buffer = String::new();

        // Retrieve the source, first looking in the standard library included in the
        // binary

        let std_file = STD_LIBS.iter().find(|tup| tup.0 == module);
        if let Some(tup) = std_file {
            return Ok(UnloadedModule::Source(Cow::Borrowed(tup.1)));
        }
        Ok(match std_file {
            Some(tup) => UnloadedModule::Source(Cow::Borrowed(tup.1)),
            None => {
                {
                    let loaders = self.loaders.read().unwrap();
                    if let Some(loader) = loaders.get(module) {
                        let value = loader(vm)?;
                        return Ok(UnloadedModule::Extern(value));
                    }
                }
                let paths = self.paths.read().unwrap();
                let file = paths
                    .iter()
                    .filter_map(|p| {
                        let base = p.join(filename);
                        match File::open(&base) {
                            Ok(file) => Some(file),
                            Err(_) => None,
                        }
                    })
                    .next();
                let mut file = file.ok_or_else(|| {
                    Error::String(format!(
                        "Could not find module '{}'. Searched {}.",
                        module,
                        paths
                            .iter()
                            .map(|p| format!("`{}`", p.display()))
                            .format(", ")
                    ))
                })?;
                file.read_to_string(&mut buffer)?;
                UnloadedModule::Source(Cow::Owned(buffer))
            }
        })
    }

    pub fn load_module(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        macros: &mut MacroExpander,
        module_id: &Symbol,
        span: Span<BytePos>,
    ) -> Result<Option<Box<Future<Item = (), Error = ()> + Send>>, (Option<ArcType>, MacroError)>
    where
        I: Importer,
    {
        assert!(module_id.is_global());
        let modulename = module_id.name().definition_name();
        let mut filename = modulename.replace(".", "/");
        filename.push_str(".glu");
        {
            let state = get_state(macros);
            if state.visited.iter().any(|m| **m == *filename) {
                let cycle = state
                    .visited
                    .iter()
                    .skip_while(|m| **m != *filename)
                    .cloned()
                    .collect();
                return Err((
                    None,
                    Error::CyclicDependency(filename.clone(), cycle).into(),
                ));
            }
            state.visited.push(filename.clone());
        }

        // Prevent any other threads from importing this module while we compile it
        let sender = {
            let mut loading = self.loading.lock().unwrap();
            match loading.entry(module_id.to_string()) {
                Entry::Occupied(entry) => {
                    get_state(macros).visited.pop();
                    return Ok(Some(Box::new(
                        entry.get().clone().map(|_| ()).map_err(|_| ()),
                    )));
                }
                Entry::Vacant(entry) => {
                    let (sender, receiver) = oneshot::channel();
                    entry.insert(receiver.shared());
                    sender
                }
            }
        };
        if vm.global_env().global_exists(module_id.definition_name()) {
            let _ = sender.send(());
            get_state(macros).visited.pop();
            return Ok(None);
        }

        let result = self.load_module_(compiler, vm, macros, module_id, &filename, span);

        let _ = sender.send(());

        get_state(macros).visited.pop();
        self.loading.lock().unwrap().remove(module_id.as_ref());

        result.map(|_| None)
    }

    fn load_module_(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        macros: &mut MacroExpander,
        module_id: &Symbol,
        filename: &str,
        span: Span<BytePos>,
    ) -> Result<(), (Option<ArcType>, MacroError)>
    where
        I: Importer,
    {
        use compiler_pipeline::*;

        let modulename = module_id.name().definition_name();
        // Retrieve the source, first looking in the standard library included in the
        // binary
        let unloaded_module = self.get_unloaded_module(vm, &modulename, &filename)
            .map_err(|err| (None, err.into()))?;

        match unloaded_module {
            UnloadedModule::Extern(ExternModule {
                value,
                typ,
                metadata,
            }) => {
                vm.set_global(module_id.clone(), typ, metadata, value.get_value())
                    .map_err(|err| (None, err.into()))?;
            }
            UnloadedModule::Source(file_contents) => {
                // Modules marked as this would create a cyclic dependency if they included the implicit
                // prelude
                let implicit_prelude = !file_contents.starts_with("//@NO-IMPLICIT-PRELUDE");
                compiler.set_implicit_prelude(implicit_prelude);

                let mut prev_errors = mem::replace(&mut macros.errors, Errors::new());

                let result =
                    file_contents.expand_macro_with(compiler, macros, &modulename, &file_contents);

                let has_errors =
                    macros.errors.has_errors() || result.is_err() || macros.error_in_expr;
                let errors = mem::replace(&mut macros.errors, prev_errors);
                if errors.has_errors() {
                    macros.errors.push(pos::spanned(
                        span,
                        Box::new(::Error::Macro(InFile::new(
                            &modulename,
                            &file_contents,
                            errors,
                        ))),
                    ));
                }

                let macro_result = match result {
                    Ok(m) => m,
                    Err((None, err)) => return Err((None, err.into())),
                    Err((Some(m), err)) => {
                        macros.errors.push(pos::spanned(span, err.into()));
                        m
                    }
                };

                self.importer.import(
                    compiler,
                    vm,
                    has_errors,
                    &modulename,
                    &file_contents,
                    macro_result.expr,
                )?;
            }
        }
        Ok(())
    }
}

/// Adds an extern module to `thread`, letting it be loaded with `import! name` from gluon code.
///
/// ```
/// extern crate gluon;
/// #[macro_use]
/// extern crate gluon_vm;
///
/// use gluon::vm::{self, ExternModule};
/// use gluon::{Compiler, Thread};
/// use gluon::import::add_extern_module;
///
/// fn yell(s: &str) -> String {
///     s.to_uppercase()
/// }
///
/// fn my_module(thread: &Thread) -> vm::Result<ExternModule> {
///     ExternModule::new(
///         thread,
///         record!{
///             message => "Hello World!",
///             yell => primitive!(1 yell)
///         }
///     )
/// }
///
/// fn main_() -> gluon::Result<()> {
///     let thread = gluon::new_vm();
///     add_extern_module(&thread, "my_module", my_module);
///     let script = r#"
///         let module = import! "my_module"
///         module.yell module.message
///     "#;
///     let (result, _) = Compiler::new().run_expr::<String>(&thread, "example", script)?;
///     assert_eq!(result, "HELLO WORLD!");
///     Ok(())
/// }
/// fn main() {
///     if let Err(err) = main_() {
///         panic!("{}", err)
///     }
/// }
/// ```
pub fn add_extern_module(thread: &Thread, name: &str, loader: ExternLoader) {
    let opt_macro = thread.get_macros().get("import");
    let import = opt_macro
        .as_ref()
        .and_then(|mac| mac.downcast_ref::<Import>())
        .unwrap_or_else(|| {
            ice!(
                "Can't add an extern module with a import macro. \
                 Did you mean to create this `Thread` with `gluon::new_vm`"
            )
        });
    import.add_loader(name, loader);
}

fn get_state<'m>(macros: &'m mut MacroExpander) -> &'m mut State {
    macros
        .state
        .entry(String::from("import"))
        .or_insert_with(|| {
            Box::new(State {
                visited: Vec::new(),
                modules_with_errors: FnvMap::default(),
            })
        })
        .downcast_mut::<State>()
        .unwrap()
}

struct State {
    visited: Vec<String>,
    modules_with_errors: FnvMap<String, Expr<Symbol>>,
}

impl<I> Macro for Import<I>
where
    I: Importer,
{
    fn expand(&self, macros: &mut MacroExpander, args: Vec<SpannedExpr<Symbol>>) -> MacroFuture {
        fn get_module_name(args: &[SpannedExpr<Symbol>]) -> Result<String, MacroError> {
            if args.len() != 1 {
                return Err(Error::String("Expected import to get 1 argument".into()).into());
            }

            let modulename = match args[0].value {
                Expr::Ident(_) | Expr::Projection(..) => {
                    let mut modulename = String::new();
                    expr_to_path(&args[0], &mut modulename)
                        .map_err(|err| Error::String(err.to_string()))?;
                    modulename
                }
                Expr::Literal(Literal::String(ref filename)) => {
                    format!("@{}", filename_to_module(filename))
                }
                _ => {
                    return Err(
                        Error::String("Expected a string literal or path to import".into()).into(),
                    )
                }
            };
            Ok(modulename)
        }

        let modulename = match get_module_name(&args) {
            Ok(modulename) => modulename,
            Err(err) => return Box::new(future::err(err)),
        };

        let vm = macros.vm;
        // Prefix globals with @ so they don't shadow any local variables
        let name = Symbol::from(if modulename.starts_with('@') {
            modulename.clone()
        } else {
            format!("@{}", modulename)
        });

        // Only load the script if it is not already loaded
        debug!("Import '{}' {:?}", modulename, get_state(macros).visited);
        if !vm.global_env().global_exists(&modulename) {
            if let Some(expr) = get_state(macros)
                .modules_with_errors
                .get(&modulename)
                .cloned()
            {
                macros.error_in_expr = true;
                return Box::new(future::ok(pos::spanned(args[0].span, expr)));
            }

            match self.load_module(&mut Compiler::new(), vm, macros, &name, args[0].span) {
                Ok(Some(future)) => {
                    let span = args[0].span;
                    return Box::new(
                        future
                            .map_err(|_| unreachable!())
                            .map(move |_| pos::spanned(span, Expr::Ident(TypedIdent::new(name)))),
                    );
                }
                Ok(None) => (),
                Err((typ, err)) => {
                    macros.errors.push(pos::spanned(args[0].span, err));

                    let expr = Expr::Error(typ);
                    get_state(macros)
                        .modules_with_errors
                        .insert(modulename, expr.clone());

                    return Box::new(future::ok(pos::spanned(args[0].span, expr)));
                }
            }
        }
        Box::new(future::ok(pos::spanned(
            args[0].span,
            Expr::Ident(TypedIdent::new(name)),
        )))
    }
}
