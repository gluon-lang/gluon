//! Implementation of the `import!` macro.

use std::{
    any::Any,
    borrow::Cow,
    collections::hash_map::Entry,
    fs::File,
    io,
    io::Read,
    mem,
    path::PathBuf,
    pin::Pin,
    sync::{Arc, Mutex, RwLock},
};

use futures::{channel::oneshot, future, prelude::*};

use itertools::Itertools;

use either::Either;

use crate::base::{
    ast::{expr_to_path, Expr, Literal, SpannedExpr, Typed, TypedIdent},
    error::{Errors, InFile},
    filename_to_module,
    fnv::FnvMap,
    pos::{self, BytePos, Span},
    symbol::Symbol,
    types::ArcType,
};

use crate::vm::{
    self,
    macros::{Error as MacroError, Macro, MacroExpander, MacroFuture, MacroState},
    thread::{Thread, ThreadInternal},
    ExternLoader, ExternModule,
};

use crate::{box_future, compiler_pipeline::*, Compiler};

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

pub const COMPILER_KEY: &str = "Compiler";

include!(concat!(env!("OUT_DIR"), "/std_modules.rs"));

pub trait Importer: Any + Clone + Sync + Send {
    fn import<'a>(
        &self,
        compiler: &'a mut Compiler,
        vm: &'a Thread,
        earlier_errors_exist: bool,
        modulename: &'a str,
        input: &'a str,
        expr: SpannedExpr<Symbol>,
    ) -> BoxFuture<'a, (), (Option<ArcType>, MacroError)>;
}

#[derive(Clone)]
pub struct DefaultImporter;
impl Importer for DefaultImporter {
    fn import<'a>(
        &self,
        compiler: &'a mut Compiler,
        vm: &'a Thread,
        earlier_errors_exist: bool,
        modulename: &'a str,
        input: &'a str,
        mut expr: SpannedExpr<Symbol>,
    ) -> BoxFuture<'a, (), (Option<ArcType>, MacroError)> {
        (async move {
            let result = {
                let expr = &mut expr;
                let result = await!(MacroValue { expr }.typecheck(compiler, vm, modulename, input));

                if result.is_ok() && earlier_errors_exist {
                    // We must not pass error patterns or expressions to the core translator so break
                    // early. An error will be returned by the macro expander so we can just return Ok
                    return Ok(());
                }

                await!(future::ready(result).and_then(|value| value.load_script(
                    compiler,
                    vm,
                    modulename,
                    input,
                    ()
                )))
            };

            result.map_err(|err| (Some(expr.env_type_of(&*vm.get_env())), err.into()))
        })
            .boxed()
    }
}

enum UnloadedModule {
    Source(Cow<'static, str>),
    Extern(Vec<String>),
}

/// Macro which rewrites occurances of `import! "filename"` to a load of that file if it is not
/// already loaded and then a global access to the loaded module
pub struct Import<I = DefaultImporter> {
    pub paths: RwLock<Vec<PathBuf>>,
    pub loaders: RwLock<FnvMap<String, (Vec<String>, ExternLoader)>>,
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

    pub fn add_loader(&self, module: &str, dependencies: Vec<String>, loader: ExternLoader) {
        self.loaders
            .write()
            .unwrap()
            .insert(String::from(module), (dependencies, loader));
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
        _vm: &Thread,
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
                    let mut loaders = self.loaders.write().unwrap();
                    if let Some((dependencies, _loader)) = loaders.get_mut(module) {
                        return Ok(UnloadedModule::Extern(dependencies.clone()));
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

    // Breaks the self-recursion in load_module
    fn load_module_boxed<'a>(
        &'a self,
        compiler: &'a mut Compiler,
        vm: &'a Thread,
        macros: &'a mut MacroExpander,
        module_id: &'a Symbol,
        span: Span<BytePos>,
    ) -> Pin<Box<Future<Output = Result<(), (Option<ArcType>, MacroError)>> + Send + 'a>>
    where
        I: Importer,
    {
        box_future(self.load_module(compiler, vm, macros, module_id, span))
    }

    pub async fn load_module<'a>(
        &'a self,
        compiler: &'a mut Compiler,
        vm: &'a Thread,
        macros: &'a mut MacroExpander,
        module_id: &'a Symbol,
        span: Span<BytePos>,
    ) -> Result<(), (Option<ArcType>, MacroError)>
    where
        I: Importer,
    {
        trace!("Loading {}", module_id);

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
            let either = {
                let mut loading = self.loading.lock().unwrap();
                match loading.entry(module_id.to_string()) {
                    Entry::Occupied(entry) => {
                        trace!("Waiting on {}", module_id);
                        get_state(macros).visited.pop();
                        Either::Left(entry.get().clone())
                    }
                    Entry::Vacant(entry) => {
                        let (sender, receiver) = oneshot::channel();
                        entry.insert(receiver.shared());
                        Either::Right(sender)
                    }
                }
            };
            match either {
                Either::Left(recv) => return Ok(await!(recv.map(|_| ()))),
                Either::Right(s) => s,
            }
        };
        if vm.global_env().global_exists(module_id.definition_name()) {
            let _ = sender.send(());
            get_state(macros).visited.pop();
            return Ok(());
        }

        let result = await!(self.load_module_(compiler, vm, macros, module_id, &filename, span));

        if let Err((ref typ, ref err)) = result {
            debug!("Import error {}: {}", module_id, err);
            if let Some(typ) = typ {
                debug!("Import got type {}", typ);
            }
        }

        let _ = sender.send(());

        get_state(macros).visited.pop();
        self.loading.lock().unwrap().remove(module_id.as_ref());

        trace!("Loaded {}", module_id);

        result
    }

    async fn load_module_<'a>(
        &'a self,
        compiler: &'a mut Compiler,
        vm: &'a Thread,
        macros: &'a mut MacroExpander,
        module_id: &'a Symbol,
        filename: &'a str,
        span: Span<BytePos>,
    ) -> Result<(), (Option<ArcType>, MacroError)>
    where
        I: Importer,
    {
        let modulename = module_id.name().definition_name();
        // Retrieve the source, first looking in the standard library included in the
        // binary
        let unloaded_module = self
            .get_unloaded_module(vm, &modulename, &filename)
            .map_err(|err| (None, err.into()))?;

        match unloaded_module {
            UnloadedModule::Extern(dependencies) => {
                for dep in dependencies {
                    let dep = Symbol::from(format!("@{}", dep));
                    await!(self.load_module_boxed(compiler, vm, macros, &dep, Span::default()))?;
                }

                let ExternModule {
                    value,
                    typ,
                    metadata,
                } = {
                    let mut loaders = self.loaders.write().unwrap();
                    let (_, loader) = loaders.get_mut(modulename).unwrap();
                    loader(vm).map_err(|err| (None, err.into()))?
                };

                vm.set_global(module_id.clone(), typ, metadata, value.get_value())
                    .map_err(|err| (None, err.into()))?;
            }
            UnloadedModule::Source(file_contents) => {
                // Modules marked as this would create a cyclic dependency if they included the implicit
                // prelude
                let implicit_prelude = !file_contents.starts_with("//@NO-IMPLICIT-PRELUDE");
                compiler.set_implicit_prelude(implicit_prelude);

                let prev_errors = mem::replace(&mut macros.errors, Errors::new());

                let result = await!(file_contents.expand_macro_with(
                    compiler,
                    macros,
                    &modulename,
                    &file_contents
                ));

                let has_errors =
                    macros.errors.has_errors() || result.is_err() || macros.error_in_expr;
                let errors = mem::replace(&mut macros.errors, prev_errors);
                if errors.has_errors() {
                    macros.errors.push(pos::spanned(
                        span,
                        Box::new(crate::Error::Macro(InFile::new(
                            compiler.code_map().clone(),
                            errors,
                        ))),
                    ));
                }

                let macro_result = match result {
                    Ok(m) => m,
                    Err((None, err)) => {
                        return Err((None, err.into()));
                    }
                    Err((Some(m), err)) => {
                        macros.errors.push(pos::spanned(span, err.into()));
                        m
                    }
                };

                await!(self.importer.import(
                    compiler,
                    vm,
                    has_errors,
                    &modulename,
                    &file_contents,
                    macro_result.expr,
                ))?;
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
///             yell => primitive!(1, yell)
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
pub fn add_extern_module<F>(thread: &Thread, name: &str, loader: F)
where
    F: FnMut(&Thread) -> vm::Result<ExternModule> + Send + Sync + 'static,
{
    add_extern_module_with_deps(thread, name, vec![], loader)
}

pub(crate) fn add_extern_module_with_deps<F>(
    thread: &Thread,
    name: &str,
    dependencies: Vec<String>,
    loader: F,
) where
    F: FnMut(&Thread) -> vm::Result<ExternModule> + Send + Sync + 'static,
{
    add_extern_module_(thread, name, dependencies, Box::new(loader))
}

fn add_extern_module_(
    thread: &Thread,
    name: &str,
    dependencies: Vec<String>,
    loader: ExternLoader,
) {
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
    import.add_loader(name, dependencies, loader);
}

macro_rules! add_extern_module_if {
    (
        #[cfg($($features: tt)*)],
        available_if = $msg: expr,
        args($vm: expr, $mod_name: expr, $loader: path)
    ) => {
        add_extern_module_if!(
            #[cfg($($features)*)],
            available_if = $msg,
            args($vm, $mod_name, vec![], $loader)
        )
    };
    (
        #[cfg($($features: tt)*)],
        available_if = $msg: expr,
        args($vm: expr, $mod_name: expr, $deps: expr, $loader: path)
    ) => {{
        #[cfg($($features)*)]
        $crate::import::add_extern_module_with_deps($vm, $mod_name, $deps, $loader);

        #[cfg(not($($features)*))]
        $crate::import::add_extern_module($vm, $mod_name, |_: &::vm::thread::Thread| -> ::vm::Result<::vm::ExternModule> {
            Err(::vm::Error::Message(
                format!(
                    "{} is only available if {}",
                    $mod_name,
                    $msg
                )
            ))
        });
    }};
}

fn get_state<'m>(macros: &'m mut MacroExpander) -> &'m mut State {
    macros
        .state
        .entry(String::from("import"))
        .or_insert_with(|| {
            Box::new(State {
                visited: Vec::new(),
                modules_with_errors: Default::default(),
            })
        })
        .downcast_mut::<State>()
        .unwrap()
}

struct State {
    visited: Vec<String>,
    modules_with_errors: Arc<RwLock<FnvMap<String, Expr<Symbol>>>>,
}

impl MacroState for State {
    fn clone_state(&self) -> Box<MacroState> {
        Box::new(State {
            visited: self.visited.clone(),
            modules_with_errors: self.modules_with_errors.clone(),
        })
    }
}

impl<I> Macro for Import<I>
where
    I: Importer,
{
    fn expand<'f>(
        &'f self,
        macros: &'f mut MacroExpander,
        args: Vec<SpannedExpr<Symbol>>,
    ) -> MacroFuture<'f> {
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
                    return Err(Error::String(
                        "Expected a string literal or path to import".into(),
                    )
                    .into());
                }
            };
            Ok(modulename)
        }

        (async move {
            let modulename = match get_module_name(&args) {
                Ok(modulename) => modulename,
                Err(err) => return Err(err),
            };

            let vm = macros.vm.clone();
            // Prefix globals with @ so they don't shadow any local variables
            let name = Symbol::from(if modulename.starts_with('@') {
                modulename.clone()
            } else {
                format!("@{}", modulename)
            });

            // Only load the script if it is not already loaded
            if !vm.global_env().global_exists(&modulename) {
                let opt = get_state(macros)
                    .modules_with_errors.read().unwrap()
                    .get(&modulename)
                    .cloned();
                if let Some(expr) = opt
                {
                    macros.error_in_expr = true;
                    return Ok(pos::spanned(args[0].span, expr));
                }

                // TODO Inherit settings from the parent compiler instead of forcing full_metadata here
                // (which is necessary for the doc generator)
                let mut temp_compiler = Compiler::new().full_metadata(true).task_spawner_raw(macros.task_spawner.clone());
                match await!(self.load_module(&mut temp_compiler, &vm, macros, &name, args[0].span,))
                {
                    Ok(()) => (),
                    Err((typ, err)) => {
                        macros.errors.push(pos::spanned(args[0].span, err));

                        let expr = Expr::Error(typ);
                        get_state(macros)
                            .modules_with_errors.write().unwrap()
                            .insert(modulename, expr.clone());

                        return Ok(pos::spanned(args[0].span, expr));
                    }
                }
            }
            Ok(pos::spanned(
                args[0].span,
                Expr::Ident(TypedIdent::new(name)),
            ))
        })
            .boxed()
    }
}
