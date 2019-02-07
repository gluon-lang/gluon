//! Implementation of the `import!` macro.

use std::{
    any::Any,
    borrow::Cow,
    fs::File,
    io::Read,
    mem,
    ops::{Deref, DerefMut},
    path::PathBuf,
    sync::{Arc, Mutex, MutexGuard, RwLock},
};

use futures::{future, Future};
use itertools::Itertools;
use salsa::ParallelDatabase;

use crate::base::{
    ast::{expr_to_path, Expr, Literal, SpannedExpr},
    filename_to_module,
    fnv::FnvMap,
    pos,
    symbol::Symbol,
    types::ArcType,
};

use crate::vm::{
    self,
    macros::{Error as MacroError, Macro, MacroExpander, MacroFuture},
    thread::{RootedThread, Thread, ThreadInternal},
    ExternLoader, ExternModule,
};

use crate::{
    compiler_pipeline::*,
    query::{Compilation, CompilationBase, CompilerDatabase},
    IoError, ModuleCompiler,
};

quick_error! {
    /// Error type for the import macro
    #[derive(Debug, Clone, Eq, PartialEq, Hash)]
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
        IO(err: IoError) {
            description(err.description())
            display("{}", err)
            from()
        }
    }
}

impl base::error::AsDiagnostic for Error {
    fn as_diagnostic(&self) -> codespan_reporting::Diagnostic {
        codespan_reporting::Diagnostic::new_error(self.to_string())
    }
}

include!(concat!(env!("OUT_DIR"), "/std_modules.rs"));

pub trait Importer: Any + Clone + Sync + Send {
    fn import(
        &self,
        compiler: &mut ModuleCompiler,
        vm: &Thread,
        modulename: &str,
    ) -> Result<(), (Option<ArcType>, crate::Error)>;
}

#[derive(Clone)]
pub struct DefaultImporter;
impl Importer for DefaultImporter {
    fn import(
        &self,
        compiler: &mut ModuleCompiler,
        vm: &Thread,
        modulename: &str,
    ) -> Result<(), (Option<ArcType>, crate::Error)> {
        let value = compiler
            .database
            .compiled_module(modulename.to_string())
            .map_err(|err| (None, err))?;
        let typ = value.typ.clone();
        Executable::load_script(value, compiler, vm, modulename, "", ())
            .wait()
            .map_err(|err| (Some(typ), err))?;
        Ok(())
    }
}

enum UnloadedModule {
    Source,
    Extern(ExternModule),
}

pub struct DatabaseSnapshot {
    snapshot: Option<salsa::Snapshot<CompilerDatabase>>,
}

impl Drop for DatabaseSnapshot {
    fn drop(&mut self) {
        let import = crate::get_import(self.thread());

        self.snapshot.take();

        let mut compiler = import.compiler.lock().unwrap();
        if Arc::get_mut(&mut compiler.state).is_some() {
            let new_states = compiler.state().module_states.clone();
            compiler.set_module_states(Arc::new(new_states));
        }
    }
}

impl Deref for DatabaseSnapshot {
    type Target = CompilerDatabase;
    fn deref(&self) -> &Self::Target {
        self.snapshot.as_ref().unwrap()
    }
}

pub struct CompilerLock<I = DefaultImporter> {
    // Only needed to ensure that the the `Compiler` the guard points to lives long enough
    _import: Arc<Import<I>>,
    // This isn't actually static but relies on `import` to live longer than the guard
    compiler: Option<MutexGuard<'static, CompilerDatabase>>,
}

impl<I> Drop for CompilerLock<I> {
    fn drop(&mut self) {
        // The compiler moves back to only be owned by the import so we need to remove the thread
        // to break the cycle
        self.thread = None;
        self.compiler.take();
    }
}

impl<I> Deref for CompilerLock<I> {
    type Target = CompilerDatabase;
    fn deref(&self) -> &Self::Target {
        self.compiler.as_ref().unwrap()
    }
}

impl<I> DerefMut for CompilerLock<I> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.compiler.as_mut().unwrap()
    }
}

/// Macro which rewrites occurances of `import! "filename"` to a load of that file if it is not
/// already loaded and then a global access to the loaded module
pub struct Import<I = DefaultImporter> {
    pub paths: RwLock<Vec<PathBuf>>,
    pub loaders: RwLock<FnvMap<String, ExternLoader>>,
    pub importer: I,

    compiler: Mutex<CompilerDatabase>,
}

impl<I> Import<I> {
    /// Creates a new import macro
    pub fn new(importer: I) -> Import<I> {
        Import {
            paths: RwLock::new(vec![PathBuf::from(".")]),
            loaders: RwLock::default(),
            compiler: CompilerDatabase::new_base(None).into(),
            importer: importer,
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

    pub fn compiler_lock(self_: Arc<Self>, thread: RootedThread) -> CompilerLock<I> {
        // Since `self` lives longer than the lifetime in the mutex guard this is safe
        let mut compiler = unsafe {
            CompilerLock {
                compiler: Some(mem::transmute::<
                    MutexGuard<CompilerDatabase>,
                    MutexGuard<CompilerDatabase>,
                >(self_.compiler.lock().unwrap())),
                _import: self_,
            }
        };

        compiler.thread = Some(thread);

        compiler
    }

    pub fn snapshot(&self, thread: RootedThread) -> DatabaseSnapshot {
        let mut compiler = self.compiler.lock().unwrap();

        compiler.thread = Some(thread);
        let snapshot = compiler.snapshot();
        compiler.thread = None;

        DatabaseSnapshot {
            snapshot: Some(snapshot),
        }
    }

    fn get_unloaded_module(&self, vm: &Thread, module: &str) -> Result<UnloadedModule, MacroError> {
        {
            let mut loaders = self.loaders.write().unwrap();
            if let Some(loader) = loaders.get_mut(module) {
                let value = loader(vm).map_err(MacroError::new)?;
                return Ok(UnloadedModule::Extern(value));
            }
        }
        Ok(UnloadedModule::Source)
    }

    pub(crate) fn get_module_source(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        module: &str,
        filename: &str,
    ) -> Result<Cow<'static, str>, Error> {
        let mut buffer = String::new();

        // Retrieve the source, first looking in the standard library included in the
        // binary

        let std_file = if compiler.settings.use_standard_lib {
            STD_LIBS.iter().find(|tup| tup.0 == module)
        } else {
            None
        };
        Ok(match std_file {
            Some(tup) => Cow::Borrowed(tup.1),
            None => {
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
                file.read_to_string(&mut buffer)
                    .map_err(|err| Error::IO(err.into()))?;
                Cow::Owned(buffer)
            }
        })
    }

    pub fn load_module(
        &self,
        compiler: &mut ModuleCompiler,
        vm: &Thread,
        module_id: &Symbol,
    ) -> Result<(), (Option<ArcType>, MacroError)>
    where
        I: Importer,
    {
        assert!(module_id.is_global());
        let modulename = module_id.name().definition_name();
        // Retrieve the source, first looking in the standard library included in the
        // binary
        let unloaded_module = self
            .get_unloaded_module(vm, &modulename)
            .map_err(|err| (None, MacroError::new(err)))?;

        match unloaded_module {
            UnloadedModule::Extern(ExternModule {
                value,
                typ,
                metadata,
            }) => {
                vm.set_global(module_id.clone(), typ, metadata, value.get_value())
                    .map_err(|err| (None, MacroError::new(err)))?;
            }
            UnloadedModule::Source => {
                self.importer
                    .import(compiler, vm, &modulename)
                    .map_err(|(t, err)| (t, MacroError::new(err)))?;
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
    add_extern_module_(thread, name, Box::new(loader))
}

fn add_extern_module_(thread: &Thread, name: &str, loader: ExternLoader) {
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

macro_rules! add_extern_module_if {
    (
        #[cfg($($features: tt)*)],
        available_if = $msg: expr,
        args($vm: expr, $mod_name: expr, $loader: path)
    ) => {{
        #[cfg($($features)*)]
        $crate::import::add_extern_module($vm, $mod_name, $loader);

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

impl<I> Macro for Import<I>
where
    I: Importer,
{
    fn expand(&self, macros: &mut MacroExpander, args: Vec<SpannedExpr<Symbol>>) -> MacroFuture {
        fn get_module_name(args: &[SpannedExpr<Symbol>]) -> Result<String, Error> {
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

        let modulename = match get_module_name(&args).map_err(MacroError::new) {
            Ok(modulename) => modulename,
            Err(err) => return Box::new(future::err(err)),
        };

        info!("import! {}", modulename);

        let compiler = try_future!(macros
            .user_data
            .downcast_ref::<CompilerDatabase>()
            .ok_or_else(|| MacroError::new(Error::String(
                "`import` requires a `CompilerDatabase` as user data during macro expansion".into(),
            ))));

        Box::new(future::result(
            compiler
                .import(modulename)
                .map_err(|err| MacroError::message(err.to_string()))
                .and_then(|result| result.map_err(MacroError::new))
                .map(|expr| pos::spanned(args[0].span, expr)),
        ))
    }
}
