//! Implementation of the `import!` macro.

use std::{
    any::{Any, TypeId},
    borrow::Cow,
    fs::File,
    io::Read,
    mem,
    ops::{Deref, DerefMut},
    path::PathBuf,
    sync::{Arc, Mutex, MutexGuard, RwLock},
};

use async_trait::async_trait;
use futures::{
    future::{self, BoxFuture},
    prelude::*,
    task::SpawnExt,
};
use itertools::Itertools;

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
    gc::Trace,
    macros::{Error as MacroError, Macro, MacroExpander, MacroFuture},
    thread::{RootedThread, Thread, ThreadInternal},
    vm::VmEnv,
    ExternLoader, ExternModule,
};

use crate::{
    query::{Compilation, CompilerDatabase},
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

#[async_trait]
pub trait Importer: Any + Clone + Sync + Send {
    async fn import(
        &self,
        compiler: &mut ModuleCompiler<'_>,
        vm: &Thread,
        modulename: &str,
    ) -> Result<ArcType, (Option<ArcType>, crate::Error)>;
}

#[derive(Clone)]
pub struct DefaultImporter;
#[async_trait]
impl Importer for DefaultImporter {
    async fn import(
        &self,
        compiler: &mut ModuleCompiler<'_>,
        _vm: &Thread,
        modulename: &str,
    ) -> Result<ArcType, (Option<ArcType>, crate::Error)> {
        let value = compiler
            .database
            .global(modulename.to_string())
            .await
            .map_err(|err| (None, err))?;
        Ok(value.typ)
    }
}

enum UnloadedModule {
    Source,
    Extern(Vec<String>),
}

pub struct DatabaseSnapshot {
    snapshot: Option<salsa::Snapshot<CompilerDatabase>>,
}

impl Deref for DatabaseSnapshot {
    type Target = CompilerDatabase;
    fn deref(&self) -> &Self::Target {
        self.snapshot.as_ref().unwrap()
    }
}

impl DerefMut for DatabaseSnapshot {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.snapshot.as_mut().unwrap()
    }
}

pub struct DatabaseFork {
    fork: Option<salsa::Fork<CompilerDatabase>>,
}

impl Deref for DatabaseFork {
    type Target = CompilerDatabase;
    fn deref(&self) -> &Self::Target {
        self.fork.as_ref().unwrap()
    }
}

impl DerefMut for DatabaseFork {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.fork.as_mut().unwrap()
    }
}

pub struct DatabaseMut {
    // Only needed to ensure that the the `Compiler` the guard points to lives long enough
    _import: Arc<dyn Macro>,
    // This isn't actually static but relies on `import` to live longer than the guard
    compiler: Option<MutexGuard<'static, CompilerDatabase>>,
}

impl Drop for DatabaseMut {
    fn drop(&mut self) {
        // The compiler moves back to only be owned by the import so we need to remove the thread
        // to break the cycle
        self.thread = None;
        self.compiler.take();
    }
}

impl Deref for DatabaseMut {
    type Target = CompilerDatabase;
    fn deref(&self) -> &Self::Target {
        self.compiler.as_ref().unwrap()
    }
}

impl DerefMut for DatabaseMut {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.compiler.as_mut().unwrap()
    }
}

#[async_trait]
pub(crate) trait ImportApi: Send + Sync {
    fn get_module_source(
        &self,
        use_standard_lib: bool,
        module: &str,
        filename: &str,
    ) -> Result<Cow<'static, str>, Error>;
    async fn load_module(
        &self,
        compiler: &mut ModuleCompiler<'_>,
        vm: &Thread,
        module_id: &Symbol,
    ) -> Result<ArcType, (Option<ArcType>, MacroError)>;
    fn snapshot(&self, thread: RootedThread) -> DatabaseSnapshot;
    fn fork(
        &self,
        forker: Arc<salsa::ForkState<CompilerDatabase>>,
        thread: RootedThread,
    ) -> DatabaseFork;
}

#[async_trait]
impl<I> ImportApi for Import<I>
where
    I: Importer,
{
    fn get_module_source(
        &self,
        use_standard_lib: bool,
        module: &str,
        filename: &str,
    ) -> Result<Cow<'static, str>, Error> {
        Self::get_module_source(self, use_standard_lib, module, filename)
    }
    async fn load_module(
        &self,
        compiler: &mut ModuleCompiler<'_>,
        vm: &Thread,
        module_id: &Symbol,
    ) -> Result<ArcType, (Option<ArcType>, MacroError)> {
        Self::load_module(self, compiler, vm, module_id).await
    }
    fn snapshot(&self, thread: RootedThread) -> DatabaseSnapshot {
        Self::snapshot(self, thread)
    }
    fn fork(
        &self,
        forker: Arc<salsa::ForkState<CompilerDatabase>>,
        thread: RootedThread,
    ) -> DatabaseFork {
        Self::fork(self, forker, thread)
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

    pub fn database_mut(self: Arc<Self>, thread: RootedThread) -> DatabaseMut
    where
        I: Importer,
    {
        // Since `self` lives longer than the lifetime in the mutex guard this is safe
        let mut compiler = unsafe {
            DatabaseMut {
                compiler: Some(mem::transmute::<
                    MutexGuard<CompilerDatabase>,
                    MutexGuard<CompilerDatabase>,
                >(self.compiler.lock().unwrap())),
                _import: self,
            }
        };

        compiler.thread = Some(thread);

        compiler
    }

    pub fn snapshot(&self, thread: RootedThread) -> DatabaseSnapshot {
        let snapshot = self.compiler.lock().unwrap().snapshot(thread);

        DatabaseSnapshot {
            snapshot: Some(snapshot),
        }
    }

    pub fn fork(
        &self,
        forker: Arc<salsa::ForkState<CompilerDatabase>>,
        thread: RootedThread,
    ) -> DatabaseFork {
        let fork = self.compiler.lock().unwrap().fork(forker, thread);

        DatabaseFork { fork: Some(fork) }
    }

    fn get_unloaded_module(&self, module: &str) -> UnloadedModule {
        {
            let loaders = self.loaders.read().unwrap();
            if let Some(loader) = loaders.get(module) {
                return UnloadedModule::Extern(loader.dependencies.clone());
            }
        }
        UnloadedModule::Source
    }

    pub(crate) fn get_module_source(
        &self,
        use_standard_lib: bool,
        module: &str,
        filename: &str,
    ) -> Result<Cow<'static, str>, Error> {
        let mut buffer = String::new();

        // Retrieve the source, first looking in the standard library included in the
        // binary

        let std_file = if use_standard_lib {
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

    pub async fn load_module(
        &self,
        compiler: &mut ModuleCompiler<'_>,
        vm: &Thread,
        module_id: &Symbol,
    ) -> Result<ArcType, (Option<ArcType>, MacroError)>
    where
        I: Importer,
    {
        assert!(module_id.is_global());
        let modulename = module_id.name().definition_name();
        // Retrieve the source, first looking in the standard library included in the
        // binary
        let unloaded_module = self.get_unloaded_module(&modulename);

        Ok(match unloaded_module {
            UnloadedModule::Extern(dependencies) => {
                for dep in dependencies {
                    let dep_id = Symbol::from(if dep.starts_with('@') {
                        dep
                    } else {
                        format!("@{}", dep)
                    });
                    self.load_module_boxed(compiler, vm, &dep_id).await?;
                }

                let ExternModule {
                    value,
                    typ,
                    metadata,
                } = (self
                    .loaders
                    .write()
                    .unwrap()
                    .get_mut(modulename)
                    .expect("bug: Missing loader but it was already seen in get_unloaded_module")
                    .load_fn)(vm)
                .map_err(|err| (None, MacroError::new(err)))?;

                vm.set_global(
                    module_id.clone(),
                    typ.clone(),
                    metadata.into(),
                    value.get_value(),
                )
                .map_err(|err| (None, MacroError::new(err)))?;
                typ
            }
            UnloadedModule::Source => self
                .importer
                .import(compiler, vm, &modulename)
                .await
                .map_err(|(t, err)| (t, MacroError::new(err)))?,
        })
    }

    fn load_module_boxed<'a, 'b>(
        &'a self,
        compiler: &'a mut ModuleCompiler<'b>,
        vm: &'a Thread,
        module_id: &'a Symbol,
    ) -> BoxFuture<'a, Result<ArcType, (Option<ArcType>, MacroError)>>
    where
        I: Importer,
    {
        self.load_module(compiler, vm, module_id).boxed()
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
/// use gluon::{Thread, ThreadExt};
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
///     let (result, _) = thread.run_expr::<String>("example", script)?;
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
    add_extern_module_(
        thread,
        name,
        ExternLoader {
            load_fn: Box::new(loader),
            dependencies: Vec::new(),
        },
    )
}

pub fn add_extern_module_with_deps<F>(
    thread: &Thread,
    name: &str,
    loader: F,
    dependencies: Vec<String>,
) where
    F: FnMut(&Thread) -> vm::Result<ExternModule> + Send + Sync + 'static,
{
    add_extern_module_(
        thread,
        name,
        ExternLoader {
            load_fn: Box::new(loader),
            dependencies,
        },
    )
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
        $(dependencies = $dependencies: expr,)?
        args($vm: expr, $mod_name: expr, $loader: path)
    ) => {{
        #[cfg($($features)*)]
        $crate::import::add_extern_module_with_deps(
            $vm,
            $mod_name,
            $loader,
            None.into_iter() $( .chain($dependencies.iter().cloned()) )? .map(|s: &str| s.into()).collect::<Vec<String>>()
        );

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
    fn get_capability_impl(
        &self,
        thread: &Thread,
        arc_self: &Arc<dyn Macro>,
        id: TypeId,
    ) -> Option<Box<dyn Any>> {
        if id == TypeId::of::<Box<dyn VmEnv>>() {
            Some(Box::new(
                Box::new(self.snapshot(thread.root_thread())) as Box<dyn VmEnv>
            ))
        } else if id == TypeId::of::<Arc<dyn ImportApi>>() {
            Some(Box::new(
                arc_self.clone().downcast_arc::<Self>().ok().unwrap() as Arc<dyn ImportApi>,
            ))
        } else if id == TypeId::of::<DatabaseSnapshot>() {
            Some(Box::new(self.snapshot(thread.root_thread())))
        } else if id == TypeId::of::<DatabaseMut>() {
            Some(Box::new(
                arc_self
                    .clone()
                    .downcast_arc::<Self>()
                    .ok()
                    .unwrap()
                    .database_mut(thread.root_thread()),
            ))
        } else {
            None
        }
    }

    fn expand<'a>(
        &self,
        macros: &mut MacroExpander<'a>,
        args: Vec<SpannedExpr<Symbol>>,
    ) -> MacroFuture<'a> {
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
            Err(err) => return Box::pin(future::err(err)),
        };

        info!("import! {}", modulename);

        let mut db = try_future!(macros
            .userdata
            .fork(macros.vm.root_thread())
            .downcast::<salsa::Fork<CompilerDatabase>>()
            .map_err(|_| MacroError::new(Error::String(
                "`import` requires a `CompilerDatabase` as user data during macro expansion".into(),
            ))));

        let span = args[0].span;

        if let Some(spawn) = macros.spawn {
            let (tx, rx) = tokio_sync::oneshot::channel();
            spawn
                .spawn(Box::pin(async move {
                    let result = db
                        .import(modulename)
                        .map_err(|err| MacroError::message(err.to_string()))
                        .map_ok(move |expr| pos::spanned(span, expr))
                        .await;
                    drop(db); // Drop the database before sending the result, otherwise the forker may drop before the forked database
                    let _ = tx.send(result);
                }))
                .unwrap();
            Box::pin(rx.map(|r| {
                r.unwrap_or_else(|err| Err(MacroError::new(Error::String(err.to_string()))))
            }))
        } else {
            Box::pin(async move {
                db.import(modulename)
                    .map_err(|err| MacroError::message(err.to_string()))
                    .map_ok(move |expr| pos::spanned(span, expr))
                    .await
            })
        }
    }
}

unsafe impl<I> Trace for Import<I> {
    impl_trace! { self, _gc, () }
}
