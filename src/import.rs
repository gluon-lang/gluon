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

use {
    async_trait::async_trait,
    futures::{
        future::{self},
        prelude::*,
    },
    itertools::Itertools,
    salsa::debug::DebugQueryTable,
};

use crate::base::{
    ast::{self, expr_to_path, Expr, Literal, SpannedExpr},
    filename_to_module, pos,
    source::FileId,
    symbol::{Symbol, Symbols},
    types::ArcType,
};

use crate::vm::{
    self,
    gc::Trace,
    macros::{Error as MacroError, LazyMacroResult, Macro, MacroExpander, MacroFuture},
    thread::{RootedThread, Thread},
    vm::VmEnv,
    ExternLoader, ExternModule,
};

use crate::{
    compiler_pipeline::{Salvage, SalvageResult},
    query::{AsyncCompilation, Compilation, CompilerDatabase},
    IoError, ModuleCompiler, ThreadExt,
};

quick_error! {
    /// Error type for the import macro
    #[derive(Debug, Clone, Eq, PartialEq, Hash)]
    pub enum Error {
        /// The importer found a cyclic dependency when loading files
        CyclicDependency(module: String, cycle: Vec<String>) {
            display(
                "Module '{}' occurs in a cyclic dependency: `{}`",
                module,
                cycle.iter().chain(Some(module)).format(" -> ")
            )
        }
        /// Generic message error
        String(message: String) {
            display("{}", message)
        }
        /// The importer could not load the imported file
        IO(err: IoError) {
            display("{}", err)
            from()
        }
    }
}

impl base::error::AsDiagnostic for Error {
    fn as_diagnostic(
        &self,
        _map: &base::source::CodeMap,
    ) -> codespan_reporting::diagnostic::Diagnostic<FileId> {
        codespan_reporting::diagnostic::Diagnostic::error().with_message(self.to_string())
    }
}

include!(concat!(env!("OUT_DIR"), "/std_modules.rs"));

#[async_trait]
pub trait Importer: Any + Clone + Sync + Send {
    async fn import(
        &self,
        compiler: &mut ModuleCompiler<'_, '_>,
        vm: &Thread,
        modulename: &str,
    ) -> SalvageResult<ArcType, crate::Error>;
}

#[derive(Clone)]
pub struct DefaultImporter;
#[async_trait]
impl Importer for DefaultImporter {
    async fn import(
        &self,
        compiler: &mut ModuleCompiler<'_, '_>,
        _vm: &Thread,
        modulename: &str,
    ) -> SalvageResult<ArcType> {
        let result = compiler.database.global(modulename.to_string()).await;
        // Forcibly load module_type so we can salvage a type for the error if necessary
        let _ = compiler
            .database
            .module_type(modulename.to_string(), None)
            .await;

        let value = result.map_err(|error| {
            let value = compiler.database.peek_module_type(modulename);
            Salvage { value, error }
        })?;
        Ok(value.typ)
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
        compiler: &mut ModuleCompiler<'_, '_>,
        vm: &Thread,
        module_id: &Symbol,
    ) -> SalvageResult<ArcType>;
    fn snapshot(&self, thread: RootedThread) -> salsa::Snapshot<CompilerDatabase>;
    fn fork(
        &mut self,
        forker: salsa::ForkState,
        thread: RootedThread,
    ) -> salsa::Snapshot<CompilerDatabase>;
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
        compiler: &mut ModuleCompiler<'_, '_>,
        vm: &Thread,
        module_id: &Symbol,
    ) -> SalvageResult<ArcType> {
        assert!(module_id.is_global());
        let modulename = module_id.name().definition_name();

        self.importer.import(compiler, vm, &modulename).await
    }
    fn snapshot(&self, thread: RootedThread) -> salsa::Snapshot<CompilerDatabase> {
        Self::snapshot(self, thread)
    }
    fn fork(
        &mut self,
        forker: salsa::ForkState,
        thread: RootedThread,
    ) -> salsa::Snapshot<CompilerDatabase> {
        Self::fork(self, forker, thread)
    }
}

/// Macro which rewrites occurances of `import! "filename"` to a load of that file if it is not
/// already loaded and then a global access to the loaded module
pub struct Import<I = DefaultImporter> {
    pub paths: RwLock<Vec<PathBuf>>,
    pub importer: I,

    pub compiler: Mutex<CompilerDatabase>,
}

#[derive(Debug)]
pub struct PtrEq<T>(pub Arc<T>);

impl<T> std::ops::Deref for PtrEq<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> Clone for PtrEq<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> Eq for PtrEq<T> {}

impl<T> PartialEq for PtrEq<T> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl<T> std::hash::Hash for PtrEq<T> {
    fn hash<H: std::hash::Hasher>(&self, hasher: &mut H) {
        (&*self.0 as *const T).hash(hasher)
    }
}

impl<I> Import<I> {
    /// Creates a new import macro
    pub fn new(importer: I) -> Import<I> {
        Import {
            paths: RwLock::new(vec![PathBuf::from(".")]),
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

    pub fn modules(&self, compiler: &mut ModuleCompiler<'_, '_>) -> Vec<Cow<'static, str>> {
        STD_LIBS
            .iter()
            .map(|t| Cow::Borrowed(t.0))
            .chain(
                crate::query::ExternLoaderQuery
                    .in_db(&*compiler.database)
                    .entries::<Vec<_>>()
                    .into_iter()
                    .map(|entry| Cow::Owned(entry.key)),
            )
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

    pub fn snapshot(&self, thread: RootedThread) -> salsa::Snapshot<CompilerDatabase> {
        self.compiler.lock().unwrap().snapshot(thread)
    }

    pub fn fork(
        &mut self,
        forker: salsa::ForkState,
        thread: RootedThread,
    ) -> salsa::Snapshot<CompilerDatabase> {
        self.compiler.lock().unwrap().fork(forker, thread)
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
}

/// Adds an extern module to `thread`, letting it be loaded with `import! name` from gluon code.
///
/// ```
/// use gluon::vm::{self, ExternModule};
/// use gluon::{primitive, record, Thread, ThreadExt};
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
/// #[tokio::main]
/// async fn main() -> gluon::Result<()> {
///     let thread = gluon::new_vm_async().await;
///     add_extern_module(&thread, "my_module", my_module);
///     let script = r#"
///         let module = import! "my_module"
///         module.yell module.message
///     "#;
///     let (result, _) = thread.run_expr_async::<String>("example", script).await?;
///     assert_eq!(result, "HELLO WORLD!");
///     Ok(())
/// }
/// ```
pub fn add_extern_module<F>(thread: &Thread, name: &str, loader: F)
where
    F: Fn(&Thread) -> vm::Result<ExternModule> + Send + Sync + 'static,
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
    F: Fn(&Thread) -> vm::Result<ExternModule> + Send + Sync + 'static,
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
    thread
        .get_database_mut()
        .set_extern_loader(name.into(), PtrEq(Arc::new(loader)));
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
            Some(Box::new(Box::new(crate::query::snapshot_env(
                self.snapshot(thread.root_thread()),
            )) as Box<dyn VmEnv>))
        } else if id == TypeId::of::<Arc<dyn ImportApi>>() {
            Some(Box::new(
                arc_self.clone().downcast_arc::<Self>().ok().unwrap() as Arc<dyn ImportApi>,
            ))
        } else if id == TypeId::of::<salsa::Snapshot<CompilerDatabase>>() {
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

    fn expand<'r, 'a: 'r, 'b: 'r, 'c: 'r, 'ast: 'r>(
        &self,
        macros: &'b mut MacroExpander<'a>,
        _symbols: &'c mut Symbols,
        _arena: &'b mut ast::OwnedArena<'ast, Symbol>,
        args: &'b mut [SpannedExpr<'ast, Symbol>],
    ) -> MacroFuture<'r, 'ast> {
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
                Expr::Literal(Literal::String(ref filename)) => filename_to_module(filename),
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
            .downcast::<salsa::Snapshot<CompilerDatabase>>()
            .map_err(|_| MacroError::new(Error::String(
                "`import` requires a `CompilerDatabase` as user data during macro expansion".into(),
            ))));

        let span = args[0].span;

        #[cfg(feature = "tokio")]
        if let Some(spawn) = macros.spawn {
            use futures::task::SpawnExt;

            let (tx, rx) = tokio::sync::oneshot::channel();
            spawn
                .spawn(Box::pin(async move {
                    let result = std::panic::AssertUnwindSafe(db.import(modulename))
                        .catch_unwind()
                        .await
                        .map(|r| {
                            r.map_err(|salvage| {
                                salvage.map_err(|err| MacroError::message(err.to_string()))
                            })
                        })
                        .unwrap_or_else(|err| {
                            Err(Salvage::from(MacroError::message(
                                err.downcast::<String>()
                                    .map(|s| *s)
                                    .or_else(|e| e.downcast::<&str>().map(|s| String::from(&s[..])))
                                    .unwrap_or_else(|_| "Unknown panic".to_string()),
                            )))
                        });
                    // Drop the database before sending the result, otherwise the forker may drop before the forked database
                    drop(db);
                    let _ = tx.send(result);
                }))
                .unwrap();
            return Box::pin(async move {
                Ok(LazyMacroResult::from(move || {
                    async move {
                        rx.await
                            .unwrap_or_else(|err| {
                                Err(Salvage::from(MacroError::new(Error::String(
                                    err.to_string(),
                                ))))
                            })
                            .map(|id| pos::spanned(span, Expr::Ident(id)))
                            .map_err(|salvage| {
                                salvage.map(|id| pos::spanned(span, Expr::Ident(id)))
                            })
                    }
                    .boxed()
                }))
            });
        }

        Box::pin(async move {
            Ok(LazyMacroResult::from(move || {
                async move {
                    let result = db
                        .import(modulename)
                        .await
                        .map_err(|salvage| {
                            salvage
                                .map(|id| pos::spanned(span, Expr::Ident(id)))
                                .map_err(|err| MacroError::message(err.to_string()))
                        })
                        .map(move |id| pos::spanned(span, Expr::Ident(id)));
                    drop(db);
                    result
                }
                .boxed()
            }))
        })
    }
}

unsafe impl<I> Trace for Import<I> {
    impl_trace! { self, _gc, () }
}
