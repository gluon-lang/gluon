use std::{
    borrow::Cow,
    collections::hash_map,
    ops::Deref,
    result::Result as StdResult,
    sync::{Arc, Mutex, MutexGuard},
};

use salsa::{Database, OwnedDb};

use {
    base::{
        ast::{self, OwnedExpr, TypedIdent},
        fnv::{FnvMap, FnvSet},
        kind::{ArcKind, KindEnv},
        metadata::{Metadata, MetadataEnv},
        pos::BytePos,
        source::{CodeMap, FileMap, Source},
        symbol::{Name, Symbol, SymbolModule, SymbolRef},
        types::{Alias, ArcType, NullInterner, PrimitiveEnv, TypeEnv, TypeExt},
    },
    vm::{
        self,
        api::{OpaqueValue, ValueRef},
        compiler::{CompilerEnv, Variable},
        core::{self, interpreter, optimize::OptimizeEnv, CoreExpr},
        gc::{GcPtr, Trace},
        internal::ClosureData,
        internal::Value,
        macros,
        thread::{RootedThread, RootedValue, Thread, ThreadInternal},
        vm::VmEnv,
        ExternLoader,
    },
};

use crate::{compiler_pipeline::*, import::PtrEq, Error, ModuleCompiler, Result, Settings};

pub use salsa;

#[derive(Debug, Trace)]
#[gluon(crate_name = "gluon_vm")]
pub struct UnrootedValue(RootedValue<RootedThread>);

impl Clone for UnrootedValue {
    fn clone(&self) -> Self {
        let mut value = self.0.clone();
        unsafe {
            value.vm_mut().unroot();
        }
        UnrootedValue(value)
    }
}

impl UnrootedValue {
    unsafe fn root_with(&self, vm: RootedThread) -> RootedValue<RootedThread> {
        vm.root_value(self.0.get_variants())
    }
}

unsafe fn root_global_with(global: UnrootedGlobal, vm: RootedThread) -> DatabaseGlobal {
    let UnrootedGlobal {
        id,
        typ,
        metadata,
        value,
    } = global;
    DatabaseGlobal {
        id,
        typ,
        metadata,
        value: value.root_with(vm),
    }
}
pub type UnrootedGlobal = vm::vm::Global<UnrootedValue>;
pub type DatabaseGlobal = vm::vm::Global<RootedValue<RootedThread>>;

#[derive(Default)]
pub struct State {
    pub(crate) code_map: CodeMap,
    pub(crate) inline_modules: FnvMap<String, Arc<Cow<'static, str>>>,
    pub(crate) index_map: FnvMap<String, BytePos>,
    extern_globals: FnvSet<String>,
}

impl State {
    pub fn update_filemap<S>(&mut self, file: &str, source: S) -> Option<Arc<FileMap>>
    where
        S: Into<String>,
    {
        let index_map = &mut self.index_map;
        let code_map = &mut self.code_map;
        index_map
            .get(file)
            .cloned()
            .and_then(|i| code_map.update(i, source.into()))
            .map(|file_map| {
                index_map.insert(file.into(), file_map.span().start());
                file_map
            })
    }

    #[doc(hidden)]
    pub fn add_filemap<S>(&mut self, file: &str, source: S) -> Arc<FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        match self.get_filemap(file) {
            Some(ref file_map) if file_map.src() == source.as_ref() => return file_map.clone(),
            _ => (),
        }
        let file_map = self.code_map.add_filemap(file.to_string(), source.into());
        self.index_map.insert(file.into(), file_map.span().start());
        file_map
    }

    pub(crate) fn get_or_insert_filemap<S>(&mut self, file: &str, source: S) -> Arc<FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        if let Some(m) = self.get_filemap(file) {
            return m;
        }
        self.add_filemap(file, source)
    }

    pub fn get_filemap(&self, file: &str) -> Option<Arc<FileMap>> {
        self.index_map
            .get(file)
            .and_then(move |i| self.code_map.get(*i))
            .cloned()
    }
}

#[salsa::database(async CompileStorage)]
pub struct CompilerDatabase {
    storage: salsa::Storage<CompilerDatabase>,
    pub(crate) state: Arc<Mutex<State>>,
    // This is only set after calling snapshot on `Import`. `Import` itself can't contain a
    // `RootedThread` as that would create a cycle
    pub(crate) thread: Option<RootedThread>,
}

impl CompilerDatabase {
    pub fn snapshot(&self, thread: RootedThread) -> salsa::Snapshot<Self> {
        salsa::Snapshot::new(Self {
            storage: self.storage.snapshot(),
            state: self.state.clone(),
            thread: Some(thread),
        })
    }

    pub fn fork(&self, state: salsa::ForkState, thread: RootedThread) -> salsa::Snapshot<Self> {
        salsa::Snapshot::new(Self {
            storage: self.storage.fork(state),
            state: self.state.clone(),
            thread: Some(thread),
        })
    }
}

impl crate::query::CompilationBase for CompilerDatabase {
    fn compiler(&self) -> &Self {
        self
    }

    fn code_map(&self) -> CodeMap {
        Self::code_map(self)
    }

    fn state(&self) -> MutexGuard<'_, State> {
        Self::state(self)
    }

    fn get_filemap(&self, file: &str) -> Option<Arc<FileMap>> {
        Self::get_filemap(self, file)
    }

    fn get_or_insert_filemap(&self, file: &str, source: &str) -> Arc<FileMap> {
        Self::get_or_insert_filemap(self, file, source)
    }

    fn add_filemap(&self, file: &str, source: &str) -> Arc<FileMap> {
        Self::add_filemap(self, file, source)
    }

    fn thread(&self) -> &Thread {
        self.thread
            .as_ref()
            .expect("Thread was not set in the compiler")
    }

    fn add_module(&mut self, module: String, contents: &str) {
        let state = self.state.clone();
        let mut state = state.lock().unwrap();

        match state.inline_modules.entry(module.clone()) {
            hash_map::Entry::Occupied(entry) => {
                let entry = entry.into_mut();
                if &**entry != contents {
                    let entry_contents = Arc::make_mut(entry).to_mut();
                    entry_contents.clear();
                    entry_contents.push_str(contents);
                    ModuleTextQuery
                        .in_db_mut(self as &mut dyn Compilation)
                        .invalidate(&module);
                } else {
                    return;
                }
            }
            hash_map::Entry::Vacant(entry) => {
                entry.insert(Arc::new(Cow::Owned(contents.into())));
            }
        }
        state.add_filemap(&module, &contents[..]);
    }

    fn peek_typechecked_source_module(
        &self,
        key: &str,
    ) -> Option<TypecheckValue<Arc<OwnedExpr<Symbol>>>> {
        TypecheckedSourceModuleQuery
            .in_db(self)
            .peek(&(key.into(), None))
            .and_then(|r| match r {
                Ok(t) => Some(t),
                Err(salvage) => salvage.value,
            })
    }

    fn peek_module_type(&self, key: &str) -> Option<ArcType> {
        ModuleTypeQuery
            .in_db(self)
            .peek(&(key.into(), None))
            .and_then(|r| match r {
                Ok(t) => Some(t),
                Err(salvage) => salvage.value,
            })
    }

    fn peek_module_metadata(&self, key: &str) -> Option<Arc<Metadata>> {
        ModuleMetadataQuery
            .in_db(self)
            .peek(&(key.into(), None))
            .and_then(|r| match r {
                Ok(t) => Some(t),
                Err(salvage) => salvage.value,
            })
    }

    fn peek_core_expr(&self, key: &str) -> Option<interpreter::Global<CoreExpr>> {
        CoreExprQuery
            .in_db(self)
            .peek(&(key.into(), None))
            .and_then(|r| r.ok())
    }

    fn peek_global(&self, key: &str) -> Option<DatabaseGlobal> {
        GlobalInnerQuery
            .in_db(self)
            .peek(&key.into())
            .and_then(|r| r.ok())
            .map(|global| unsafe { root_global_with(global, self.thread().root_thread()) })
    }
}

impl salsa::Database for CompilerDatabase {}

impl salsa::ParallelDatabase for CompilerDatabase {
    fn snapshot(&self) -> salsa::Snapshot<Self> {
        panic!("Call CompilerDatabase::snapshot(&self, &Thread)")
    }

    fn fork(&self, _state: salsa::ForkState) -> salsa::Snapshot<Self> {
        panic!("Call CompilerDatabase::fork(&self, &Thread)")
    }
}

impl CompilerDatabase {
    pub(crate) fn new_base(thread: Option<RootedThread>) -> CompilerDatabase {
        let mut compiler = CompilerDatabase {
            state: Default::default(),
            storage: Default::default(),
            thread,
        };
        compiler.set_compiler_settings(Default::default());
        compiler
    }

    pub(crate) fn state(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap()
    }

    pub fn code_map(&self) -> CodeMap {
        self.state().code_map.clone()
    }

    pub fn update_filemap<S>(&self, file: &str, source: S) -> Option<Arc<FileMap>>
    where
        S: Into<String>,
    {
        self.state().update_filemap(file, source)
    }

    pub fn get_filemap(&self, file: &str) -> Option<Arc<FileMap>> {
        self.state().get_filemap(file)
    }

    pub(crate) fn get_or_insert_filemap<S>(&self, file: &str, source: S) -> Arc<FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        self.state().get_or_insert_filemap(file, source)
    }

    #[doc(hidden)]
    pub fn add_filemap<S>(&self, file: &str, source: S) -> Arc<FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        self.state().add_filemap(file, source)
    }

    pub fn set_global(&mut self, name: &str, typ: ArcType, metadata: Arc<Metadata>, value: &Value) {
        let thread = self.thread().root_thread();
        let mut gc = thread.global_env().gc.lock().unwrap();
        let mut cloner = vm::internal::Cloner::new(&thread, &mut gc);
        let mut value: RootedValue<RootedThread> =
            thread.root_value(cloner.deep_clone(&value).unwrap());

        let id = Symbol::from(format!("@{}", name));
        unsafe { value.vm_mut().unroot() };
        self.state().extern_globals.insert(name.into());
        self.set_extern_global(
            name.into(),
            UnrootedGlobal {
                id,
                typ,
                metadata,
                value: UnrootedValue(value),
            },
        )
    }

    pub(crate) fn collect_garbage(&self) {
        let strategy = salsa::SweepStrategy::default()
            .discard_values()
            .sweep_all_revisions();

        ModuleTextQuery.in_db(self).sweep(strategy);
        TypecheckedSourceModuleQuery.in_db(self).sweep(strategy);
        CoreExprQuery.in_db(self).sweep(strategy);
        CompiledModuleQuery.in_db(self).sweep(strategy);
    }
}

pub trait CompilationBase: Send {
    fn compiler(&self) -> &CompilerDatabase;
    fn code_map(&self) -> CodeMap;
    fn state(&self) -> MutexGuard<'_, State>;
    fn get_filemap(&self, file: &str) -> Option<Arc<FileMap>>;
    fn get_or_insert_filemap(&self, file: &str, source: &str) -> Arc<FileMap>;
    fn add_filemap(&self, file: &str, source: &str) -> Arc<FileMap>;
    fn thread(&self) -> &Thread;
    fn add_module(&mut self, module: String, contents: &str);

    fn peek_typechecked_source_module(
        &self,
        key: &str,
    ) -> Option<TypecheckValue<Arc<OwnedExpr<Symbol>>>>;
    fn peek_module_type(&self, key: &str) -> Option<ArcType>;
    fn peek_module_metadata(&self, key: &str) -> Option<Arc<Metadata>>;
    fn peek_core_expr(&self, key: &str) -> Option<interpreter::Global<CoreExpr>>;
    fn peek_global(&self, key: &str) -> Option<DatabaseGlobal>;
}

#[salsa::query_group(CompileStorage)]
pub trait Compilation: CompilationBase {
    #[salsa::input]
    fn compiler_settings(&self) -> Settings;

    #[salsa::input]
    fn extern_loader(&self, module: String) -> PtrEq<ExternLoader>;

    #[doc(hidden)]
    #[salsa::input]
    fn extern_global(&self, name: String) -> UnrootedGlobal;

    #[doc(hidden)]
    #[salsa::cycle(recover_cycle)]
    async fn extern_module(&self, module: String) -> Result<UnrootedGlobal>;

    #[salsa::transparent]
    fn get_extern_global(&self, name: &str) -> Option<DatabaseGlobal>;

    #[salsa::dependencies]
    fn module_text(&self, module: String) -> StdResult<Arc<Cow<'static, str>>, Error>;

    #[salsa::cycle(recover_cycle_typecheck)]
    async fn typechecked_source_module(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> SalvageResult<TypecheckValue<Arc<OwnedExpr<Symbol>>>, Error>;

    async fn module_type(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> SalvageResult<ArcType, Error>;

    async fn module_metadata(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> SalvageResult<Arc<Metadata>, Error>;

    #[salsa::cycle(recover_cycle_expected_type)]
    async fn core_expr(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> StdResult<interpreter::Global<CoreExpr>, Error>;

    #[salsa::cycle(recover_cycle_expected_type)]
    #[salsa::dependencies]
    async fn compiled_module(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> StdResult<OpaqueValue<RootedThread, GcPtr<ClosureData>>, Error>;

    #[salsa::cycle(recover_cycle_salvage)]
    async fn import(&self, module: String) -> SalvageResult<TypedIdent<Symbol>, Error>;

    #[doc(hidden)]
    #[salsa::cycle(recover_cycle)]
    async fn global_inner(&self, name: String) -> Result<UnrootedGlobal>;

    #[salsa::transparent]
    #[salsa::cycle(recover_cycle)]
    async fn global(&self, name: String) -> Result<DatabaseGlobal>;
}

fn recover_cycle_typecheck<T>(
    db: &dyn Compilation,
    cycle: &[String],
    module: &String,
    _: &Option<ArcType>,
) -> SalvageResult<T, Error> {
    Ok(recover_cycle(db, cycle, module)?)
}

fn recover_cycle_expected_type<T>(
    db: &dyn Compilation,
    cycle: &[String],
    module: &String,
    _: &Option<ArcType>,
) -> StdResult<T, Error> {
    recover_cycle(db, cycle, module)
}

fn recover_cycle<T>(
    _db: &dyn Compilation,
    cycle: &[String],
    module: &String,
) -> StdResult<T, Error> {
    let mut cycle: Vec<_> = cycle
        .iter()
        .filter(|k| k.starts_with("import("))
        .map(|k| {
            k.trim_matches(|c: char| c != '"')
                .trim_matches('"')
                .trim_start_matches('@')
                .to_string()
        })
        .collect();
    cycle.pop();
    Err(macros::Error::new(crate::import::Error::CyclicDependency(
        module.to_string(),
        cycle,
    ))
    .into())
}

fn recover_cycle_salvage<T>(
    _db: &dyn Compilation,
    cycle: &[String],
    module: &String,
) -> SalvageResult<T, Error> {
    let mut cycle: Vec<_> = cycle
        .iter()
        .filter(|k| k.starts_with("import("))
        .map(|k| {
            k.trim_matches(|c: char| c != '"')
                .trim_matches('"')
                .trim_start_matches('@')
                .to_string()
        })
        .collect();
    cycle.pop();
    Err(
        Error::from(macros::Error::new(crate::import::Error::CyclicDependency(
            module.to_string(),
            cycle,
        )))
        .into(),
    )
}

fn get_extern_global(db: &dyn Compilation, name: &str) -> Option<DatabaseGlobal> {
    if db.compiler().state().extern_globals.contains(name) {
        unsafe {
            Some(root_global_with(
                db.extern_global(name.into()),
                db.thread().root_thread(),
            ))
        }
    } else {
        None
    }
}

fn module_text(db: &dyn Compilation, module: String) -> StdResult<Arc<Cow<'static, str>>, Error> {
    db.salsa_runtime()
        .report_synthetic_read(salsa::Durability::LOW);

    let opt = { db.compiler().state().inline_modules.get(&module).cloned() };
    let contents = if let Some(contents) = opt {
        contents
    } else {
        let mut filename = module.replace(".", "/");
        filename.push_str(".glu");

        let use_standard_lib = db.compiler_settings().use_standard_lib;
        Arc::new(
            crate::get_import(db.thread())
                .get_module_source(use_standard_lib, &module, &filename)
                .map_err(macros::Error::new)?,
        )
    };

    Ok(contents)
}

async fn typechecked_source_module(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    module: String,
    expected_type: Option<ArcType>,
) -> SalvageResult<TypecheckValue<Arc<OwnedExpr<Symbol>>>, Error> {
    db.salsa_runtime().report_untracked_read();

    let text = db.module_text(module.clone())?;

    let thread = db.thread().root_thread();
    let mut compiler = ModuleCompiler::new(db);
    let value = text
        .typecheck_expected(
            &mut compiler,
            &thread,
            &module,
            &text,
            expected_type.as_ref(),
        )
        .await
        .map_err(|err| err.map(|value| value.map(Arc::new)))?;

    Ok(value.map(Arc::new))
}

async fn module_type(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    name: String,
    expected_type: Option<ArcType>,
) -> SalvageResult<ArcType, Error> {
    if ExternLoaderQuery.in_db(&**db).peek(&name).is_some() {
        let global = db.extern_module(name).await?;
        return Ok(global.typ.clone());
    }
    db.typechecked_source_module(name, expected_type)
        .await
        .map(|module| module.typ)
        .map_err(|err| err.map(|m| m.typ))
}

async fn module_metadata(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    name: String,
    expected_type: Option<ArcType>,
) -> SalvageResult<Arc<Metadata>, Error> {
    if ExternLoaderQuery.in_db(&**db).peek(&name).is_some() {
        let global = db.extern_module(name).await?;
        return Ok(global.metadata.clone());
    }
    db.typechecked_source_module(name, expected_type)
        .await
        .map(|module| module.metadata)
        .map_err(|err| err.map(|m| m.metadata))
}

async fn core_expr(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    module: String,
    expected_type: Option<ArcType>,
) -> StdResult<interpreter::Global<CoreExpr>, Error> {
    db.salsa_runtime().report_untracked_read();

    let value = db
        .typechecked_source_module(module.clone(), expected_type.clone())
        .await?;

    // Ensure the type is stored in the database so we can collect typechecked_source_module later
    db.module_type(module.clone(), expected_type.clone())
        .await?;
    db.module_metadata(module.clone(), expected_type).await?;

    let settings = db.compiler_settings();

    let env = env(db.compiler());
    Ok(core::with_translator(&env, |translator| {
        let expr = translator.translate_expr(value.expr.expr());

        debug!("Translation returned: {}", expr);

        let core_expr = if settings.optimize {
            core::optimize::optimize(&translator.allocator, &env, expr)
        } else {
            interpreter::Global {
                value: core::freeze_expr(&translator.allocator, expr),
                info: Default::default(),
            }
        };
        debug!("Optimization returned: {}", core_expr);

        core_expr
    }))
}

async fn compiled_module(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    module: String,
    expected_type: Option<ArcType>,
) -> StdResult<OpaqueValue<RootedThread, GcPtr<ClosureData>>, Error> {
    let core_expr = db.core_expr(module.clone(), expected_type).await?;
    let settings = db.compiler_settings();

    let mut compiler = ModuleCompiler::new(&mut *db);

    let source = compiler
        .get_filemap(&module)
        .expect("Filemap does not exist");

    let name = Name::new(&module);
    let symbols = SymbolModule::new(
        String::from(AsRef::<str>::as_ref(name.module())),
        &mut compiler.symbols,
    );

    let thread = db.thread().root_thread();
    let env = env(db.compiler());
    let mut compiler = vm::compiler::Compiler::new(
        &env,
        thread.global_env(),
        symbols,
        &source,
        module.clone(),
        settings.emit_debug_info,
    );

    let mut compiled_module = compiler.compile_expr(core_expr.value.expr())?;
    let module_id = Symbol::from(format!("@{}", name));
    compiled_module.function.id = module_id.clone();
    let closure = thread
        .global_env()
        .new_global_thunk(&thread, compiled_module)?;

    Ok(closure)
}

async fn import(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    modulename: String,
) -> SalvageResult<TypedIdent<Symbol>, Error> {
    assert!(!modulename.starts_with('@'));
    let thread = db.thread().root_thread();

    let name = Symbol::from(format!("@{}", modulename));
    let result = crate::get_import(&thread)
        .load_module(&mut ModuleCompiler::new(&mut *db), &thread, &name)
        .await;

    let compiler = db.compiler();
    compiler.collect_garbage();

    let typ = result.map_err(|salvage| {
        salvage.map(|typ| TypedIdent {
            name: name.clone(),
            typ,
        })
    })?;

    Ok(TypedIdent { name, typ })
}

async fn global_inner(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    name: String,
) -> Result<UnrootedGlobal> {
    if ExternLoaderQuery.in_db(db.compiler()).peek(&name).is_some() {
        let global = db.extern_module(name.clone()).await?;

        // Ensure the type is stored in the database so we can collect typechecked_source_module later
        db.module_type(name.clone(), None).await?;
        db.module_metadata(name, None).await?;

        return Ok(global);
    }

    let TypecheckValue { metadata, typ, .. } =
        db.typechecked_source_module(name.clone(), None).await?;

    // Ensure the type is stored in the database so we can collect typechecked_source_module later
    db.module_type(name.clone(), None).await?;
    db.module_metadata(name.clone(), None).await?;

    let closure = db.compiled_module(name.clone(), None).await?;

    let module_id = closure.function.name.clone();

    let vm = db.thread();
    let v = vm
        .call_thunk_top(&closure)
        .await
        .map(move |value| ExecuteValue {
            id: module_id,
            expr: (),
            typ,
            value,
            metadata,
        })
        .map_err(Error::from)?;

    let ExecuteValue {
        id,
        metadata,
        typ,
        value,
        ..
    } = if db.compiler_settings().run_io {
        let vm = db.thread();
        crate::compiler_pipeline::run_io(vm, v).await?
    } else {
        v
    };

    let vm = db.thread();
    let mut gc = vm.global_env().gc.lock().unwrap();
    let mut cloner = vm::internal::Cloner::new(vm, &mut gc);
    let value = cloner.deep_clone(&value)?;

    let mut value: RootedValue<RootedThread> = vm.root_value(value);
    unsafe { value.vm_mut().unroot() };
    Ok(UnrootedGlobal {
        id,
        typ,
        metadata,
        value: UnrootedValue(value),
    })
}

async fn extern_module(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    name: String,
) -> Result<UnrootedGlobal> {
    let id = Symbol::from(format!("@{}", name));
    let loader = db.extern_loader(name);

    for dep in &loader.dependencies {
        db.import(dep.clone()).await?;
    }

    let vm = db.thread();

    let module = (loader.load_fn)(vm)?;
    let mut value = module.value.clone();
    unsafe { value.vm_mut().unroot() }; // FIXME

    Ok(UnrootedGlobal {
        id,
        typ: module.typ.clone(),
        metadata: Arc::new(module.metadata),
        value: UnrootedValue(value),
    })
}

async fn global(
    db: &mut OwnedDb<'_, dyn Compilation + '_>,
    name: String,
) -> Result<DatabaseGlobal> {
    db.global_inner(name)
        .await
        .map(|global| unsafe { root_global_with(global, db.thread().root_thread()) })
}

use std::cell::RefCell;
pub struct Env<T>(RefCell<T>);

pub(crate) fn env(env: &(dyn Compilation + '_)) -> Env<&'_ CompilerDatabase> {
    Env(RefCell::new(env.compiler()))
}
pub(crate) fn snapshot_env<T>(env: T) -> Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    Env(RefCell::new(env))
}

impl<T> CompilerEnv for Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        if id.is_global() {
            self.get_global(id.definition_name())
                .map(|g| (Variable::UpVar(g.id.clone()), g.typ.clone()))
        } else {
            let name = id.definition_name();

            self.0
                .borrow_mut()
                .get_extern_global(name)
                .map(|g| (Variable::UpVar(g.id.clone()), g.typ.clone()))
        }
    }
}

impl<T> KindEnv for Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        if id.is_global() {
            TypeEnv::find_type_info(self, id).map(|t| {
                t.kind(
                    &self
                        .0
                        .borrow_mut()
                        .thread()
                        .global_env()
                        .type_cache()
                        .kind_cache,
                )
                .into_owned()
            })
        } else {
            None
        }
    }
}

impl<T> TypeEnv for Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    type Type = ArcType;

    fn find_type(&self, id: &SymbolRef) -> Option<ArcType> {
        if id.is_global() {
            self.0
                .borrow_mut()
                .get_binding_inner(id.definition_name(), |self_, module| {
                    self_
                        .get_extern_global(module.as_str())
                        .map(|global| global.typ)
                        .or_else(|| self_.peek_module_type(module.as_str().into()))
                })
                .ok()
        } else {
            let name = id.definition_name();

            self.0
                .borrow_mut()
                .get_extern_global(name)
                .map(|global| global.typ.clone())
        }
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        if id.is_global() {
            let env = self.0.borrow();
            let globals = env.thread().global_env().get_globals();
            globals.type_infos.find_type_info(id)
        } else {
            None
        }
    }
}

impl<T> PrimitiveEnv for Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    fn get_bool(&self) -> ArcType {
        self.0
            .borrow_mut()
            .find_type_info("std.types.Bool")
            .expect("std.types.Bool")
            .into_type()
    }
}

impl<T> MetadataEnv for Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>> {
        if id.is_global() {
            self.0
                .borrow_mut()
                .peek_module_metadata(id.definition_name())
        } else {
            None
        }
    }
}

impl<T> OptimizeEnv for Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    fn find_expr(&self, id: &Symbol) -> Option<interpreter::Global<CoreExpr>> {
        if id.is_global() {
            self.0
                .borrow_mut()
                .peek_core_expr(id.definition_name().into())
        } else {
            None
        }
    }
}

unsafe impl<T> Trace for Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    impl_trace! { self, _gc, () }
}

impl<T> VmEnv for Env<T>
where
    T: Deref<Target = CompilerDatabase>,
{
    fn get_global(&self, name: &str) -> Option<vm::vm::Global<RootedValue<RootedThread>>> {
        let module = Name::new(name.trim_start_matches('@'));

        let env = self.0.borrow_mut();
        env.get_extern_global(name)
            .or_else(|| env.peek_global(module.as_str().into()))
    }
}

fn get_scoped_global<'n, T>(
    name: &'n str,
    mut lookup: impl FnMut(&Name) -> Option<T>,
) -> Option<(&'n Name, T)> {
    let mut module = Name::new(name.trim_start_matches('@'));
    // Try to find a global by successively reducing the module path
    // Input: "x.y.z.w"
    // Test: "x.y.z"
    // Test: "x.y"
    // Test: "x"
    // Test: -> Error
    let global = loop {
        if module.as_str() == "" {
            return None;
        }
        if let Some(g) = lookup(module) {
            break g;
        }
        module = module.module();
    };
    let remaining_offset = ::std::cmp::min(name.len(), module.as_str().len() + 1); //Add 1 byte for the '.'
    let remaining_fields = Name::new(&name[remaining_offset..]);
    Some((remaining_fields, global))
}

use crate::base::resolve;
trait Extract: Sized {
    // type Output;
    fn extract(&self, db: &CompilerDatabase, field_name: &str) -> Option<Self>;
    fn typ(&self) -> &ArcType;
    // fn output(&self) -> Self::Output;
}

impl Extract for ArcType {
    fn extract(&self, db: &CompilerDatabase, field_name: &str) -> Option<Self> {
        let typ = resolve::remove_aliases_cow(&env(db), &mut NullInterner, self);
        typ.row_iter()
            .find(|field| field.name.as_str() == field_name)
            .map(|field| field.typ.clone())
    }
    fn typ(&self) -> &ArcType {
        self
    }
}
impl Extract for (RootedValue<RootedThread>, ArcType) {
    fn extract(&self, db: &CompilerDatabase, field_name: &str) -> Option<Self> {
        let (value, typ) = self;
        let typ = resolve::remove_aliases_cow(&env(db), &mut NullInterner, typ);
        typ.row_iter()
            .enumerate()
            .find(|&(_, field)| field.name.as_str() == field_name)
            .map(|(index, field)| match value.get_variants().as_ref() {
                ValueRef::Data(data) => (
                    db.thread().root_value(data.get_variant(index).unwrap()),
                    field.typ.clone(),
                ),
                _ => ice!("Unexpected value {:?}", value),
            })
    }
    fn typ(&self) -> &ArcType {
        &self.1
    }
}

impl CompilerDatabase {
    pub fn find_type_info(&self, name: &str) -> Result<Alias<Symbol, ArcType>> {
        let name = Name::new(name);

        let typ = self.get_binding_inner(name.module().as_str(), |self_, module| {
            self_
                .get_extern_global(module.as_str())
                .map(|global| global.typ)
                .or_else(|| self_.peek_module_type(module.as_str().into()))
        })?;

        let maybe_type_info = {
            let field_name = name.name();
            typ.type_field_iter()
                .find(|field| field.name.as_str() == field_name.as_str())
                .map(|field| &field.typ)
                .cloned()
        };
        maybe_type_info
            .ok_or_else(move || vm::Error::UndefinedField(typ, name.name().as_str().into()).into())
    }

    pub fn get_binding(&self, name: &str) -> Result<(RootedValue<RootedThread>, ArcType)> {
        self.get_binding_inner(name, |self_, module| {
            self_
                .get_extern_global(module.as_str())
                .or_else(|| self_.peek_global(module.as_str().into()))
                .map(|global| (global.value, global.typ))
        })
    }

    fn get_binding_inner<T>(
        &self,
        name: &str,
        mut lookup: impl FnMut(&Self, &Name) -> Option<T>,
    ) -> Result<T>
    where
        T: Extract,
    {
        let (remaining_fields, mut value) = get_scoped_global(name, |n| lookup(self, n))
            .ok_or_else(|| vm::Error::UndefinedBinding(name.into()))?;

        if remaining_fields.as_str().is_empty() {
            // No fields left
            return Ok(value);
        }

        for mut field_name in remaining_fields.components() {
            if field_name.starts_with('(') && field_name.ends_with(')') {
                field_name = &field_name[1..field_name.len() - 1];
            } else if field_name.contains(ast::is_operator_char) {
                return Err(vm::Error::Message(format!(
                    "Operators cannot be used as fields \
                     directly. To access an operator field, \
                     enclose the operator with parentheses \
                     before passing it in. (test.(+) instead of \
                     test.+)"
                ))
                .into());
            }

            value = value.extract(self, field_name).ok_or_else(move || {
                vm::Error::UndefinedField(value.typ().clone(), field_name.into())
            })?;
        }

        Ok(value)
    }

    pub fn get_metadata(&self, name_str: &str) -> Result<Arc<Metadata>> {
        self.get_metadata_(name_str)
            .ok_or_else(|| vm::Error::MetadataDoesNotExist(name_str.into()).into())
    }

    fn get_metadata_(&self, name_str: &str) -> Option<Arc<Metadata>> {
        let (remaining, metadata) = get_scoped_global(name_str, |module| {
            self.get_extern_global(module.as_str())
                .map(|global| global.metadata)
                .or_else(|| self.peek_module_metadata(module.as_str().into()))
        })?;

        let mut metadata = &metadata;

        for field_name in remaining.components() {
            metadata = metadata.module.get(field_name)?
        }
        Some(metadata.clone())
    }

    pub fn as_env(&self) -> Env<&Self> {
        env(self)
    }
}
