use std::{
    borrow::Cow,
    collections::hash_map,
    result::Result as StdResult,
    sync::{Arc, Mutex, MutexGuard},
};

use {futures::prelude::*, salsa::Database};

use {
    base::{
        ast::{self, SendSpannedExpr, TypedIdent},
        fnv::FnvMap,
        kind::{ArcKind, KindEnv},
        metadata::{Metadata, MetadataEnv},
        pos::BytePos,
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
        macros,
        thread::{RootedThread, RootedValue, Thread, ThreadInternal},
        vm::VmEnv,
    },
};

use crate::{compiler_pipeline::*, Error, ModuleCompiler, Result, Settings};

pub use {crate::import::DatabaseSnapshot, salsa};

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
pub(crate) struct State {
    pub(crate) code_map: codespan::CodeMap,
    pub(crate) inline_modules: FnvMap<String, Arc<Cow<'static, str>>>,
    pub(crate) index_map: FnvMap<String, BytePos>,
}

impl State {
    pub fn update_filemap<S>(&mut self, file: &str, source: S) -> Option<Arc<codespan::FileMap>>
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
    pub fn add_filemap<S>(&mut self, file: &str, source: S) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        match self.get_filemap(file) {
            Some(ref file_map) if file_map.src() == source.as_ref() => return file_map.clone(),
            _ => (),
        }
        let file_map = self.code_map.add_filemap(
            codespan::FileName::virtual_(file.to_string()),
            source.into(),
        );
        self.index_map.insert(file.into(), file_map.span().start());
        file_map
    }

    pub(crate) fn get_or_insert_filemap<S>(
        &mut self,
        file: &str,
        source: S,
    ) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        if let Some(i) = self.index_map.get(file) {
            return self.code_map.find_file(*i).unwrap().clone();
        }
        self.add_filemap(file, source)
    }

    pub fn get_filemap(&self, file: &str) -> Option<Arc<codespan::FileMap>> {
        self.index_map
            .get(file)
            .and_then(move |i| self.code_map.find_file(*i))
            .cloned()
    }
}

#[salsa::database(CompileStorage)]
pub struct CompilerDatabase {
    runtime: salsa::Runtime<CompilerDatabase>,
    pub(crate) state: Arc<Mutex<State>>,
    // This is only set after calling snapshot on `Import`. `Import` itself can't contain a
    // `RootedThread` as that would create a cycle
    pub(crate) thread: Option<RootedThread>,
}

impl CompilerDatabase {
    pub fn snapshot(&self, thread: RootedThread) -> salsa::Snapshot<Self> {
        salsa::Snapshot::new(Self {
            runtime: self.runtime.snapshot(self),
            state: self.state.clone(),
            thread: Some(thread),
        })
    }

    pub fn fork(
        &self,
        state: salsa::ForkState<Self>,
        thread: RootedThread,
    ) -> salsa::Snapshot<Self> {
        salsa::Snapshot::new(Self {
            runtime: self.runtime.fork(self, state),
            state: self.state.clone(),
            thread: Some(thread),
        })
    }
}

impl crate::query::CompilationBase for CompilerDatabase {
    fn compiler(&mut self) -> &mut Self {
        self
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
                    self.query_mut(ModuleTextQuery).invalidate(&module);
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

    fn peek_typechecked_module(
        &self,
        key: &str,
    ) -> Option<TypecheckValue<Arc<SendSpannedExpr<Symbol>>>> {
        self.query(TypecheckedModuleQuery)
            .peek(&(key.into(), None))
            .and_then(|r| r.ok())
    }
    fn peek_core_expr(&self, key: &str) -> Option<interpreter::Global<CoreExpr>> {
        self.query(CoreExprQuery)
            .peek(&(key.into(), None))
            .and_then(|r| r.ok())
    }

    fn peek_global(&self, key: &str) -> Option<DatabaseGlobal> {
        self.query(GlobalInnerQuery)
            .peek(&key.into())
            .and_then(|r| r.ok())
            .map(|global| unsafe { root_global_with(global, self.thread().root_thread()) })
    }
}

impl salsa::Database for CompilerDatabase {
    fn salsa_runtime(&self) -> &salsa::Runtime<Self> {
        &self.runtime
    }

    fn salsa_runtime_mut(&mut self) -> &mut salsa::Runtime<Self> {
        &mut self.runtime
    }
}

impl salsa::ParallelDatabase for CompilerDatabase {
    fn snapshot(&self) -> salsa::Snapshot<Self> {
        panic!("Call CompilerDatabase::snapshot(&self, &Thread)")
    }

    fn fork(&self, _state: salsa::ForkState<Self>) -> salsa::Snapshot<Self> {
        panic!("Call CompilerDatabase::fork(&self, &Thread)")
    }
}

impl CompilerDatabase {
    pub(crate) fn new_base(thread: Option<RootedThread>) -> CompilerDatabase {
        let mut compiler = CompilerDatabase {
            state: Default::default(),
            runtime: Default::default(),
            thread,
        };
        compiler.set_compiler_settings(Default::default());
        compiler
    }

    pub(crate) fn state(&self) -> MutexGuard<State> {
        self.state.lock().unwrap()
    }

    pub fn code_map(&self) -> codespan::CodeMap {
        self.state().code_map.clone()
    }

    pub fn update_filemap<S>(&self, file: &str, source: S) -> Option<Arc<codespan::FileMap>>
    where
        S: Into<String>,
    {
        self.state().update_filemap(file, source)
    }

    pub fn get_filemap(&self, file: &str) -> Option<Arc<codespan::FileMap>> {
        self.state().get_filemap(file)
    }

    pub(crate) fn get_or_insert_filemap<S>(&self, file: &str, source: S) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        self.state().get_or_insert_filemap(file, source)
    }

    #[doc(hidden)]
    pub fn add_filemap<S>(&self, file: &str, source: S) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        self.state().add_filemap(file, source)
    }

    pub(crate) fn collect_garbage(&mut self) {
        let strategy = salsa::SweepStrategy::default()
            .discard_values()
            .sweep_all_revisions();

        self.query(ModuleTextQuery).sweep(strategy);
        self.query(TypecheckedModuleQuery).sweep(strategy);
        self.query(CoreExprQuery).sweep(strategy);
        self.query(CompiledModuleQuery).sweep(strategy);
    }
}

pub trait CompilationBase: Send {
    fn compiler(&mut self) -> &mut CompilerDatabase;
    fn thread(&self) -> &Thread;
    fn add_module(&mut self, module: String, contents: &str);

    fn peek_typechecked_module(
        &self,
        key: &str,
    ) -> Option<TypecheckValue<Arc<SendSpannedExpr<Symbol>>>>;
    fn peek_core_expr(&self, key: &str) -> Option<interpreter::Global<CoreExpr>>;
    fn peek_global(&self, key: &str) -> Option<DatabaseGlobal>;
}

#[salsa::query_group(CompileStorage)]
pub trait Compilation: CompilationBase {
    #[salsa::input]
    fn compiler_settings(&self) -> Settings;

    #[salsa::dependencies]
    fn module_text(&self, module: String) -> StdResult<Arc<Cow<'static, str>>, Error>;

    #[salsa::cycle(recover_cycle_typecheck)]
    async fn typechecked_module(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> StdResult<
        TypecheckValue<Arc<SendSpannedExpr<Symbol>>>,
        (Option<TypecheckValue<Arc<SendSpannedExpr<Symbol>>>>, Error),
    >;

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

    #[salsa::cycle(recover_cycle)]
    async fn import(&self, module: String) -> StdResult<TypedIdent<Symbol>, Error>;

    #[doc(hidden)]
    #[salsa::cycle(recover_cycle)]
    async fn global_inner(&self, name: String) -> Result<UnrootedGlobal>;

    #[salsa::transparent]
    #[salsa::cycle(recover_cycle)]
    async fn global(&self, name: String) -> Result<DatabaseGlobal>;
}

fn recover_cycle_typecheck<T>(
    db: &mut dyn Compilation,
    cycle: &[String],
    module: &String,
    _: &Option<ArcType>,
) -> StdResult<T, (Option<T>, Error)> {
    recover_cycle(db, cycle, module).map_err(|err| (None, err))
}

fn recover_cycle_expected_type<T>(
    db: &mut dyn Compilation,
    cycle: &[String],
    module: &String,
    _: &Option<ArcType>,
) -> StdResult<T, Error> {
    recover_cycle(db, cycle, module)
}

fn recover_cycle<T>(
    _db: &mut dyn Compilation,
    cycle: &[String],
    module: &String,
) -> StdResult<T, Error> {
    Err(macros::Error::new(crate::import::Error::CyclicDependency(
        module.to_string(),
        cycle
            .iter()
            .filter(|k| k.contains("import"))
            .map(|k| {
                k.trim_matches(|c: char| c != '"')
                    .trim_matches('"')
                    .trim_start_matches('@')
                    .to_string()
            })
            .collect(),
    ))
    .into())
}

fn module_text(
    db: &mut (impl Compilation + salsa::Database),
    module: String,
) -> StdResult<Arc<Cow<'static, str>>, Error> {
    db.salsa_runtime_mut()
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

async fn typechecked_module(
    db: &mut (impl Compilation + salsa::Database),
    module: String,
    expected_type: Option<ArcType>,
) -> StdResult<
    TypecheckValue<Arc<SendSpannedExpr<Symbol>>>,
    (Option<TypecheckValue<Arc<SendSpannedExpr<Symbol>>>>, Error),
> {
    db.salsa_runtime_mut().report_untracked_read();

    let text = db.module_text(module.clone()).map_err(|err| (None, err))?;

    let thread = db.thread().root_thread();
    let mut compiler = ModuleCompiler::new(db.compiler());
    let value = text
        .typecheck_expected(
            &mut compiler,
            &thread,
            &module,
            &text,
            expected_type.as_ref(),
        )
        .map_err(|(opt, err)| (opt.map(|value| value.map(Arc::new)), err))
        .await?;

    Ok(value.map(Arc::new))
}

async fn core_expr(
    db: &mut (impl Compilation + salsa::Database),
    module: String,
    expected_type: Option<ArcType>,
) -> StdResult<interpreter::Global<CoreExpr>, Error> {
    db.salsa_runtime_mut().report_untracked_read();

    let value = db
        .typechecked_module(module.clone(), expected_type)
        .map_err(|(_, err)| err)
        .await?;
    let settings = db.compiler_settings();

    let env = db.compiler();
    Ok(core::with_translator(&*env, |translator| {
        let expr = translator.translate_expr(value.expr.expr());

        debug!("Translation returned: {}", expr);

        let core_expr = if settings.optimize {
            core::optimize::optimize(&translator.allocator, env, expr)
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
    db: &mut dyn Compilation,
    module: String,
    expected_type: Option<ArcType>,
) -> StdResult<OpaqueValue<RootedThread, GcPtr<ClosureData>>, Error> {
    let core_expr = db.core_expr(module.clone(), expected_type).await?;
    let settings = db.compiler_settings();

    let mut compiler = ModuleCompiler::new(db.compiler());

    let source = compiler
        .get_filemap(&module)
        .expect("Filemap does not exist");

    let name = Name::new(&module);
    let symbols = SymbolModule::new(
        String::from(AsRef::<str>::as_ref(name.module())),
        &mut compiler.symbols,
    );

    let env = db.compiler();
    let mut compiler = vm::compiler::Compiler::new(
        &*env,
        env.thread().global_env(),
        symbols,
        &source,
        module.clone(),
        settings.emit_debug_info,
    );

    let mut compiled_module = compiler.compile_expr(core_expr.value.expr())?;
    let module_id = Symbol::from(format!("@{}", name));
    compiled_module.function.id = module_id.clone();
    let closure = env
        .thread()
        .global_env()
        .new_global_thunk(&env.thread(), compiled_module)?;

    Ok(closure)
}

async fn import(
    db: &mut dyn Compilation,
    modulename: String,
) -> StdResult<TypedIdent<Symbol>, Error> {
    let thread = db.thread().root_thread();
    let compiler = db.compiler();

    let name = Symbol::from(if modulename.starts_with('@') {
        modulename.clone()
    } else {
        format!("@{}", modulename)
    });
    let result = crate::get_import(&thread)
        .load_module(&mut ModuleCompiler::new(compiler), &thread, &name)
        .await
        .map_err(|(_, err)| err);

    compiler.collect_garbage();

    let typ = result?;

    Ok(TypedIdent { name, typ })
}

async fn global_inner(db: &mut dyn Compilation, name: String) -> Result<UnrootedGlobal> {
    let TypecheckValue { metadata, typ, .. } = db
        .typechecked_module(name.clone(), None)
        .map_err(|(_, err)| err)
        .await?;
    let closure = db.compiled_module(name.clone(), None).await?;

    let module_id = closure.function.name.clone();

    let vm = db.thread();
    let v = vm
        .call_thunk_top(&closure)
        .map_ok(move |value| ExecuteValue {
            id: module_id,
            expr: (),
            typ,
            value,
            metadata,
        })
        .map_err(Error::from)
        .await?;

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

async fn global(db: &mut dyn Compilation, name: String) -> Result<DatabaseGlobal> {
    db.global_inner(name)
        .await
        .map(|global| unsafe { root_global_with(global, db.thread().root_thread()) })
}

impl CompilerEnv for CompilerDatabase {
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        if id.is_global() {
            self.get_global(id.definition_name())
                .map(|g| (Variable::UpVar(g.id.clone()), g.typ.clone()))
        } else {
            let name = id.definition_name();

            let globals = self.thread().global_env().get_globals();
            globals
                .globals
                .get(name)
                .map(|g| (Variable::UpVar(g.id.clone()), g.typ.clone()))
        }
    }
}

impl KindEnv for CompilerDatabase {
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        if id.is_global() {
            TypeEnv::find_type_info(self, id).map(|t| {
                t.kind(&self.thread().global_env().type_cache().kind_cache)
                    .into_owned()
            })
        } else {
            None
        }
    }
}

impl TypeEnv for CompilerDatabase {
    type Type = ArcType;

    fn find_type(&self, id: &SymbolRef) -> Option<ArcType> {
        if id.is_global() {
            self.get_global(id.definition_name()).map(|g| g.typ.clone())
        } else {
            let name = id.definition_name();

            let globals = self.thread().global_env().get_globals();
            globals.globals.get(name).map(|global| global.typ.clone())
        }
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        if id.is_global() {
            let globals = self.thread().global_env().get_globals();
            globals.type_infos.find_type_info(id)
        } else {
            None
        }
    }
}

impl PrimitiveEnv for CompilerDatabase {
    fn get_bool(&self) -> ArcType {
        self.find_type_info("std.types.Bool")
            .expect("std.types.Bool")
            .into_type()
    }
}

impl MetadataEnv for CompilerDatabase {
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>> {
        if id.is_global() {
            self.peek_typechecked_module(id.definition_name())
                .map(|v| v.metadata.clone())
        } else {
            None
        }
    }
}

impl OptimizeEnv for CompilerDatabase {
    fn find_expr(&self, id: &Symbol) -> Option<interpreter::Global<CoreExpr>> {
        if id.is_global() {
            self.peek_core_expr(id.definition_name().into())
        } else {
            None
        }
    }
}

unsafe impl Trace for CompilerDatabase {
    impl_trace! { self, _gc, () }
}

impl VmEnv for CompilerDatabase {
    fn get_global(&self, name: &str) -> Option<vm::vm::Global<RootedValue<RootedThread>>> {
        let module = Name::new(name.trim_start_matches('@'));

        let globals = self.thread().global_env().get_globals();
        globals
            .globals
            .get(name)
            .map(|global| DatabaseGlobal {
                id: global.id.clone(),
                typ: global.typ.clone(),
                metadata: global.metadata.clone(),
                value: self.thread().root_value(global.value.get_variants()),
            })
            .or_else(|| self.peek_global(module.as_str().into()))
    }
}

impl CompilerEnv for DatabaseSnapshot {
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        CompilerEnv::find_var(&**self, id)
    }
}

impl KindEnv for DatabaseSnapshot {
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        KindEnv::find_kind(&**self, id)
    }
}

impl TypeEnv for DatabaseSnapshot {
    type Type = ArcType;

    fn find_type(&self, id: &SymbolRef) -> Option<ArcType> {
        TypeEnv::find_type(&**self, id)
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        TypeEnv::find_type_info(&**self, id)
    }
}

impl PrimitiveEnv for DatabaseSnapshot {
    fn get_bool(&self) -> ArcType {
        (&**self).get_bool()
    }
}

impl MetadataEnv for DatabaseSnapshot {
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>> {
        MetadataEnv::get_metadata(&**self, id)
    }
}

impl OptimizeEnv for DatabaseSnapshot {
    fn find_expr(&self, id: &Symbol) -> Option<interpreter::Global<CoreExpr>> {
        (&**self).find_expr(id)
    }
}

unsafe impl Trace for DatabaseSnapshot {
    fn trace(&self, gc: &mut vm::gc::Gc) {
        (**self).trace(gc)
    }
}

impl VmEnv for DatabaseSnapshot {
    fn get_global(&self, name: &str) -> Option<vm::vm::Global<RootedValue<RootedThread>>> {
        VmEnv::get_global(&**self, name)
    }
}

impl CompilerDatabase {
    pub fn find_type_info(&self, name: &str) -> Result<Alias<Symbol, ArcType>> {
        let name = Name::new(name);
        let (_, typ) = self.get_binding(name.module().as_str())?;
        let maybe_type_info = {
            let field_name = name.name();
            typ.type_field_iter()
                .find(|field| field.name.as_ref() == field_name.as_str())
                .map(|field| &field.typ)
                .cloned()
        };
        maybe_type_info
            .ok_or_else(move || vm::Error::UndefinedField(typ, name.name().as_str().into()).into())
    }

    fn get_scoped_global<'s, 'n>(&'s self, name: &'n str) -> Option<(&'n Name, DatabaseGlobal)> {
        let mut module = Name::new(name.trim_start_matches('@'));
        // Try to find a global by successively reducing the module path
        // Input: "x.y.z.w"
        // Test: "x.y.z"
        // Test: "x.y"
        // Test: "x"
        // Test: -> Error
        let globals = self.thread().global_env().get_globals();
        let global = loop {
            if module.as_str() == "" {
                return None;
            }
            if let Some(g) = globals
                .globals
                .get(name)
                .map(|global| DatabaseGlobal {
                    id: global.id.clone(),
                    typ: global.typ.clone(),
                    metadata: global.metadata.clone(),
                    value: self.thread().root_value(global.value.get_variants()),
                })
                .or_else(|| self.peek_global(module.as_str().into()))
            {
                break g;
            }
            module = module.module();
        };
        let remaining_offset = ::std::cmp::min(name.len(), module.as_str().len() + 1); //Add 1 byte for the '.'
        let remaining_fields = Name::new(&name[remaining_offset..]);
        Some((remaining_fields, global))
    }

    pub fn get_binding(&self, name: &str) -> Result<(RootedValue<RootedThread>, ArcType)> {
        use crate::base::resolve;

        let (remaining_fields, global) = self
            .get_scoped_global(name)
            .ok_or_else(|| vm::Error::UndefinedBinding(name.into()))?;

        if remaining_fields.as_str().is_empty() {
            // No fields left
            return Ok((global.value, global.typ.clone()));
        }

        let mut typ = global.typ;
        let mut value = global.value.get_variant();

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
            typ = resolve::remove_aliases(self, &mut NullInterner, typ);
            let next_type = {
                typ.row_iter()
                    .enumerate()
                    .find(|&(_, field)| field.name.as_ref() == field_name)
                    .map(|(index, field)| match value.as_ref() {
                        ValueRef::Data(data) => {
                            value = data.get_variant(index).unwrap();
                            &field.typ
                        }
                        _ => ice!("Unexpected value {:?}", value),
                    })
                    .cloned()
            };
            typ =
                next_type.ok_or_else(move || vm::Error::UndefinedField(typ, field_name.into()))?;
        }
        Ok((self.thread().root_value(value), typ))
    }

    pub fn get_metadata(&self, name_str: &str) -> Result<Arc<Metadata>> {
        self.get_metadata_(name_str)
            .ok_or_else(|| vm::Error::MetadataDoesNotExist(name_str.into()).into())
    }

    fn get_metadata_(&self, name_str: &str) -> Option<Arc<Metadata>> {
        let (remaining, global) = self.get_scoped_global(name_str)?;

        let mut metadata = &global.metadata;
        for field_name in remaining.components() {
            metadata = metadata.module.get(field_name)?
        }
        Some(metadata.clone())
    }
}
