use std::{
    borrow::Cow,
    result::Result as StdResult,
    sync::{Arc, Mutex, MutexGuard},
};

use {futures::Future, salsa::Database};

use {
    base::{
        ast::{self, Expr, SpannedExpr, TypedIdent},
        error::Errors,
        fnv::FnvMap,
        kind::{ArcKind, KindEnv},
        metadata::{Metadata, MetadataEnv},
        pos::BytePos,
        symbol::{Name, Symbol, SymbolModule, SymbolRef},
        types::{Alias, ArcType, NullInterner, PrimitiveEnv, TypeEnv, TypeExt},
    },
    vm::{
        self,
        api::ValueRef,
        compiler::{CompiledModule, CompilerEnv, Variable},
        core::{self, CoreExpr},
        internal::Value,
        macros,
        thread::{RootedThread, RootedValue, Thread, ThreadInternal},
        vm::VmEnv,
    },
};

use crate::{compiler_pipeline::*, import::DatabaseSnapshot, Compiler, Error, Result, Settings};

#[derive(Default)]
pub(crate) struct State {
    pub(crate) code_map: codespan::CodeMap,
    pub(crate) inline_modules: FnvMap<String, String>,
    pub(crate) index_map: FnvMap<String, BytePos>,
    pub(crate) errors: Errors<Error>,
    pub(crate) module_states: FnvMap<String, usize>,
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

    pub fn get_filemap(&self, file: &str) -> Option<&Arc<codespan::FileMap>> {
        self.index_map
            .get(file)
            .and_then(move |i| self.code_map.find_file(*i))
    }

    #[doc(hidden)]
    pub fn add_filemap<S>(&mut self, file: &str, source: S) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        match self.get_filemap(file) {
            Some(file_map) if file_map.src() == source.as_ref() => return file_map.clone(),
            _ => (),
        }
        let file_map = self.code_map.add_filemap(
            codespan::FileName::virtual_(file.to_string()),
            source.into(),
        );
        self.index_map.insert(file.into(), file_map.span().start());
        file_map
    }

    pub(crate) fn get_or_insert_filemap<S>(&self, file: &str, source: S) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        self.state().get_or_insert_filemap(file, source)
    }

    pub fn get_filemap(&self, file: &str) -> Option<Arc<codespan::FileMap>> {
        self.state().get_filemap(file).cloned()
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

impl crate::query::CompilationBase for CompilerDatabase {
    fn compiler(&self) -> &Self {
        self
    }

    fn thread(&self) -> &Thread {
        self.thread
            .as_ref()
            .expect("Thread was not set in the compiler")
    }

    fn invalidate_module(&self, module: String, contents: &str) {
        let mut state = self.state();
        state.add_filemap(&module, &contents[..]);
        state
            .module_states
            .entry(module)
            .and_modify(|v| *v += 1)
            .or_default();
    }

    fn report_errors(&self, error: &mut Iterator<Item = Error>) {
        self.state().errors.extend(error);
    }
}

impl salsa::Database for CompilerDatabase {
    fn salsa_runtime(&self) -> &salsa::Runtime<Self> {
        &self.runtime
    }
}

impl salsa::ParallelDatabase for CompilerDatabase {
    fn snapshot(&self) -> salsa::Snapshot<Self> {
        salsa::Snapshot::new(Self {
            runtime: self.runtime.snapshot(self),
            state: self.state.clone(),
            thread: self.thread.clone(),
        })
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
        compiler.set_module_states(Default::default());
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
        self.state().get_filemap(file).cloned()
    }

    #[doc(hidden)]
    pub fn add_filemap<S>(&self, file: &str, source: S) -> Arc<codespan::FileMap>
    where
        S: AsRef<str> + Into<String>,
    {
        self.state().add_filemap(file, source)
    }

    pub(crate) fn collect_garbage(&self) {
        let strategy = salsa::SweepStrategy::default()
            .discard_values()
            .sweep_all_revisions();

        self.query(ModuleTextQuery).sweep(strategy);
        self.query(TypecheckedModuleQuery).sweep(strategy);
        self.query(CoreExprQuery).sweep(strategy);
        self.query(CompiledModuleQuery).sweep(strategy);
    }
}

#[derive(Clone, Debug)]
pub struct DatabaseGlobal {
    pub id: Symbol,
    pub typ: ArcType,
    pub metadata: Arc<Metadata>,
    pub value: RootedValue<RootedThread>,
}

impl Eq for DatabaseGlobal {}

impl PartialEq for DatabaseGlobal {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl std::hash::Hash for DatabaseGlobal {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.id.hash(hasher)
    }
}

pub trait CompilationBase: salsa::Database {
    fn compiler(&self) -> &CompilerDatabase;
    fn thread(&self) -> &Thread;
    fn invalidate_module(&self, module: String, contents: &str);
    fn report_errors(&self, error: &mut Iterator<Item = Error>);
}

#[salsa::query_group(CompileStorage)]
pub trait Compilation: CompilationBase {
    #[salsa::input]
    fn compiler_settings(&self) -> Settings;

    #[salsa::input]
    fn module_states(&self) -> Arc<FnvMap<String, usize>>;

    #[salsa::dependencies]
    fn module_state(&self, module: String) -> usize;

    #[salsa::dependencies]
    fn module_text(&self, module: String) -> StdResult<Arc<Cow<'static, str>>, Error>;

    #[salsa::cycle(recover_cycle_typecheck)]
    #[salsa::volatile]
    fn typechecked_module(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> StdResult<TypecheckValue<Arc<SpannedExpr<Symbol>>>, Error>;

    #[salsa::cycle(recover_cycle)]
    #[salsa::volatile]
    fn core_expr(&self, module: String) -> StdResult<CoreExpr, Error>;

    #[salsa::cycle(recover_cycle)]
    fn compiled_module(&self, module: String) -> StdResult<CompiledModule, Error>;

    #[salsa::cycle(recover_cycle)]
    fn import(&self, module: String) -> StdResult<Expr<Symbol>, Error>;

    fn globals(&self) -> Arc<FnvMap<String, DatabaseGlobal>>;

    #[salsa::cycle(recover_cycle)]
    fn global(&self, name: String) -> Result<DatabaseGlobal>;
}

fn recover_cycle_typecheck<T>(
    db: &impl Compilation,
    cycle: &[String],
    module: &String,
    _: &Option<ArcType>,
) -> StdResult<T, Error> {
    recover_cycle(db, cycle, module)
}
fn recover_cycle<T>(
    _db: &impl Compilation,
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

fn module_state(db: &impl Compilation, module: String) -> usize {
    db.module_states().get(&module).cloned().unwrap_or_default()
}

fn module_text(db: &impl Compilation, module: String) -> StdResult<Arc<Cow<'static, str>>, Error> {
    // We just need to depend on updates to the state, we don't care what it is
    db.module_state(module.clone());

    let contents = if let Some(contents) = db.compiler().state().inline_modules.get(&module) {
        Arc::new(contents.to_string().into()) // FIXME Avoid copying
    } else {
        let mut filename = module.replace(".", "/");
        filename.push_str(".glu");

        Arc::new(
            crate::get_import(db.thread())
                .get_module_source(&module, &filename)
                .map_err(macros::Error::new)?,
        )
    };

    Ok(contents)
}

fn typechecked_module(
    db: &impl Compilation,
    module: String,
    expected_type: Option<ArcType>,
) -> StdResult<TypecheckValue<Arc<SpannedExpr<Symbol>>>, Error> {
    let text = db.module_text(module.clone())?;

    let thread = db.thread();
    text.typecheck_expected(
        &mut Compiler::new().module_compiler(db.compiler()),
        thread,
        &module,
        &text,
        expected_type.as_ref(),
    )
    .map(|value| value.map(Arc::new))
    .map_err(|(_, err)| err)
}

fn core_expr(db: &impl Compilation, module: String) -> StdResult<CoreExpr, Error> {
    let thread = db.thread();

    let value = db.typechecked_module(module.clone(), None)?;
    let settings = db.compiler_settings();

    let env = thread.get_env();
    Ok(core::with_translator(&env, |translator| {
        let expr = translator.translate_expr(&value.expr);

        debug!("Translation returned: {}", expr);

        if settings.optimize {
            core::optimize::optimize(&translator.allocator, &env, expr)
        } else {
            expr
        }
    }))
}

fn compiled_module(db: &impl Compilation, module: String) -> StdResult<CompiledModule, Error> {
    let core_expr = db.core_expr(module.clone())?;
    let settings = db.compiler_settings();

    let thread = db.thread();
    let env = thread.get_env();

    let compiler = Compiler::new();
    let mut compiler = compiler.module_compiler(db.compiler());

    let source = compiler
        .get_filemap(&module)
        .expect("Filemap does not exist");

    let name = Name::new(&module);
    let symbols = SymbolModule::new(
        String::from(AsRef::<str>::as_ref(name.module())),
        &mut compiler.symbols,
    );

    let mut compiler = vm::compiler::Compiler::new(
        &env,
        thread.global_env(),
        symbols,
        &source,
        module.clone(),
        settings.emit_debug_info,
    );

    let mut compiled_module = compiler.compile_expr(core_expr.expr())?;
    compiled_module.function.id = Symbol::from(module);

    Ok(compiled_module)
}

fn import(db: &impl Compilation, modulename: String) -> StdResult<Expr<Symbol>, Error> {
    let compiler = db.compiler();
    let thread = db.thread();

    let name = Symbol::from(if modulename.starts_with('@') {
        modulename.clone()
    } else {
        format!("@{}", modulename)
    });
    let result = crate::get_import(thread)
        .load_module(
            &mut Compiler::new().module_compiler(compiler),
            thread,
            &name,
        )
        .map_err(|(_, err)| err);

    compiler.collect_garbage();

    result?;

    Ok(Expr::Ident(TypedIdent::new(name)))
}

fn globals(db: &impl Compilation) -> Arc<FnvMap<String, DatabaseGlobal>> {
    let globals = db
        .module_states()
        .keys()
        .filter_map(|name| db.global(name.clone()).ok().map(|g| (name.clone(), g)))
        .collect();
    Arc::new(globals)
}

fn global(db: &impl Compilation, name: String) -> Result<DatabaseGlobal> {
    let vm = db.thread();

    let TypecheckValue { metadata, typ, .. } = db.typechecked_module(name.clone(), None)?;
    let mut compiled_module = db.compiled_module(name.clone())?;

    let module_id = Symbol::from(format!("@{}", name));
    compiled_module.function.id = module_id.clone();
    let closure = vm.global_env().new_global_thunk(&vm, compiled_module)?;

    let vm1 = vm.clone();
    let value = vm1.call_thunk_top(closure).wait()?;

    vm.set_global(
        module_id.clone(),
        typ.clone(),
        metadata.clone(),
        value.get_value(),
    )
    .unwrap();

    Ok(DatabaseGlobal {
        id: module_id,
        typ,
        metadata,
        value,
    })
}

impl CompilerEnv for DatabaseSnapshot {
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        self.global(id.definition_name().into())
            .ok()
            .map(|g| (Variable::UpVar(g.id.clone()), g.typ.clone()))
    }
}

impl KindEnv for DatabaseSnapshot {
    fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
        None
    }
}

impl TypeEnv for DatabaseSnapshot {
    type Type = ArcType;

    fn find_type(&self, id: &SymbolRef) -> Option<ArcType> {
        self.global(id.definition_name().into())
            .ok()
            .map(|g| g.typ.clone())
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        self.thread()
            .get_env()
            .find_type_info(id.definition_name())
            .ok()
    }
}

impl PrimitiveEnv for DatabaseSnapshot {
    fn get_bool(&self) -> ArcType {
        self.find_type_info("std.types.Bool")
            .expect("std.types.Bool")
            .into_type()
    }
}

impl MetadataEnv for DatabaseSnapshot {
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>> {
        self.thread()
            .get_env()
            .get_metadata(id.definition_name())
            .ok()
    }
}

impl VmEnv for DatabaseSnapshot {
    fn get_global(&self, name: &str) -> Option<vm::vm::Global> {
        self.global(name.into()).ok().map(|g| vm::vm::Global {
            id: g.id,
            metadata: g.metadata,
            typ: g.typ,
            value: g.value.get_value(),
        })
    }
}

impl DatabaseSnapshot {
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

    fn get_global<'s, 'n>(&'s self, name: &'n str) -> Option<(&'n Name, DatabaseGlobal)> {
        let mut module = Name::new(name.trim_start_matches('@'));
        let global;
        // Try to find a global by successively reducing the module path
        // Input: "x.y.z.w"
        // Test: "x.y.z"
        // Test: "x.y"
        // Test: "x"
        // Test: -> Error
        loop {
            if module.as_str() == "" {
                return None;
            }
            if let Ok(g) = self.global(module.as_str().into()) {
                global = g;
                break;
            }
            module = module.module();
        }
        let remaining_offset = ::std::cmp::min(name.len(), module.as_str().len() + 1); //Add 1 byte for the '.'
        let remaining_fields = Name::new(&name[remaining_offset..]);
        Some((remaining_fields, global))
    }

    pub fn get_binding(&self, name: &str) -> Result<(Value, ArcType)> {
        use crate::base::resolve;

        let (remaining_fields, global) = self
            .get_global(name)
            .ok_or_else(|| vm::Error::UndefinedBinding(name.into()))?;

        if remaining_fields.as_str().is_empty() {
            // No fields left
            return Ok((global.value.get_value(), global.typ.clone()));
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
        Ok((value.get_value(), typ))
    }

    pub fn get_metadata(&self, name_str: &str) -> Result<Arc<Metadata>> {
        eprintln!("META {}", name_str);
        self.get_metadata_(name_str)
            .ok_or_else(|| vm::Error::MetadataDoesNotExist(name_str.into()).into())
    }

    fn get_metadata_(&self, name_str: &str) -> Option<Arc<Metadata>> {
        let (remaining, global) = self.get_global(name_str)?;

        let mut metadata = &global.metadata;
        for field_name in remaining.components() {
            metadata = metadata.module.get(field_name)?
        }
        Some(metadata.clone())
    }
}
