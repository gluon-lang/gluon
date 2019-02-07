use std::{
    borrow::Cow,
    result::Result as StdResult,
    sync::{Arc, Mutex, MutexGuard},
};

use {
    base::{
        ast::{Expr, SpannedExpr, TypedIdent},
        error::Errors,
        fnv::FnvMap,
        pos::BytePos,
        symbol::Symbol,
        types::ArcType,
    },
    vm::{
        macros,
        thread::{RootedThread, Thread},
    },
};

use crate::{compiler_pipeline::*, Compiler, Error, Settings};

#[derive(Default)]
pub(crate) struct State {
    pub(crate) code_map: codespan::CodeMap,
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

    fn new_module(&self, module: String, contents: &str) {
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
}

pub(crate) trait CompilationBase: salsa::Database {
    fn compiler(&self) -> &CompilerDatabase;
    fn thread(&self) -> &Thread;
    fn new_module(&self, module: String, contents: &str);
    fn report_errors(&self, error: &mut Iterator<Item = Error>);
}

#[salsa::query_group(CompileStorage)]
pub(crate) trait Compilation: CompilationBase {
    #[salsa::input]
    fn compiler_settings(&self) -> Settings;

    #[salsa::input]
    fn module_states(&self) -> Arc<FnvMap<String, usize>>;

    fn module_state(&self, module: String) -> usize;

    fn module_text(&self, module: String) -> StdResult<Arc<Cow<'static, str>>, Error>;

    fn typechecked_module(
        &self,
        module: String,
        expected_type: Option<ArcType>,
    ) -> StdResult<TypecheckValue<Arc<SpannedExpr<Symbol>>>, Error>;

    fn compiled_module(
        &self,
        module: String,
    ) -> StdResult<CompileValue<Arc<SpannedExpr<Symbol>>>, Error>;

    #[salsa::cycle]
    fn import(&self, module: String) -> StdResult<Expr<Symbol>, Error>;
}

fn module_state(db: &impl Compilation, module: String) -> usize {
    db.module_states().get(&module).cloned().unwrap_or_default()
}

fn module_text(db: &impl Compilation, module: String) -> StdResult<Arc<Cow<'static, str>>, Error> {
    // We just need to depend on updates to the state, we don't care what it is
    db.module_state(module.clone());

    let mut filename = module.replace(".", "/");
    filename.push_str(".glu");

    let contents = Arc::new(
        crate::get_import(db.thread())
            .get_module_source(&module, &filename)
            .map_err(macros::Error::new)?,
    );
    db.new_module(module, &contents);
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

fn compiled_module(
    db: &impl Compilation,
    module: String,
) -> StdResult<CompileValue<Arc<SpannedExpr<Symbol>>>, Error> {
    let text = db.module_text(module.clone())?;
    let value = db.typechecked_module(module.clone(), None)?;

    let thread = db.thread();
    value.compile(
        &mut Compiler::new().module_compiler(db.compiler()),
        thread,
        &module,
        &text,
        None::<ArcType>,
    )
}

fn import(db: &impl Compilation, modulename: String) -> StdResult<Expr<Symbol>, Error> {
    let compiler = db.compiler();
    let thread = db.thread();

    let name = Symbol::from(if modulename.starts_with('@') {
        modulename.clone()
    } else {
        format!("@{}", modulename)
    });
    crate::get_import(thread)
        .load_module(
            &mut Compiler::new().module_compiler(compiler),
            thread,
            &name,
        )
        .map_err(|(_, err)| err)?;
    Ok(Expr::Ident(TypedIdent::new(name)))
}
