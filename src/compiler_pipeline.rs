//! Advanced compiler pipeline which ensures that the compilation phases are run in order even if
//! not the entire compilation procedure is needed.
//!
//! Each trait in this module represents a stage in a full compilation so to only run compilation
//! up until and including typechecking the `Typecheckable` trait can be used. Furthermore, if
//! compilation should continue at some point after typechecking has succeeded, the result of
//! typechecking (`TypecheckValue`) can be used as input to the next stage, ensuring that it is
//! difficult to forget a stage.

use std::{
    borrow::{Borrow, BorrowMut, Cow},
    result::Result as StdResult,
    sync::Arc,
};

#[cfg(feature = "serde")]
use either::Either;

#[cfg(feature = "serde")]
use crate::ThreadExt;

use crate::{
    base::{
        ast::{self, OwnedExpr, RootExpr, SpannedExpr, Typed},
        error::{Errors, InFile},
        fnv::FnvMap,
        metadata::Metadata,
        resolve,
        symbol::{Name, NameBuf, Symbol, SymbolModule},
        types::{ArcType, NullInterner, Type, TypeCache},
    },
    check::{metadata, rename},
    query::{env, AsyncCompilation, Compilation},
    vm::{
        compiler::CompiledModule,
        core::{self, interpreter, CoreExpr},
        macros::MacroExpander,
        thread::{RootedThread, RootedValue, Thread, ThreadInternal, VmRoot},
    },
    Error, ModuleCompiler, Result,
};

pub type BoxFuture<'vm, T, E> =
    std::pin::Pin<Box<dyn futures::Future<Output = StdResult<T, E>> + Send + 'vm>>;

pub type SalvageResult<T, E = Error> = crate::base::error::SalvageResult<T, E>;

pub use crate::base::error::Salvage;

impl<T> From<Salvage<T, Error>> for Error {
    fn from(s: Salvage<T, Error>) -> Self {
        s.error
    }
}

macro_rules! join_result {
    ($result: expr, |$f_arg: pat| $f_body: expr $(,)?) => {{
        let mut first_error = None;
        let $f_arg = match $result {
            Ok(x) => x,
            Err(Salvage {
                value: Some(expr),
                error,
            }) => {
                first_error = Some(error);
                expr
            }
            Err(Salvage { value: None, error }) => return Err(Salvage { value: None, error }),
        };

        match $f_body {
            Ok(value) => match first_error {
                Some(error) => {
                    return Err(Salvage {
                        value: Some(value),
                        error,
                    })
                }
                None => Ok(value),
            },
            Err(Salvage { value, error }) => Err(Salvage {
                value,
                error: Errors::from(
                    first_error
                        .into_iter()
                        .chain(Some(error))
                        .collect::<Vec<_>>(),
                )
                .into(),
            }),
        }
    }};
}

pub fn parse_expr_inner<'ast>(
    arena: ast::ArenaRef<'_, 'ast, Symbol>,
    compiler: &mut ModuleCompiler<'_, '_>,
    type_cache: &TypeCache<Symbol, ArcType>,
    file: &str,
    expr_str: &str,
) -> SalvageResult<SpannedExpr<'ast, Symbol>, InFile<parser::Error>> {
    let map = compiler.add_filemap(file, expr_str);
    parser::parse_partial_expr(
        arena,
        &mut SymbolModule::new(file.into(), &mut compiler.symbols),
        type_cache,
        &*map,
    )
    .map_err(|(value, error)| {
        info!("Parse error: {}", error);
        Salvage {
            value,
            error: InFile::new(compiler.code_map().clone(), error),
        }
    })
}

pub fn parse_expr(
    compiler: &mut ModuleCompiler<'_, '_>,
    type_cache: &TypeCache<Symbol, ArcType>,
    file: &str,
    expr_str: &str,
) -> SalvageResult<OwnedExpr<Symbol>, InFile<parser::Error>> {
    let result = {
        mk_ast_arena!(arena);

        parse_expr_inner((*arena).borrow(), compiler, type_cache, file, expr_str)
            .map(|expr| RootExpr::new(arena.clone(), arena.alloc(expr)))
            .map_err(|err| err.map(|expr| RootExpr::new(arena.clone(), arena.alloc(expr))))
    };
    result
        .map(|expr| expr.try_into_send().unwrap())
        .map_err(|err| err.map(|expr| expr.try_into_send().unwrap()))
}

/// Result type of successful macro expansion
#[derive(Debug)]
pub struct MacroValue<E> {
    pub expr: E,
}

#[async_trait::async_trait]
pub trait MacroExpandable {
    type Expr: BorrowMut<OwnedExpr<Symbol>>;

    async fn expand_macro(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>>;
}

#[async_trait::async_trait]
impl<'s> MacroExpandable for &'s str {
    type Expr = OwnedExpr<Symbol>;

    async fn expand_macro(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        join_result!(
            parse_expr(compiler, thread.global_env().type_cache(), file, self)
                .map_err(|err| err.err_into()),
            |expr| expr.expand_macro(compiler, thread, file, expr_str).await,
        )
    }
}

#[async_trait::async_trait]
impl<'s> MacroExpandable for &'s mut OwnedExpr<Symbol> {
    type Expr = &'s mut OwnedExpr<Symbol>;

    async fn expand_macro(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        if compiler.compiler_settings().implicit_prelude
            && !expr_str.starts_with("//@NO-IMPLICIT-PRELUDE")
        {
            let (arena, expr) = self.arena_expr();
            compiler.include_implicit_prelude(
                arena.borrow(),
                thread.global_env().type_cache(),
                file,
                expr,
            );
        }

        let result = {
            struct Forker<'a, 'b, 'c>(
                salsa::Forker<&'b mut salsa::OwnedDb<'a, dyn Compilation + 'c>>,
            );
            impl vm::macros::MacroUserdata for Forker<'_, '_, '_> {
                fn fork(&self, thread: RootedThread) -> Box<dyn std::any::Any> {
                    Box::new(self.0.db.compiler().fork(self.0.state.clone(), thread))
                }
            }
            let mut forker = Forker(salsa::forker(&mut compiler.database));

            let spawner = thread.spawner();

            let (arena, expr) = self.arena_expr();
            let mut macros = MacroExpander::new(thread, &mut forker, spawner);
            macros.run(&mut compiler.symbols, arena, expr).await;
            macros.finish()
        };
        let value = MacroValue { expr: self };
        if let Err(errors) = result {
            Err(Salvage {
                value: Some(value),
                error: InFile::new(compiler.code_map().clone(), errors).into(),
            })
        } else {
            Ok(value)
        }
    }
}

#[async_trait::async_trait]
impl MacroExpandable for OwnedExpr<Symbol> {
    type Expr = OwnedExpr<Symbol>;

    async fn expand_macro(
        mut self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        let result = (&mut self)
            .expand_macro(compiler, thread, file, expr_str)
            .await
            .map(|_| ())
            .map_err(|err| err.error);

        let value = MacroValue { expr: self };
        match result {
            Ok(()) => Ok(value),
            Err(error) => Err(Salvage {
                value: Some(value),
                error,
            }),
        }
    }
}

pub struct Renamed<E> {
    pub expr: E,
}

#[async_trait::async_trait]
pub trait Renameable: Sized {
    type Expr: BorrowMut<OwnedExpr<Symbol>>;

    async fn rename(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<Renamed<Self::Expr>>;
}

#[async_trait::async_trait]
impl<T> Renameable for T
where
    T: MacroExpandable + Send,
    T::Expr: Send,
{
    type Expr = T::Expr;

    async fn rename(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<Renamed<Self::Expr>> {
        join_result!(
            self.expand_macro(compiler, thread, file, expr_str).await,
            |mac| mac.rename(compiler, thread, file, expr_str).await,
        )
    }
}

#[async_trait::async_trait]
impl<E> Renameable for MacroValue<E>
where
    E: BorrowMut<OwnedExpr<Symbol>> + Send,
{
    type Expr = E;

    async fn rename(
        mut self,
        compiler: &mut ModuleCompiler<'_, '_>,
        _thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<Renamed<Self::Expr>> {
        let source = compiler.get_or_insert_filemap(file, expr_str);
        let mut symbols = SymbolModule::new(String::from(file), &mut compiler.symbols);

        self.expr
            .borrow_mut()
            .with_arena(|arena, expr| rename::rename(&*source, &mut symbols, arena.borrow(), expr));
        Ok(Renamed { expr: self.expr })
    }
}

pub struct WithMetadata<E> {
    pub expr: E,
    pub metadata_map: FnvMap<Symbol, Arc<Metadata>>,
    pub metadata: Arc<Metadata>,
}

#[async_trait::async_trait]
pub trait MetadataExtractable: Sized {
    type Expr: BorrowMut<OwnedExpr<Symbol>>;

    async fn extract_metadata(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<WithMetadata<Self::Expr>>;
}

#[async_trait::async_trait]
impl<T> MetadataExtractable for T
where
    T: Renameable + Send,
    T::Expr: Send,
{
    type Expr = T::Expr;

    async fn extract_metadata(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<WithMetadata<Self::Expr>> {
        join_result!(
            self.rename(compiler, thread, file, expr_str).await,
            |renamed| renamed
                .extract_metadata(compiler, thread, file, expr_str)
                .await,
        )
    }
}

#[async_trait::async_trait]
impl<E> MetadataExtractable for Renamed<E>
where
    E: BorrowMut<OwnedExpr<Symbol>> + Send,
{
    type Expr = E;

    async fn extract_metadata(
        mut self,
        compiler: &mut ModuleCompiler<'_, '_>,
        _thread: &Thread,
        _file: &str,
        _expr_str: &str,
    ) -> SalvageResult<WithMetadata<Self::Expr>> {
        let env = env(&*compiler.database);
        let (metadata, metadata_map) = metadata::metadata(&env, self.expr.borrow_mut().expr_mut());
        Ok(WithMetadata {
            expr: self.expr,
            metadata,
            metadata_map,
        })
    }
}

#[derive(Debug)]
pub struct InfixReparsed<E> {
    pub expr: E,
    pub metadata_map: FnvMap<Symbol, Arc<Metadata>>,
    pub metadata: Arc<Metadata>,
}

#[async_trait::async_trait]
pub trait InfixReparseable: Sized {
    type Expr: BorrowMut<OwnedExpr<Symbol>>;

    async fn reparse_infix(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<InfixReparsed<Self::Expr>>;
}

#[async_trait::async_trait]
impl<T> InfixReparseable for T
where
    T: MetadataExtractable + Send,
    T::Expr: Send,
{
    type Expr = T::Expr;

    async fn reparse_infix(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<InfixReparsed<Self::Expr>> {
        join_result!(
            self.extract_metadata(compiler, thread, file, expr_str)
                .await,
            |expr| expr.reparse_infix(compiler, thread, file, expr_str).await,
        )
    }
}

#[async_trait::async_trait]
impl<E> InfixReparseable for WithMetadata<E>
where
    E: BorrowMut<OwnedExpr<Symbol>> + Send,
{
    type Expr = E;

    async fn reparse_infix(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        _thread: &Thread,
        _file: &str,
        _expr_str: &str,
    ) -> SalvageResult<InfixReparsed<Self::Expr>> {
        use crate::parser::reparse_infix;

        let WithMetadata {
            mut expr,
            metadata,
            metadata_map,
        } = self;
        match expr.borrow_mut().with_arena(|arena, expr| {
            reparse_infix(arena.borrow(), &metadata_map, &compiler.symbols, expr)
        }) {
            Ok(()) => Ok(InfixReparsed {
                expr,
                metadata,
                metadata_map,
            }),
            Err(err) => Err(Salvage {
                value: Some(InfixReparsed {
                    expr,
                    metadata,
                    metadata_map,
                }),
                error: InFile::new(compiler.code_map().clone(), err).into(),
            }),
        }
    }
}

/// Result type of successful typechecking
#[derive(Eq, PartialEq, Clone, Debug)]
pub struct TypecheckValue<E> {
    pub expr: E,
    pub typ: ArcType,
    pub metadata_map: FnvMap<Symbol, Arc<Metadata>>,
    pub metadata: Arc<Metadata>,
}

impl<E> TypecheckValue<E> {
    pub fn map<F>(self, f: impl FnOnce(E) -> F) -> TypecheckValue<F> {
        let TypecheckValue {
            expr,
            typ,
            metadata_map,
            metadata,
        } = self;
        TypecheckValue {
            expr: f(expr),
            typ,
            metadata_map,
            metadata,
        }
    }
}

#[async_trait::async_trait]
pub trait Typecheckable: Sized {
    type Expr: BorrowMut<OwnedExpr<Symbol>>;

    async fn typecheck(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<TypecheckValue<Self::Expr>> {
        self.typecheck_expected(compiler, thread, file, expr_str, None)
            .await
    }
    async fn typecheck_expected(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> SalvageResult<TypecheckValue<Self::Expr>>;
}

#[async_trait::async_trait]
impl<T> Typecheckable for T
where
    T: InfixReparseable + Send,
    T::Expr: Send,
{
    type Expr = T::Expr;

    async fn typecheck_expected(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> SalvageResult<TypecheckValue<Self::Expr>> {
        join_result!(
            self.reparse_infix(compiler, thread, file, expr_str).await,
            |expr| expr
                .typecheck_expected(compiler, thread, file, expr_str, expected_type)
                .await,
        )
    }
}

fn typecheck_expr(
    expr: &mut OwnedExpr<Symbol>,
    compiler: &mut ModuleCompiler<'_, '_>,
    thread: &Thread,
    file: &str,
    expected_type: Option<&ArcType>,
    metadata_map: &mut FnvMap<Symbol, Arc<Metadata>>,
) -> Result<ArcType> {
    use crate::check::typecheck::Typecheck;
    let env = env(&*compiler.database);
    let (arena, expr) = expr.arena_expr();
    let mut tc = Typecheck::new(
        file.into(),
        &mut compiler.symbols,
        &env,
        &thread.global_env().type_cache(),
        metadata_map,
        arena.borrow(),
    );

    tc.typecheck_expr_expected(expr, expected_type)
        .map_err(|err| InFile::new(compiler.database.state().code_map.clone(), err).into())
}

#[async_trait::async_trait]
impl<E> Typecheckable for InfixReparsed<E>
where
    E: BorrowMut<OwnedExpr<Symbol>> + Send,
{
    type Expr = E;

    async fn typecheck_expected(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        _expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> SalvageResult<TypecheckValue<Self::Expr>> {
        trace!("Typecheck: {}", file);

        let InfixReparsed {
            mut expr,
            mut metadata_map,
            metadata,
        } = self;

        let typ = match typecheck_expr(
            expr.borrow_mut(),
            compiler,
            thread,
            file,
            expected_type,
            &mut metadata_map,
        ) {
            Ok(typ) => typ,
            Err(error) => {
                let typ = expr
                    .borrow_mut()
                    .expr()
                    .try_type_of(&env(&*compiler.database))
                    .unwrap_or_else(|_| thread.global_env().type_cache().error());
                return Err(Salvage {
                    value: Some(TypecheckValue {
                        typ,
                        expr,
                        metadata_map,
                        metadata,
                    }),
                    error,
                });
            }
        };

        // Some metadata requires typechecking so recompute it if full metadata is required
        let (metadata, metadata_map) = if compiler.compiler_settings().full_metadata {
            let env = env(&*compiler.database);
            metadata::metadata(&env, expr.borrow_mut().expr_mut())
        } else {
            (metadata, metadata_map)
        };

        Ok(TypecheckValue {
            expr,
            typ,
            metadata_map,
            metadata,
        })
    }
}

/// Result of successful compilation
#[derive(Debug)]
pub struct CompileValue<E> {
    pub expr: E,
    pub core_expr: interpreter::Global<CoreExpr>,
    pub typ: ArcType,
    pub metadata: Arc<Metadata>,
    pub module: CompiledModule,
}

impl<E> CompileValue<E> {
    pub fn map<F>(self, f: impl FnOnce(E) -> F) -> CompileValue<F> {
        let CompileValue {
            expr,
            core_expr,
            typ,
            metadata,
            module,
        } = self;
        CompileValue {
            expr: f(expr),
            core_expr,
            typ,
            metadata,
            module,
        }
    }
}

#[async_trait::async_trait]
pub trait Compileable<Extra> {
    type Expr;

    async fn compile(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        arg: Extra,
    ) -> Result<CompileValue<Self::Expr>>
    where
        Extra: 'async_trait;
}

#[async_trait::async_trait]
impl<'a, 'b, T> Compileable<Option<&'b ArcType>> for T
where
    T: Typecheckable + Send,
    T::Expr: Send + Sync,
{
    type Expr = T::Expr;

    async fn compile(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&'b ArcType>,
    ) -> Result<CompileValue<Self::Expr>> {
        let tc_value = self
            .typecheck_expected(compiler, thread, file, expr_str, expected_type)
            .await?;
        tc_value.compile(compiler, thread, file, expr_str, ()).await
    }
}

#[async_trait::async_trait]
impl<E, Extra> Compileable<Extra> for TypecheckValue<E>
where
    E: Borrow<OwnedExpr<Symbol>> + Send + Sync,
    Extra: Send,
{
    type Expr = E;

    async fn compile(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        filename: &str,
        expr_str: &str,
        extra: Extra,
    ) -> Result<CompileValue<Self::Expr>>
    where
        Extra: 'async_trait,
    {
        (&self)
            .compile(compiler, thread, filename, expr_str, extra)
            .await
            .map(|value| value.map(|_| ()))
            .map(
                |CompileValue {
                     typ,
                     metadata,
                     module,
                     core_expr,
                     ..
                 }| CompileValue {
                    expr: self.expr,
                    core_expr,
                    typ,
                    metadata,
                    module,
                },
            )
    }
}

#[async_trait::async_trait]
impl<'e, E, Extra> Compileable<Extra> for &'e TypecheckValue<E>
where
    E: Borrow<OwnedExpr<Symbol>> + Send + Sync,
    Extra: Send,
{
    type Expr = &'e E;

    async fn compile(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        thread: &Thread,
        filename: &str,
        _expr_str: &str,
        _: Extra,
    ) -> Result<CompileValue<Self::Expr>>
    where
        Extra: 'async_trait,
    {
        use crate::vm::compiler::Compiler;

        info!("Compile `{}`", filename);

        let settings = compiler.compiler_settings();

        let core_expr;

        let mut module = {
            core_expr = {
                let env = env(&*compiler.database);
                core::with_translator(&env, |translator| {
                    let expr = translator.translate_expr(self.expr.borrow().expr());

                    debug!("Translation returned: {}", expr);

                    if settings.optimize {
                        core::optimize::optimize(&translator.allocator, &env, expr)
                    } else {
                        interpreter::Global {
                            value: core::freeze_expr(&translator.allocator, expr),
                            info: Default::default(),
                        }
                    }
                })
            };

            debug!("Optimization returned: {}", core_expr);

            let source = compiler
                .get_filemap(filename)
                .expect("Filemap does not exist");

            let name = Name::new(filename);
            let name = NameBuf::from(name.module());
            let symbols = SymbolModule::new(
                String::from(AsRef::<str>::as_ref(&name)),
                &mut compiler.symbols,
            );

            let env = env(&*compiler.database);
            let mut compiler = Compiler::new(
                &env,
                thread.global_env(),
                symbols,
                &source,
                filename.to_string(),
                settings.emit_debug_info,
            );
            compiler.compile_expr(core_expr.value.expr())?
        };
        module.function.id = Symbol::from(filename);
        Ok(CompileValue {
            expr: &self.expr,
            core_expr,
            typ: self.typ.clone(),
            metadata: self.metadata.clone(),
            module,
        })
    }
}

/// Result of successful execution
pub struct ExecuteValue<T, E>
where
    T: for<'a> VmRoot<'a>,
{
    pub id: Symbol,
    pub expr: E,
    pub typ: ArcType,
    pub metadata: Arc<Metadata>,
    pub value: RootedValue<T>,
}

#[async_trait::async_trait]
pub trait Executable<'vm, Extra> {
    type Expr;

    async fn run_expr<T>(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        vm: T,
        name: &str,
        expr_str: &str,
        arg: Extra,
    ) -> Result<ExecuteValue<RootedThread, Self::Expr>>
    where
        T: Send + Sync + VmRoot<'vm>,
        Extra: 'async_trait,
        'vm: 'async_trait;

    async fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        vm: T,
        filename: &str,
        expr_str: &str,
        arg: Extra,
    ) -> Result<()>
    where
        T: Send + Sync + VmRoot<'vm>,
        Extra: 'async_trait,
        'vm: 'async_trait;
}

#[async_trait::async_trait]
impl<'vm, C, Extra> Executable<'vm, Extra> for C
where
    C: Compileable<Extra> + Send,
    C::Expr: Send + 'vm,
    Extra: Send,
{
    type Expr = C::Expr;

    async fn run_expr<T>(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        vm: T,
        name: &str,
        expr_str: &str,
        arg: Extra,
    ) -> Result<ExecuteValue<RootedThread, Self::Expr>>
    where
        T: Send + Sync + VmRoot<'vm>,
        'vm: 'async_trait,
        Extra: 'async_trait,
    {
        match self.compile(compiler, &vm, name, expr_str, arg).await {
            Ok(v) => v.run_expr(compiler, vm, name, expr_str, ()).await,
            Err(err) => Err(err),
        }
    }

    async fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        vm: T,
        filename: &str,
        expr_str: &str,
        arg: Extra,
    ) -> Result<()>
    where
        T: Send + Sync + VmRoot<'vm>,
        Extra: 'async_trait,
        'vm: 'async_trait,
    {
        match self.compile(compiler, &vm, filename, expr_str, arg).await {
            Ok(v) => v.load_script(compiler, vm, filename, expr_str, ()).await,
            Err(err) => Err(err),
        }
    }
}

#[async_trait::async_trait]
impl<'vm, E> Executable<'vm, ()> for CompileValue<E>
where
    E: Send + 'vm,
{
    type Expr = E;

    async fn run_expr<T>(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        vm: T,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> Result<ExecuteValue<RootedThread, Self::Expr>>
    where
        T: Send + Sync + VmRoot<'vm>,
        'vm: 'async_trait,
    {
        let CompileValue {
            expr,
            core_expr: _,
            typ,
            mut module,
            metadata,
        } = self;
        let run_io = compiler.database.compiler_settings().run_io;
        let module_id = Symbol::from(format!("@{}", name));
        module.function.id = module_id.clone();
        let closure = vm.global_env().new_global_thunk(&vm, module)?;

        let vm1 = vm.clone();
        let value = vm1.call_thunk_top(&closure).await.map_err(Error::from)?;
        let v = ExecuteValue {
            id: module_id,
            expr,
            typ,
            value,
            metadata,
        };
        if run_io {
            crate::compiler_pipeline::run_io(vm, v).await
        } else {
            Ok(v)
        }
    }

    async fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler<'_, '_>,
        _vm: T,
        filename: &str,
        expr_str: &str,
        _: (),
    ) -> Result<()>
    where
        T: Send + Sync + VmRoot<'vm>,
        'vm: 'async_trait,
    {
        let filename = filename.to_string();

        compiler
            .state()
            .inline_modules
            .insert(filename.clone(), Arc::new(Cow::Owned(expr_str.into())));

        compiler.database.import(filename.into()).await?;

        Ok(())
    }
}

#[cfg(feature = "serde")]
pub struct Precompiled<D>(pub D);

#[cfg_attr(
    feature = "serde_derive_state",
    derive(DeserializeState, SerializeState)
)]
#[cfg_attr(
    feature = "serde_derive_state",
    serde(
        deserialize_state = "::vm::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive_state",
    serde(serialize_state = "::vm::serialization::SeSeed")
)]
pub struct Module {
    #[cfg_attr(
        feature = "serde_derive_state",
        serde(state_with = "::vm::serialization::borrow")
    )]
    pub typ: ArcType,

    pub metadata: Arc<Metadata>,

    #[cfg_attr(feature = "serde_derive_state", serde(state))]
    pub module: CompiledModule,
}

#[cfg(feature = "serde")]
#[async_trait::async_trait]
impl<'vm, D> Executable<'vm, ()> for Precompiled<D>
where
    D: crate::serde::Deserializer<'vm> + Send,
{
    type Expr = ();

    async fn run_expr<T>(
        self,
        _compiler: &mut ModuleCompiler<'_, '_>,
        vm: T,
        filename: &str,
        _expr_str: &str,
        _: (),
    ) -> Result<ExecuteValue<RootedThread, Self::Expr>>
    where
        T: Send + Sync + VmRoot<'vm>,
        'vm: 'async_trait,
    {
        use crate::vm::serialization::DeSeed;

        let module: Module = DeSeed::new(&vm, &mut vm.current_context())
            .deserialize(self.0)
            .map_err(|err| err.to_string())?;
        let module_id = module.module.function.id.clone();
        if filename != module_id.as_str() {
            return Err(format!("filenames do not match `{}` != `{}`", filename, module_id).into());
        }

        let typ = module.typ;
        let metadata = module.metadata;
        let closure = vm.global_env().new_global_thunk(&vm, module.module)?;
        vm.call_thunk_top(&closure)
            .await
            .map(move |value| ExecuteValue {
                id: module_id,
                expr: (),
                typ: typ,
                metadata,
                value,
            })
            .map_err(Error::from)
    }

    async fn load_script<T>(
        self,
        _compiler: &mut ModuleCompiler<'_, '_>,
        vm: T,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> Result<()>
    where
        T: Send + Sync + VmRoot<'vm>,
        'vm: 'async_trait,
    {
        use crate::vm::{internal::Global, serialization::DeSeed};

        let Global {
            metadata,
            typ,
            value,
            id: _,
        } = DeSeed::new(&vm, &mut vm.current_context())
            .deserialize(self.0)
            .map_err(|err| err.to_string())?;
        vm.get_database_mut()
            .set_global(name, typ, metadata.clone(), &value);
        info!("Loaded module `{}`", name);
        Ok(())
    }
}

#[cfg(feature = "serde")]
pub async fn compile_to<S, T, E>(
    self_: T,
    compiler: &mut ModuleCompiler<'_, '_>,
    thread: &Thread,
    file: &str,
    expr_str: &str,
    arg: E,
    serializer: S,
) -> StdResult<S::Ok, Either<Error, S::Error>>
where
    S: crate::serde::Serializer,
    S::Error: 'static,
    T: Compileable<E>,
{
    use crate::serde::ser::SerializeState;
    use crate::vm::serialization::SeSeed;
    let CompileValue {
        expr: _,
        core_expr: _,
        typ,
        metadata,
        module,
    } = self_
        .compile(compiler, thread, file, expr_str, arg)
        .await
        .map_err(Error::from)
        .map_err(Either::Left)?;
    let module = Module {
        typ,
        metadata,
        module,
    };
    module
        .serialize_state(serializer, &SeSeed::new())
        .map_err(Either::Right)
}

pub async fn run_io<'vm, T, E>(
    vm: T,
    v: ExecuteValue<RootedThread, E>,
) -> Result<ExecuteValue<RootedThread, E>>
where
    E: Send + 'vm,
    T: Send + VmRoot<'vm>,
{
    use crate::check::check_signature;
    use crate::vm::api::generic::A;
    use crate::vm::api::{VmType, IO};

    if check_signature(&vm.get_env(), &v.typ, &IO::<A>::make_forall_type(&vm)) {
        let ExecuteValue {
            id,
            expr,
            typ,
            value,
            metadata,
        } = v;

        let vm1 = vm.clone();
        vm1.execute_io_top(value.get_variant())
            .await
            .map(move |value| {
                // The type of the new value will be `a` instead of `IO a`
                let actual = resolve::remove_aliases_cow(&vm.get_env(), &mut NullInterner, &typ);
                let actual = match **actual {
                    Type::App(_, ref arg) => arg[0].clone(),
                    _ => ice!("ICE: Expected IO type found: `{}`", actual),
                };
                ExecuteValue {
                    id,
                    expr,
                    value,
                    metadata,
                    typ: actual,
                }
            })
            .map_err(Error::from)
    } else {
        Ok(v)
    }
}
