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
use futures::prelude::*;
use salsa::ParallelDatabase;

use crate::{
    base::{
        ast::{SpannedExpr, Typed},
        error::{Errors, InFile},
        fnv::FnvMap,
        metadata::Metadata,
        resolve,
        symbol::{Name, NameBuf, Symbol, SymbolModule},
        types::{ArcType, NullInterner, Type, TypeCache},
    },
    check::{metadata, rename},
    query::{Compilation, CompilerDatabase},
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

pub type SalvageResult<T, E = Error> = StdResult<T, (Option<T>, E)>;

fn call<T, U>(v: T, f: impl FnOnce(T) -> U) -> U {
    f(v)
}

macro_rules! join_result {
    ($result: expr, $f: expr, $join: expr $(,)?) => {{
        let mut first_error = None;
        let mut x = match $result {
            Ok(x) => x,
            Err((Some(expr), err)) => {
                first_error = Some(err);
                expr
            }
            Err((None, err)) => return Err((None, err)),
        };
        let result = call(&mut x, $f)
            .await
            .map(|_| ())
            .map_err(|(value, err)| (value.map(|_| ()), err));
        if let Err((value, err)) = result {
            return Err((
                value.map(|_| call(x, $join)),
                if first_error.is_some() {
                    Errors::from(first_error.into_iter().chain(Some(err)).collect::<Vec<_>>())
                        .into()
                } else {
                    err
                },
            ));
        }
        let v = call(x, $join);
        match first_error {
            Some(err) => Err((Some(v), err)),
            None => Ok(v),
        }
    }};
}

pub fn parse_expr(
    compiler: &mut ModuleCompiler<'_>,
    type_cache: &TypeCache<Symbol, ArcType>,
    file: &str,
    expr_str: &str,
) -> SalvageResult<SpannedExpr<Symbol>, InFile<parser::Error>> {
    let map = compiler.add_filemap(file, expr_str);

    Ok(parser::parse_partial_expr(
        &mut SymbolModule::new(file.into(), &mut compiler.symbols),
        type_cache,
        &*map,
    )
    .map_err(|(expr, err)| {
        info!("Parse error: {}", err);
        (expr, InFile::new(compiler.code_map().clone(), err))
    })?)
}

/// Result type of successful macro expansion
#[derive(Debug)]
pub struct MacroValue<E> {
    pub expr: E,
}

#[async_trait::async_trait]
pub trait MacroExpandable {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    async fn expand_macro(
        self,
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>>;
}

#[async_trait::async_trait]
impl<'s> MacroExpandable for &'s str {
    type Expr = SpannedExpr<Symbol>;

    async fn expand_macro(
        self,
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        join_result!(
            parse_expr(compiler, thread.global_env().type_cache(), file, self)
                .map_err(|(x, err)| (x, err.into())),
            |expr| {
                async move {
                    expr.expand_macro(compiler, thread, file, expr_str)
                        .map_ok(|_| ())
                        .map_err(|(opt, err)| (opt.map(|_| ()), err))
                        .await
                }
            },
            |expr| MacroValue { expr },
        )
    }
}

#[async_trait::async_trait]
impl<'s> MacroExpandable for &'s mut SpannedExpr<Symbol> {
    type Expr = &'s mut SpannedExpr<Symbol>;

    async fn expand_macro(
        self,
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        if compiler.compiler_settings().implicit_prelude
            && !expr_str.starts_with("//@NO-IMPLICIT-PRELUDE")
        {
            compiler.include_implicit_prelude(thread.global_env().type_cache(), file, self);
        }

        let result = {
            struct Forker<'a>(salsa::Forker<'a, CompilerDatabase>);
            impl vm::macros::MacroUserdata for Forker<'_> {
                fn fork(&self, thread: RootedThread) -> Box<dyn std::any::Any> {
                    Box::new(CompilerDatabase::fork(
                        self.0.db,
                        self.0.state.clone(),
                        thread,
                    ))
                }
            }
            let mut forker = Forker(compiler.database.forker());

            let spawner = thread.spawner();

            let mut macros = MacroExpander::new(thread, &mut forker, spawner);
            macros.run(&mut compiler.symbols, self).await;
            macros.finish()
        };
        let value = MacroValue { expr: self };
        if let Err(errors) = result {
            Err((
                Some(value),
                InFile::new(compiler.code_map().clone(), errors).into(),
            ))
        } else {
            Ok(value)
        }
    }
}

#[async_trait::async_trait]
impl MacroExpandable for SpannedExpr<Symbol> {
    type Expr = SpannedExpr<Symbol>;

    async fn expand_macro(
        mut self,
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        let result = (&mut self)
            .expand_macro(compiler, thread, file, expr_str)
            .await
            .map(|_| ())
            .map_err(|(_, err)| err);

        let value = MacroValue { expr: self };
        match result {
            Ok(()) => Ok(value),
            Err(err) => Err((Some(value), err)),
        }
    }
}

pub struct Renamed<E> {
    pub expr: E,
}

#[async_trait::async_trait]
pub trait Renameable: Sized {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    async fn rename(
        self,
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<Renamed<Self::Expr>> {
        join_result!(
            self.expand_macro(compiler, thread, file, expr_str).await,
            |MacroValue { expr }| {
                MacroValue {
                    expr: expr.borrow_mut(),
                }
                .rename(compiler, thread, file, expr_str)
                .map_ok(|_| ())
                .map_err(|(opt, err)| (opt.map(|_| ()), err))
            },
            |MacroValue { expr }| Renamed { expr },
        )
    }
}

#[async_trait::async_trait]
impl<E> Renameable for MacroValue<E>
where
    E: BorrowMut<SpannedExpr<Symbol>> + Send,
{
    type Expr = E;

    async fn rename(
        mut self,
        compiler: &mut ModuleCompiler<'_>,
        _thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<Renamed<Self::Expr>> {
        let source = compiler.get_or_insert_filemap(file, expr_str);
        let mut symbols = SymbolModule::new(String::from(file), &mut compiler.symbols);
        rename::rename(&*source, &mut symbols, &mut self.expr.borrow_mut());
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
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    async fn extract_metadata(
        self,
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<WithMetadata<Self::Expr>> {
        let mut macro_error = None;
        let expr = match self.rename(compiler, thread, file, expr_str).await {
            Ok(expr) => expr,
            Err((Some(expr), err)) => {
                macro_error = Some(err);
                expr
            }
            Err((None, err)) => return Err((None, err)),
        };
        match expr
            .extract_metadata(compiler, thread, file, expr_str)
            .await
        {
            Ok(value) => match macro_error {
                Some(err) => return Err((Some(value), err)),
                None => Ok(value),
            },
            Err((opt, err)) => Err((
                opt,
                Errors::from(macro_error.into_iter().chain(Some(err)).collect::<Vec<_>>()).into(),
            )),
        }
    }
}

#[async_trait::async_trait]
impl<E> MetadataExtractable for Renamed<E>
where
    E: BorrowMut<SpannedExpr<Symbol>> + Send,
{
    type Expr = E;

    async fn extract_metadata(
        mut self,
        compiler: &mut ModuleCompiler<'_>,
        _thread: &Thread,
        _file: &str,
        _expr_str: &str,
    ) -> SalvageResult<WithMetadata<Self::Expr>> {
        let env = &*compiler.database;
        let (metadata, metadata_map) = metadata::metadata(env, self.expr.borrow_mut());
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
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    async fn reparse_infix(
        self,
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<InfixReparsed<Self::Expr>> {
        let mut macro_error = None;
        let expr = match self
            .extract_metadata(compiler, thread, file, expr_str)
            .await
        {
            Ok(expr) => expr,
            Err((Some(expr), err)) => {
                macro_error = Some(err);
                expr
            }
            Err((None, err)) => return Err((None, err)),
        };
        match expr.reparse_infix(compiler, thread, file, expr_str).await {
            Ok(value) => match macro_error {
                Some(err) => return Err((Some(value), err)),
                None => Ok(value),
            },
            Err((opt, err)) => Err((
                opt,
                Errors::from(macro_error.into_iter().chain(Some(err)).collect::<Vec<_>>()).into(),
            )),
        }
    }
}

#[async_trait::async_trait]
impl<E> InfixReparseable for WithMetadata<E>
where
    E: BorrowMut<SpannedExpr<Symbol>> + Send,
{
    type Expr = E;

    async fn reparse_infix(
        self,
        compiler: &mut ModuleCompiler<'_>,
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
        match reparse_infix(&metadata_map, &compiler.symbols, expr.borrow_mut()) {
            Ok(()) => Ok(InfixReparsed {
                expr,
                metadata,
                metadata_map,
            }),
            Err(err) => Err((
                Some(InfixReparsed {
                    expr,
                    metadata,
                    metadata_map,
                }),
                InFile::new(compiler.code_map().clone(), err).into(),
            )),
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
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    async fn typecheck(
        self,
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<TypecheckValue<Self::Expr>> {
        self.typecheck_expected(compiler, thread, file, expr_str, None)
            .await
    }
    async fn typecheck_expected(
        self,
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> SalvageResult<TypecheckValue<Self::Expr>> {
        let mut macro_error = None;
        let expr = match self.reparse_infix(compiler, thread, file, expr_str).await {
            Ok(expr) => expr,
            Err((Some(expr), err)) => {
                macro_error = Some(err);
                expr
            }
            Err((None, err)) => return Err((None, err)),
        };
        match expr
            .typecheck_expected(compiler, thread, file, expr_str, expected_type)
            .await
        {
            Ok(value) => match macro_error {
                Some(err) => return Err((Some(value), err)),
                None => Ok(value),
            },
            Err((opt, err)) => Err((
                opt,
                Errors::from(macro_error.into_iter().chain(Some(err)).collect::<Vec<_>>()).into(),
            )),
        }
    }
}

fn typecheck_expr(
    expr: &mut SpannedExpr<Symbol>,
    compiler: &mut ModuleCompiler<'_>,
    thread: &Thread,
    file: &str,
    expected_type: Option<&ArcType>,
    metadata_map: &mut FnvMap<Symbol, Arc<Metadata>>,
) -> Result<ArcType> {
    use crate::check::typecheck::Typecheck;
    let env = &*compiler.database;
    let mut tc = Typecheck::new(
        file.into(),
        &mut compiler.symbols,
        &*env,
        &thread.global_env().type_cache(),
        metadata_map,
    );

    tc.typecheck_expr_expected(expr.borrow_mut(), expected_type)
        .map_err(|err| InFile::new(compiler.database.state().code_map.clone(), err).into())
}

#[async_trait::async_trait]
impl<E> Typecheckable for InfixReparsed<E>
where
    E: BorrowMut<SpannedExpr<Symbol>> + Send,
{
    type Expr = E;

    async fn typecheck_expected(
        self,
        compiler: &mut ModuleCompiler<'_>,
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
            Err(err) => {
                return Err((
                    Some(TypecheckValue {
                        typ: expr
                            .borrow_mut()
                            .try_type_of(&*compiler.database)
                            .unwrap_or_else(|_| thread.global_env().type_cache().error()),
                        expr,
                        metadata_map,
                        metadata,
                    }),
                    err,
                ))
            }
        };

        // Some metadata requires typechecking so recompute it if full metadata is required
        let (metadata, metadata_map) = if compiler.compiler_settings().full_metadata {
            let env = &*compiler.database;
            metadata::metadata(&*env, expr.borrow_mut())
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
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&'b ArcType>,
    ) -> Result<CompileValue<Self::Expr>> {
        let tc_value = self
            .typecheck_expected(compiler, thread, file, expr_str, expected_type)
            .await
            .map_err(|(_, err)| err)?;
        tc_value.compile(compiler, thread, file, expr_str, ()).await
    }
}

#[async_trait::async_trait]
impl<E, Extra> Compileable<Extra> for TypecheckValue<E>
where
    E: Borrow<SpannedExpr<Symbol>> + Send + Sync,
    Extra: Send,
{
    type Expr = E;

    async fn compile(
        self,
        compiler: &mut ModuleCompiler<'_>,
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
    E: Borrow<SpannedExpr<Symbol>> + Send + Sync,
    Extra: Send,
{
    type Expr = &'e E;

    async fn compile(
        self,
        compiler: &mut ModuleCompiler<'_>,
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
            let env = &*compiler.database;

            core_expr = core::with_translator(&*env, |translator| {
                let expr = translator.translate_expr(self.expr.borrow());

                debug!("Translation returned: {}", expr);

                if settings.optimize {
                    core::optimize::optimize(&translator.allocator, env, expr)
                } else {
                    interpreter::Global {
                        value: core::freeze_expr(&translator.allocator, expr),
                        info: Default::default(),
                    }
                }
            });

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

            let mut compiler = Compiler::new(
                &*env,
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
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
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
        compiler: &mut ModuleCompiler<'_>,
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
        vm1.call_thunk_top(&closure)
            .map_ok(move |value| ExecuteValue {
                id: module_id,
                expr,
                typ,
                value,
                metadata,
            })
            .map_err(Error::from)
            .and_then(move |v| {
                async move {
                    if run_io {
                        crate::compiler_pipeline::run_io(vm, v).await
                    } else {
                        Ok(v)
                    }
                }
            })
            .await
    }

    async fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler<'_>,
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

        compiler.database.import(filename.into()).await.map(|_| ())
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
        _compiler: &mut ModuleCompiler<'_>,
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
        if filename != module_id.as_ref() {
            return Err(format!("filenames do not match `{}` != `{}`", filename, module_id).into());
        }

        let typ = module.typ;
        let metadata = module.metadata;
        let closure = vm.global_env().new_global_thunk(&vm, module.module)?;
        vm.call_thunk_top(&closure)
            .map_ok(move |value| ExecuteValue {
                id: module_id,
                expr: (),
                typ: typ,
                metadata,
                value,
            })
            .map_err(Error::from)
            .await
    }

    async fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler<'_>,
        vm: T,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> Result<()>
    where
        T: Send + Sync + VmRoot<'vm>,
        'vm: 'async_trait,
    {
        use crate::vm::internal::Global;
        use crate::vm::serialization::DeSeed;
        use base::symbol::SymbolData;

        let Global {
            metadata,
            typ,
            value,
            id: _,
        } = DeSeed::new(&vm, &mut vm.current_context())
            .deserialize(self.0)
            .map_err(|err| err.to_string())?;
        let id = compiler.symbols.symbol(SymbolData {
            global: true,
            location: None,
            name: name,
        });
        vm.set_global(id, typ, metadata.clone(), &value)?;
        info!("Loaded module `{}`", name);
        Ok(())
    }
}

#[cfg(feature = "serde")]
pub async fn compile_to<S, T, E>(
    self_: T,
    compiler: &mut ModuleCompiler<'_>,
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
            .map_ok(move |value| {
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
            .await
    } else {
        Ok(v)
    }
}
