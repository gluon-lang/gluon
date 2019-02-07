//! Advanced compiler pipeline which ensures that the compilation phases are run in order even if
//! not the entire compilation procedure is needed.
//!
//! Each trait in this module represents a stage in a full compilation so to only run compilation
//! up until and including typechecking the `Typecheckable` trait can be used. Furthermore, if
//! compilation should continue at some point after typechecking has succeeded, the result of
//! typechecking (`TypecheckValue`) can be used as input to the next stage, ensuring that it is
//! difficult to forget a stage.

use std::borrow::{Borrow, BorrowMut};
use std::mem;
use std::result::Result as StdResult;
use std::sync::Arc;

#[cfg(feature = "serde")]
use either::Either;
use futures::{future, Future};

use crate::base::{
    ast::{SpannedExpr, Typed},
    error::{Errors, InFile},
    fnv::FnvMap,
    metadata::Metadata,
    resolve,
    symbol::{Name, NameBuf, Symbol, SymbolModule},
    types::{ArcType, NullInterner, Type, TypeCache},
};

use crate::check::{metadata, rename};

use crate::vm::{
    compiler::CompiledModule,
    core,
    macros::MacroExpander,
    thread::{RootedThread, RootedValue, Thread, ThreadInternal, VmRoot},
};

use crate::{query::Compilation, Error, ModuleCompiler, Result};

pub type BoxFuture<'vm, T, E> = Box<dyn Future<Item = T, Error = E> + Send + 'vm>;

pub type SalvageResult<T, E = Error> = StdResult<T, (Option<T>, E)>;

fn join_result<T, U, V>(
    result: SalvageResult<T>,
    f: impl FnOnce(&mut T) -> SalvageResult<V>,
    join: impl FnOnce(T) -> U,
) -> SalvageResult<U> {
    let mut first_error = None;
    let mut x = match result {
        Ok(x) => x,
        Err((Some(expr), err)) => {
            first_error = Some(err);
            expr
        }
        Err((None, err)) => return Err((None, err.into())),
    };
    let result = f(&mut x)
        .map(|_| ())
        .map_err(|(value, err)| (value.map(|_| ()), err));
    if let Err((value, err)) = result {
        return Err((
            value.map(|_| join(x)),
            if first_error.is_some() {
                Errors::from(first_error.into_iter().chain(Some(err)).collect::<Vec<_>>()).into()
            } else {
                err
            },
        ));
    }
    match first_error {
        Some(err) => Err((Some(join(x)), err)),
        None => Ok(join(x)),
    }
}

pub fn parse_expr(
    compiler: &mut ModuleCompiler,
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

pub trait MacroExpandable {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    fn expand_macro(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>>
    where
        Self: Sized,
    {
        let mut macros = MacroExpander::new(thread, compiler.database);
        let expr = self.expand_macro_with(compiler, &mut macros, file, expr_str)?;
        if let Err(err) = macros.finish() {
            return Err((
                Some(expr),
                InFile::new(compiler.code_map().clone(), err).into(),
            ));
        }
        Ok(expr)
    }

    fn expand_macro_with(
        self,
        compiler: &mut ModuleCompiler,
        macros: &mut MacroExpander,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>>;
}

impl<'s> MacroExpandable for &'s str {
    type Expr = SpannedExpr<Symbol>;

    fn expand_macro_with(
        self,
        compiler: &mut ModuleCompiler,
        macros: &mut MacroExpander,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        join_result(
            parse_expr(compiler, macros.vm.global_env().type_cache(), file, self)
                .map_err(|(x, err)| (x, err.into())),
            |expr| {
                expr.expand_macro_with(compiler, macros, file, expr_str)
                    .map(|_| ())
                    .map_err(|(opt, err)| (opt.map(|_| ()), err))
            },
            |expr| MacroValue { expr },
        )
    }
}

impl<'s> MacroExpandable for &'s mut SpannedExpr<Symbol> {
    type Expr = &'s mut SpannedExpr<Symbol>;

    fn expand_macro_with(
        self,
        compiler: &mut ModuleCompiler,
        macros: &mut MacroExpander,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        if compiler.compiler_settings().implicit_prelude
            && compiler.compiler.implicit_prelude
            && !expr_str.starts_with("//@NO-IMPLICIT-PRELUDE")
        {
            compiler.include_implicit_prelude(macros.vm.global_env().type_cache(), file, self);
        }
        let prev_errors = mem::replace(&mut macros.errors, Errors::new());
        macros.run(&mut compiler.symbols, self);
        let errors = mem::replace(&mut macros.errors, prev_errors);
        let value = MacroValue { expr: self };
        if errors.has_errors() {
            Err((
                Some(value),
                InFile::new(compiler.code_map().clone(), errors).into(),
            ))
        } else {
            Ok(value)
        }
    }
}

impl MacroExpandable for SpannedExpr<Symbol> {
    type Expr = SpannedExpr<Symbol>;

    fn expand_macro_with(
        mut self,
        compiler: &mut ModuleCompiler,
        macros: &mut MacroExpander,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        let result = (&mut self)
            .expand_macro_with(compiler, macros, file, expr_str)
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

pub trait Renameable: Sized {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    fn rename(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<Renamed<Self::Expr>>;
}

impl<T> Renameable for T
where
    T: MacroExpandable,
{
    type Expr = T::Expr;

    fn rename(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<Renamed<Self::Expr>> {
        join_result(
            self.expand_macro(compiler, thread, file, expr_str),
            |MacroValue { expr }| {
                MacroValue {
                    expr: expr.borrow_mut(),
                }
                .rename(compiler, thread, file, expr_str)
                .map(|_| ())
                .map_err(|(opt, err)| (opt.map(|_| ()), err))
            },
            |MacroValue { expr }| Renamed { expr },
        )
    }
}

impl<E> Renameable for MacroValue<E>
where
    E: BorrowMut<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn rename(
        mut self,
        compiler: &mut ModuleCompiler,
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

pub trait MetadataExtractable: Sized {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    fn extract_metadata(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<WithMetadata<Self::Expr>>;
}

impl<T> MetadataExtractable for T
where
    T: Renameable,
{
    type Expr = T::Expr;

    fn extract_metadata(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<WithMetadata<Self::Expr>> {
        let mut macro_error = None;
        let expr = match self.rename(compiler, thread, file, expr_str) {
            Ok(expr) => expr,
            Err((Some(expr), err)) => {
                macro_error = Some(err);
                expr
            }
            Err((None, err)) => return Err((None, err)),
        };
        match expr.extract_metadata(compiler, thread, file, expr_str) {
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

impl<E> MetadataExtractable for Renamed<E>
where
    E: BorrowMut<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn extract_metadata(
        mut self,
        _compiler: &mut ModuleCompiler,
        thread: &Thread,
        _file: &str,
        _expr_str: &str,
    ) -> SalvageResult<WithMetadata<Self::Expr>> {
        let env = thread.get_env();
        let (metadata, metadata_map) = metadata::metadata(&env, self.expr.borrow_mut());
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

pub trait InfixReparseable: Sized {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    fn reparse_infix(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<InfixReparsed<Self::Expr>>;
}

impl<T> InfixReparseable for T
where
    T: MetadataExtractable,
{
    type Expr = T::Expr;

    fn reparse_infix(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<InfixReparsed<Self::Expr>> {
        let mut macro_error = None;
        let expr = match self.extract_metadata(compiler, thread, file, expr_str) {
            Ok(expr) => expr,
            Err((Some(expr), err)) => {
                macro_error = Some(err);
                expr
            }
            Err((None, err)) => return Err((None, err)),
        };
        match expr.reparse_infix(compiler, thread, file, expr_str) {
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

impl<E> InfixReparseable for WithMetadata<E>
where
    E: BorrowMut<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn reparse_infix(
        self,
        compiler: &mut ModuleCompiler,
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

pub trait Typecheckable: Sized {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    fn typecheck(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<TypecheckValue<Self::Expr>> {
        self.typecheck_expected(compiler, thread, file, expr_str, None)
    }
    fn typecheck_expected(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> SalvageResult<TypecheckValue<Self::Expr>>;
}

impl<T> Typecheckable for T
where
    T: InfixReparseable,
{
    type Expr = T::Expr;

    fn typecheck_expected(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> SalvageResult<TypecheckValue<Self::Expr>> {
        let mut macro_error = None;
        let expr = match self.reparse_infix(compiler, thread, file, expr_str) {
            Ok(expr) => expr,
            Err((Some(expr), err)) => {
                macro_error = Some(err);
                expr
            }
            Err((None, err)) => return Err((None, err)),
        };
        match expr.typecheck_expected(compiler, thread, file, expr_str, expected_type) {
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

impl<E> Typecheckable for InfixReparsed<E>
where
    E: BorrowMut<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn typecheck_expected(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        _expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> SalvageResult<TypecheckValue<Self::Expr>> {
        use crate::check::typecheck::Typecheck;
        trace!("Typecheck: {}", file);

        let InfixReparsed {
            mut expr,
            mut metadata_map,
            metadata,
        } = self;

        let typ = {
            let result = {
                let env = thread.get_env();
                let mut tc = Typecheck::new(
                    file.into(),
                    &mut compiler.symbols,
                    &env,
                    &thread.global_env().type_cache(),
                    &mut metadata_map,
                );

                tc.typecheck_expr_expected(expr.borrow_mut(), expected_type)
            };
            match result {
                Ok(typ) => typ,
                Err(err) => {
                    return Err((
                        Some(TypecheckValue {
                            typ: expr
                                .borrow_mut()
                                .try_type_of(&thread.get_env())
                                .unwrap_or_else(|_| thread.global_env().type_cache().error()),
                            expr,
                            metadata_map,
                            metadata,
                        }),
                        InFile::new(compiler.database.state().code_map.clone(), err).into(),
                    ));
                }
            }
        };

        // Some metadata requires typechecking so recompute it if full metadata is required
        let (metadata, metadata_map) = if compiler.compiler_settings().full_metadata {
            let env = thread.get_env();
            metadata::metadata(&env, expr.borrow_mut())
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
#[derive(Eq, PartialEq, Hash, Debug, Clone)]
pub struct CompileValue<E> {
    pub expr: E,
    pub typ: ArcType,
    pub metadata: Arc<Metadata>,
    pub module: CompiledModule,
}

impl<E> CompileValue<E> {
    pub fn map<F>(self, f: impl FnOnce(E) -> F) -> CompileValue<F> {
        let CompileValue {
            expr,
            typ,
            metadata,
            module,
        } = self;
        CompileValue {
            expr: f(expr),
            typ,
            metadata,
            module,
        }
    }
}

pub trait Compileable<Extra> {
    type Expr;

    fn compile(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        arg: Extra,
    ) -> Result<CompileValue<Self::Expr>>;
}
impl<'a, 'b, T> Compileable<Option<&'b ArcType>> for T
where
    T: Typecheckable,
{
    type Expr = T::Expr;

    fn compile(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&'b ArcType>,
    ) -> Result<CompileValue<Self::Expr>> {
        self.typecheck_expected(compiler, thread, file, expr_str, expected_type)
            .map_err(|(_, err)| err)
            .and_then(|tc_value| tc_value.compile(compiler, thread, file, expr_str, ()))
    }
}
impl<E, Extra> Compileable<Extra> for TypecheckValue<E>
where
    E: Borrow<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn compile(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        filename: &str,
        expr_str: &str,
        extra: Extra,
    ) -> Result<CompileValue<Self::Expr>> {
        (&self)
            .compile(compiler, thread, filename, expr_str, extra)
            .map(|value| value.map(|_| ()))
            .map(
                |CompileValue {
                     typ,
                     metadata,
                     module,
                     ..
                 }| CompileValue {
                    expr: self.expr,
                    typ,
                    metadata,
                    module,
                },
            )
    }
}

impl<'e, E, Extra> Compileable<Extra> for &'e TypecheckValue<E>
where
    E: Borrow<SpannedExpr<Symbol>>,
{
    type Expr = &'e E;

    fn compile(
        self,
        compiler: &mut ModuleCompiler,
        thread: &Thread,
        filename: &str,
        _expr_str: &str,
        _: Extra,
    ) -> Result<CompileValue<Self::Expr>> {
        use crate::vm::compiler::Compiler;

        info!("Compile `{}`", filename);

        let settings = compiler.compiler_settings();

        let mut module = {
            let env = thread.get_env();

            let translator = core::Translator::new(&env);
            let expr = {
                let expr = translator.translate_expr(self.expr.borrow());

                debug!("Translation returned: {}", expr);

                core::optimize::optimize(&translator.allocator, expr)
            };

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
                &env,
                thread.global_env(),
                symbols,
                &source,
                filename.to_string(),
                settings.emit_debug_info,
            );
            compiler.compile_expr(expr)?
        };
        module.function.id = Symbol::from(filename);
        Ok(CompileValue {
            expr: &self.expr,
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

pub trait Executable<'vm, Extra> {
    type Expr;

    fn run_expr<T>(
        self,
        compiler: &mut ModuleCompiler,
        vm: T,
        name: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFuture<'vm, ExecuteValue<RootedThread, Self::Expr>, Error>
    where
        T: Send + VmRoot<'vm>;

    fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler,
        vm: T,
        filename: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFuture<'vm, (), Error>
    where
        T: Send + VmRoot<'vm>;
}
impl<'vm, C, Extra> Executable<'vm, Extra> for C
where
    C: Compileable<Extra>,
    C::Expr: Send + 'vm,
{
    type Expr = C::Expr;

    fn run_expr<T>(
        self,
        compiler: &mut ModuleCompiler,
        vm: T,
        name: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFuture<'vm, ExecuteValue<RootedThread, Self::Expr>, Error>
    where
        T: Send + VmRoot<'vm>,
    {
        match self.compile(compiler, &vm, name, expr_str, arg) {
            Ok(v) => v.run_expr(compiler, vm, name, expr_str, ()),
            Err(err) => Box::new(future::err(err)),
        }
    }
    fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler,
        vm: T,
        filename: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFuture<'vm, (), Error>
    where
        T: Send + VmRoot<'vm>,
    {
        match self.compile(compiler, &vm, filename, expr_str, arg) {
            Ok(v) => v.load_script(compiler, vm, filename, expr_str, ()),
            Err(err) => Box::new(future::err(err)),
        }
    }
}
impl<'vm, E> Executable<'vm, ()> for CompileValue<E>
where
    E: Send + 'vm,
{
    type Expr = E;

    fn run_expr<T>(
        self,
        compiler: &mut ModuleCompiler,
        vm: T,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFuture<'vm, ExecuteValue<RootedThread, Self::Expr>, Error>
    where
        T: Send + VmRoot<'vm>,
    {
        let CompileValue {
            expr,
            typ,
            mut module,
            metadata,
        } = self;
        let run_io = compiler.compiler.run_io;
        let module_id = Symbol::from(format!("@{}", name));
        module.function.id = module_id.clone();
        let closure = try_future!(vm.global_env().new_global_thunk(&vm, module));

        let vm1 = vm.clone();
        Box::new(
            vm1.call_thunk_top(closure)
                .map(move |value| ExecuteValue {
                    id: module_id,
                    expr,
                    typ,
                    value,
                    metadata,
                })
                .map_err(Error::from)
                .and_then(move |v| {
                    if run_io {
                        future::Either::B(crate::compiler_pipeline::run_io(vm, v))
                    } else {
                        future::Either::A(future::ok(v))
                    }
                }),
        )
    }
    fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler,
        _vm: T,
        filename: &str,
        expr_str: &str,
        _: (),
    ) -> BoxFuture<'vm, (), Error>
    where
        T: Send + VmRoot<'vm>,
    {
        let filename = filename.to_string();

        compiler
            .state()
            .inline_modules
            .insert(filename.clone(), expr_str.into());

        Box::new(future::result(
            compiler.database.import(filename.into()).map(|_| ()),
        ))
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
impl<'vm, 'de, D> Executable<'vm, ()> for Precompiled<D>
where
    D: crate::serde::Deserializer<'de>,
{
    type Expr = ();

    fn run_expr<T>(
        self,
        _compiler: &mut ModuleCompiler,
        vm: T,
        filename: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFuture<'vm, ExecuteValue<RootedThread, Self::Expr>, Error>
    where
        T: Send + VmRoot<'vm>,
    {
        use crate::vm::serialization::DeSeed;

        let module: Module = try_future!(DeSeed::new(&vm, &mut vm.current_context())
            .deserialize(self.0)
            .map_err(|err| err.to_string()));
        let module_id = module.module.function.id.clone();
        if filename != module_id.as_ref() {
            return Box::new(future::err(
                format!("filenames do not match `{}` != `{}`", filename, module_id).into(),
            ));
        }

        let typ = module.typ;
        let metadata = module.metadata;
        let closure = try_future!(vm.global_env().new_global_thunk(&vm, module.module));
        Box::new(
            vm.call_thunk_top(closure)
                .map(move |value| ExecuteValue {
                    id: module_id,
                    expr: (),
                    typ: typ,
                    metadata,
                    value,
                })
                .map_err(Error::from),
        )
    }

    fn load_script<T>(
        self,
        compiler: &mut ModuleCompiler,
        vm: T,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFuture<'vm, (), Error>
    where
        T: Send + VmRoot<'vm>,
    {
        use crate::vm::internal::Global;
        use crate::vm::serialization::DeSeed;

        let Global {
            metadata,
            typ,
            value,
            id: _,
        } = try_future!(DeSeed::new(&vm, &mut vm.current_context())
            .deserialize(self.0)
            .map_err(|err| err.to_string()));
        let id = compiler.symbols.symbol(SymbolData {
            global: true,
            location: None,
            name: name,
        });
        try_future!(vm.set_global(id, typ, metadata.clone(), value,));
        info!("Loaded module `{}`", name);
        Box::new(future::ok(()))
    }
}

#[cfg(feature = "serde")]
pub fn compile_to<S, T, E>(
    self_: T,
    compiler: &mut ModuleCompiler,
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
        typ,
        metadata,
        module,
    } = self_
        .compile(compiler, thread, file, expr_str, arg)
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

pub fn run_io<'vm, T, E>(
    vm: T,
    v: ExecuteValue<RootedThread, E>,
) -> impl Future<Item = ExecuteValue<RootedThread, E>, Error = Error>
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
        future::Either::B(
            vm1.execute_io_top(value.get_variant())
                .map(move |value| {
                    // The type of the new value will be `a` instead of `IO a`
                    let actual =
                        resolve::remove_aliases_cow(&vm.get_env(), &mut NullInterner, &typ);
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
                .map_err(Error::from),
        )
    } else {
        future::Either::A(future::ok(v))
    }
}
