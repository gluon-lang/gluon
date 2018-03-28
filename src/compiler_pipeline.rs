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
use std::ops::Deref;
use std::result::Result as StdResult;

#[cfg(feature = "serde")]
use either::Either;

use base::ast::SpannedExpr;
use base::error::{Errors, InFile};
use base::metadata::Metadata;
use base::types::{ArcType, Type};
use base::source::Source;
use base::symbol::{Name, NameBuf, Symbol, SymbolModule};
use base::resolve;

use vm::core;
use vm::compiler::CompiledModule;
use vm::future::{BoxFutureValue, FutureValue};
use vm::macros::MacroExpander;
use vm::thread::{Execute, RootedValue, Thread, ThreadInternal, VmRoot};

use {Compiler, Error, Result};

fn execute<T, F>(vm: T, f: F) -> FutureValue<Execute<T>>
where
    T: Deref<Target = Thread>,
    F: for<'vm> FnOnce(&'vm Thread) -> FutureValue<Execute<&'vm Thread>>,
{
    let opt = match f(&vm) {
        FutureValue::Value(result) => Some(result.map(|v| v.1)),
        FutureValue::Future(_) => None,
        FutureValue::Polled => return FutureValue::Polled,
    };
    match opt {
        Some(result) => FutureValue::Value(result.map(|v| (vm, v))),
        None => FutureValue::Future(Execute::new(vm)),
    }
}

pub type SalvageResult<T> = StdResult<T, (Option<T>, Error)>;

/// Result type of successful macro expansion
pub struct MacroValue<E> {
    pub expr: E,
}

pub trait MacroExpandable {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    fn expand_macro(
        self,
        compiler: &mut Compiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>>
    where
        Self: Sized,
    {
        let mut macros = MacroExpander::new(thread);
        let expr = self.expand_macro_with(compiler, &mut macros, file, expr_str)?;
        if let Err(err) = macros.finish() {
            return Err((Some(expr), InFile::new(file, expr_str, err).into()));
        }
        Ok(expr)
    }

    fn expand_macro_with(
        self,
        compiler: &mut Compiler,
        macros: &mut MacroExpander,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>>;
}

impl<'s> MacroExpandable for &'s str {
    type Expr = SpannedExpr<Symbol>;

    fn expand_macro_with(
        self,
        compiler: &mut Compiler,
        macros: &mut MacroExpander,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        compiler
            .parse_expr(macros.vm.global_env().type_cache(), file, self)
            .map_err(|err| (None, err.into()))
            .and_then(|mut expr| {
                let result = (&mut expr)
                    .expand_macro_with(compiler, macros, file, expr_str)
                    .map(|_| ())
                    .map_err(|(value, err)| (value.map(|_| ()), err));
                if let Err((value, err)) = result {
                    return Err((value.map(|_| MacroValue { expr }), err));
                }
                Ok(MacroValue { expr })
            })
    }
}

impl<'s> MacroExpandable for &'s mut SpannedExpr<Symbol> {
    type Expr = &'s mut SpannedExpr<Symbol>;

    fn expand_macro_with(
        self,
        compiler: &mut Compiler,
        macros: &mut MacroExpander,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        if compiler.implicit_prelude && !expr_str.starts_with("//@NO-IMPLICIT-PRELUDE") {
            compiler.include_implicit_prelude(macros.vm.global_env().type_cache(), file, self);
        }
        macros.run(self);
        Ok(MacroValue { expr: self })
    }
}

impl MacroExpandable for SpannedExpr<Symbol> {
    type Expr = SpannedExpr<Symbol>;

    fn expand_macro_with(
        mut self,
        compiler: &mut Compiler,
        macros: &mut MacroExpander,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<MacroValue<Self::Expr>> {
        if compiler.implicit_prelude && !expr_str.starts_with("//@NO-IMPLICIT-PRELUDE") {
            compiler.include_implicit_prelude(macros.vm.global_env().type_cache(), file, &mut self);
        }
        let prev_errors = mem::replace(&mut macros.errors, Errors::new());
        macros.run(&mut self);
        let errors = mem::replace(&mut macros.errors, prev_errors);
        if errors.has_errors() {
            Err((None, InFile::new(file, expr_str, errors).into()))
        } else {
            Ok(MacroValue { expr: self })
        }
    }
}

/// Result type of successful typechecking
pub struct TypecheckValue<E> {
    pub expr: E,
    pub typ: ArcType,
}

pub trait Typecheckable: Sized {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    fn typecheck(
        self,
        compiler: &mut Compiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
    ) -> Result<TypecheckValue<Self::Expr>> {
        self.typecheck_expected(compiler, thread, file, expr_str, None)
    }
    fn typecheck_expected(
        self,
        compiler: &mut Compiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> Result<TypecheckValue<Self::Expr>>;
}

impl<T> Typecheckable for T
where
    T: MacroExpandable,
{
    type Expr = T::Expr;

    fn typecheck_expected(
        self,
        compiler: &mut Compiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> Result<TypecheckValue<Self::Expr>> {
        let mut macro_error = None;
        let expr = match self.expand_macro(compiler, thread, file, expr_str) {
            Ok(expr) => expr,
            Err((Some(expr), err)) => {
                macro_error = Some(err);
                expr
            }
            Err((None, err)) => return Err(err),
        };
        match expr.typecheck_expected(compiler, thread, file, expr_str, expected_type) {
            Ok(value) => match macro_error {
                Some(err) => return Err(err),
                None => Ok(value),
            },
            Err(err) => Err(Errors::from(
                macro_error.into_iter().chain(Some(err)).collect::<Vec<_>>(),
            ).into()),
        }
    }
}

impl<E> Typecheckable for MacroValue<E>
where
    E: BorrowMut<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn typecheck_expected(
        mut self,
        compiler: &mut Compiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> Result<TypecheckValue<Self::Expr>> {
        use check::typecheck::Typecheck;

        let env = thread.get_env();
        let mut tc = Typecheck::new(
            file.into(),
            &mut compiler.symbols,
            &*env,
            thread.global_env().type_cache().clone(),
        );

        let typ = tc.typecheck_expr_expected(self.expr.borrow_mut(), expected_type)
            .map_err(|err| {
                info!("Error when typechecking `{}`: {}", file, err);
                InFile::new(file, expr_str, err)
            })?;

        Ok(TypecheckValue {
            expr: self.expr,
            typ: typ,
        })
    }
}

/// Result of successful compilation
pub struct CompileValue<E> {
    pub expr: E,
    pub typ: ArcType,
    pub module: CompiledModule,
}

pub trait Compileable<Extra> {
    type Expr;

    fn compile(
        self,
        compiler: &mut Compiler,
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
        compiler: &mut Compiler,
        thread: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&'b ArcType>,
    ) -> Result<CompileValue<Self::Expr>> {
        self.typecheck_expected(compiler, thread, file, expr_str, expected_type)
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
        compiler: &mut Compiler,
        thread: &Thread,
        filename: &str,
        expr_str: &str,
        _: Extra,
    ) -> Result<CompileValue<Self::Expr>> {
        use vm::compiler::Compiler;
        debug!("Compile `{}`", filename);
        let mut module = {
            let env = thread.get_env();

            let translator = core::Translator::new(&*env);
            let expr = {
                let expr = translator
                    .allocator
                    .arena
                    .alloc(translator.translate(self.expr.borrow()));

                debug!("Translation returned: {}", expr);

                core::optimize::optimize(&translator.allocator, expr)
            };

            let name = Name::new(filename);
            let name = NameBuf::from(name.module());
            let symbols = SymbolModule::new(
                String::from(AsRef::<str>::as_ref(&name)),
                &mut compiler.symbols,
            );
            let source = Source::new(expr_str);

            let mut compiler = Compiler::new(
                &*env,
                thread.global_env(),
                symbols,
                &source,
                filename.to_string(),
                compiler.emit_debug_info,
            );
            compiler.compile_expr(expr)?
        };
        module.function.id = Symbol::from(filename);
        Ok(CompileValue {
            expr: self.expr,
            typ: self.typ,
            module,
        })
    }
}

/// Result of successful execution
pub struct ExecuteValue<T, E>
where
    T: Deref<Target = Thread>,
{
    pub id: Symbol,
    pub expr: E,
    pub typ: ArcType,
    pub value: RootedValue<T>,
}

pub trait Executable<'vm, Extra> {
    type Expr;

    fn run_expr<T>(
        self,
        compiler: &mut Compiler,
        vm: T,
        name: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFutureValue<'vm, ExecuteValue<T, Self::Expr>, Error>
    where
        T: Send + VmRoot<'vm>;

    fn load_script<T>(
        self,
        compiler: &mut Compiler,
        vm: T,
        filename: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFutureValue<'vm, (), Error>
    where
        T: Send + VmRoot<'vm>;
}
impl<'vm, C, Extra> Executable<'vm, Extra> for C
where
    C: Compileable<Extra>,
    C::Expr: BorrowMut<SpannedExpr<Symbol>> + Send + 'vm,
{
    type Expr = C::Expr;

    fn run_expr<T>(
        self,
        compiler: &mut Compiler,
        vm: T,
        name: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFutureValue<'vm, ExecuteValue<T, Self::Expr>, Error>
    where
        T: Send + VmRoot<'vm>,
    {
        match self.compile(compiler, &vm, name, expr_str, arg) {
            Ok(v) => v.run_expr(compiler, vm, name, expr_str, ()),
            Err(err) => FutureValue::Value(Err(err)),
        }
    }
    fn load_script<T>(
        self,
        compiler: &mut Compiler,
        vm: T,
        filename: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFutureValue<'vm, (), Error>
    where
        T: Send + VmRoot<'vm>,
    {
        match self.compile(compiler, &vm, filename, expr_str, arg) {
            Ok(v) => v.load_script(compiler, vm, filename, expr_str, ()),
            Err(err) => FutureValue::Value(Err(err)),
        }
    }
}
impl<'vm, E> Executable<'vm, ()> for CompileValue<E>
where
    E: BorrowMut<SpannedExpr<Symbol>> + Send + 'vm,
{
    type Expr = E;

    fn run_expr<T>(
        self,
        compiler: &mut Compiler,
        vm: T,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFutureValue<'vm, ExecuteValue<T, Self::Expr>, Error>
    where
        T: Send + VmRoot<'vm>,
    {
        let CompileValue {
            expr,
            typ,
            mut module,
        } = self;
        let run_io = compiler.run_io;
        let module_id = Symbol::from(format!("@{}", name));
        module.function.id = module_id.clone();
        let closure = try_future!(vm.global_env().new_global_thunk(module));

        let vm1 = vm.clone();
        execute(vm1, |vm| vm.call_thunk(closure))
            .map(|(vm, value)| ExecuteValue {
                id: module_id,
                expr: expr,
                typ: typ,
                value: vm.root_value_with_self(value),
            })
            .map_err(Error::from)
            .and_then(move |v| {
                if run_io {
                    ::compiler_pipeline::run_io(vm, v)
                } else {
                    FutureValue::sync(Ok(v)).boxed()
                }
            })
            .boxed()
    }
    fn load_script<T>(
        self,
        compiler: &mut Compiler,
        vm: T,
        filename: &str,
        expr_str: &str,
        _: (),
    ) -> BoxFutureValue<'vm, (), Error>
    where
        T: Send + VmRoot<'vm>,
    {
        use check::metadata;

        let run_io = compiler.run_io;
        let filename = filename.to_string();

        let vm1 = vm.clone();
        let vm2 = vm.clone();
        self.run_expr(compiler, vm1, &filename, expr_str, ())
            .and_then(move |v| {
                if run_io {
                    ::compiler_pipeline::run_io(vm2, v)
                } else {
                    FutureValue::sync(Ok(v)).boxed()
                }
            })
            .and_then(move |mut value| {
                let (metadata, _) = metadata::metadata(&*vm.get_env(), value.expr.borrow_mut());
                try_future!(vm.set_global(
                    value.id.clone(),
                    value.typ,
                    metadata,
                    value.value.get_value(),
                ));
                info!("Loaded module `{}` filename", filename);
                FutureValue::sync(Ok(()))
            })
            .boxed()
    }
}

#[cfg(feature = "serde")]
pub struct Precompiled<D>(pub D);

#[cfg_attr(feature = "serde_derive_state", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive_state",
           serde(deserialize_state = "::vm::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive_state", serde(serialize_state = "::vm::serialization::SeSeed"))]
pub struct Module {
    #[cfg_attr(feature = "serde_derive_state", serde(state_with = "::vm::serialization::borrow"))]
    pub typ: ArcType,

    pub metadata: Metadata,

    #[cfg_attr(feature = "serde_derive_state", serde(state))]
    pub module: CompiledModule,
}

#[cfg(feature = "serde")]
impl<'vm, 'de, D> Executable<'vm, ()> for Precompiled<D>
where
    D: ::serde::Deserializer<'de>,
{
    type Expr = ();

    fn run_expr<T>(
        self,
        _compiler: &mut Compiler,
        vm: T,
        filename: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFutureValue<'vm, ExecuteValue<T, Self::Expr>, Error>
    where
        T: Send + VmRoot<'vm>,
    {
        use vm::serialization::DeSeed;

        let module: Module = try_future!(
            DeSeed::new(&vm)
                .deserialize(self.0)
                .map_err(|err| err.to_string())
        );
        let module_id = module.module.function.id.clone();
        if filename != module_id.as_ref() {
            return FutureValue::sync(Err(format!(
                "filenames do not match `{}` != `{}`",
                filename, module_id
            ).into()))
                .boxed();
        }
        let typ = module.typ;
        let vm1 = vm.clone();
        let closure = try_future!(vm.global_env().new_global_thunk(module.module));
        execute(vm1, |vm| vm.call_thunk(closure))
            .map(|(vm, value)| ExecuteValue {
                id: module_id,
                expr: (),
                typ: typ,
                value: vm.root_value_with_self(value),
            })
            .map_err(Error::from)
            .boxed()
    }
    fn load_script<T>(
        self,
        compiler: &mut Compiler,
        vm: T,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFutureValue<'vm, (), Error>
    where
        T: Send + VmRoot<'vm>,
    {
        use vm::serialization::DeSeed;
        use vm::internal::Global;

        let Global {
            metadata,
            typ,
            value,
            id: _,
        } = try_future!(
            DeSeed::new(&vm)
                .deserialize(self.0)
                .map_err(|err| err.to_string())
        );
        let id = compiler.symbols.symbol(format!("@{}", name));
        try_future!(vm.set_global(id, typ, metadata, value,));
        info!("Loaded module `{}`", name);
        FutureValue::sync(Ok(())).boxed()
    }
}

#[cfg(feature = "serde")]
pub fn compile_to<S, T, E>(
    self_: T,
    compiler: &mut Compiler,
    thread: &Thread,
    file: &str,
    expr_str: &str,
    arg: E,
    serializer: S,
) -> StdResult<S::Ok, Either<Error, S::Error>>
where
    S: ::serde::Serializer,
    S::Error: 'static,
    T: Compileable<E>,
{
    use serde::ser::SerializeState;
    use vm::serialization::SeSeed;
    let CompileValue {
        expr: _,
        typ,
        module,
    } = self_
        .compile(compiler, thread, file, expr_str, arg)
        .map_err(Error::from)
        .map_err(Either::Left)?;
    let module = Module {
        typ,
        metadata: Metadata::default(),
        module,
    };
    module
        .serialize_state(serializer, &SeSeed::new())
        .map_err(Either::Right)
}

pub fn run_io<'vm, T, E>(
    vm: T,
    v: ExecuteValue<T, E>,
) -> BoxFutureValue<'vm, ExecuteValue<T, E>, Error>
where
    E: Send + 'vm,
    T: Send + VmRoot<'vm>,
{
    use check::check_signature;
    use vm::api::{VmType, IO};
    use vm::api::generic::A;

    if check_signature(&*vm.get_env(), &v.typ, &IO::<A>::make_forall_type(&vm)) {
        let ExecuteValue {
            id,
            expr,
            typ,
            value,
        } = v;

        let vm1 = vm.clone();
        execute(vm1, |vm| vm.execute_io(value.get_value()))
            .map(move |(_, value)| {
                // The type of the new value will be `a` instead of `IO a`
                let actual = resolve::remove_aliases_cow(&*vm.get_env(), &typ);
                let actual = match **actual {
                    Type::App(_, ref arg) => arg[0].clone(),
                    _ => ice!("ICE: Expected IO type found: `{}`", actual),
                };
                ExecuteValue {
                    id,
                    expr,
                    value: vm.root_value_with_self(value),
                    typ: actual,
                }
            })
            .map_err(Error::from)
            .boxed()
    } else {
        FutureValue::sync(Ok(v)).boxed()
    }
}
