//! Advanced compiler pipeline which ensures that the compilation phases are run in order even if
//! not the entire compilation procedure is needed.
//!
//! Each trait in this module represents a stage in a full compilation so to only run compilation
//! up until and including typechecking the `Typecheckable` trait can be used. Furthermore, if
//! compilation should continue at some point after typechecking has succeeded, the result of
//! typechecking (`TypecheckValue`) can be used as input to the next stage, ensuring that it is
//! difficult to forget a stage.

use std::borrow::{Borrow, BorrowMut};
#[cfg(feature = "serde")]
use std::result::Result as StdResult;

#[cfg(feature = "serde")]
use either::Either;

use base::ast::SpannedExpr;
use base::error::InFile;
use base::metadata::Metadata;
use base::types::{ArcType, Type};
use base::source::Source;
use base::symbol::{Name, NameBuf, Symbol, SymbolModule};
use base::resolve;

use vm::compiler::CompiledFunction;
use vm::future::{BoxFutureValue, FutureValue};
use vm::macros::MacroExpander;
use vm::thread::{RootedValue, Thread, ThreadInternal};

use {Compiler, Error, Result};

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
    ) -> Result<MacroValue<Self::Expr>>
    where
        Self: Sized,
    {
        let mut macros = MacroExpander::new(thread);
        let expr = self.expand_macro_with(compiler, &mut macros, file)?;
        macros.finish()?;
        Ok(expr)
    }

    fn expand_macro_with(
        self,
        compiler: &mut Compiler,
        macros: &mut MacroExpander,
        file: &str,
    ) -> Result<MacroValue<Self::Expr>>;
}

impl<'s> MacroExpandable for &'s str {
    type Expr = SpannedExpr<Symbol>;

    fn expand_macro_with(
        self,
        compiler: &mut Compiler,
        macros: &mut MacroExpander,
        file: &str,
    ) -> Result<MacroValue<Self::Expr>> {
        compiler
            .parse_expr(macros.vm.global_env().type_cache(), file, self)
            .map_err(From::from)
            .and_then(|mut expr| {
                expr.expand_macro_with(compiler, macros, file)?;
                Ok(MacroValue { expr: expr })
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
    ) -> Result<MacroValue<Self::Expr>> {
        if compiler.implicit_prelude {
            compiler.include_implicit_prelude(macros.vm.global_env().type_cache(), file, self);
        }
        macros.run(self);
        Ok(MacroValue { expr: self })
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
        self.expand_macro(compiler, thread, file).and_then(|expr| {
            expr.typecheck_expected(compiler, thread, file, expr_str, expected_type)
        })
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
            .map_err(|err| InFile::new(file, expr_str, err))?;

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
    pub function: CompiledFunction,
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
            .and_then(|tc_value| {
                tc_value.compile(compiler, thread, file, expr_str, ())
            })
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
        let mut function = {
            let env = thread.get_env();
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
            compiler.compile_expr(self.expr.borrow())?
        };
        function.id = Symbol::from(filename);
        Ok(CompileValue {
            expr: self.expr,
            typ: self.typ,
            function: function,
        })
    }
}

/// Result of successful execution
pub struct ExecuteValue<'vm, E> {
    pub id: Symbol,
    pub expr: E,
    pub typ: ArcType,
    pub value: RootedValue<&'vm Thread>,
}

pub trait Executable<'vm, Extra> {
    type Expr;

    fn run_expr(
        self,
        compiler: &mut Compiler,
        vm: &'vm Thread,
        name: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFutureValue<'vm, ExecuteValue<'vm, Self::Expr>, Error>;

    fn load_script(
        self,
        compiler: &mut Compiler,
        vm: &'vm Thread,
        filename: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFutureValue<'vm, (), Error>;
}
impl<'vm, C, Extra> Executable<'vm, Extra> for C
where
    C: Compileable<Extra>,
    C::Expr: BorrowMut<SpannedExpr<Symbol>> + Send + 'vm,
{
    type Expr = C::Expr;

    fn run_expr(
        self,
        compiler: &mut Compiler,
        vm: &'vm Thread,
        name: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFutureValue<'vm, ExecuteValue<'vm, Self::Expr>, Error> {
        match self.compile(compiler, vm, name, expr_str, arg) {
            Ok(v) => v.run_expr(compiler, vm, name, expr_str, ()),
            Err(err) => FutureValue::Value(Err(err)),
        }
    }
    fn load_script(
        self,
        compiler: &mut Compiler,
        vm: &'vm Thread,
        filename: &str,
        expr_str: &str,
        arg: Extra,
    ) -> BoxFutureValue<'vm, (), Error> {
        match self.compile(compiler, vm, filename, expr_str, arg) {
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

    fn run_expr(
        self,
        _compiler: &mut Compiler,
        vm: &'vm Thread,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFutureValue<'vm, ExecuteValue<'vm, Self::Expr>, Error> {
        let CompileValue {
            expr,
            typ,
            mut function,
        } = self;
        let module_id = Symbol::from(name);
        function.id = module_id.clone();
        let closure = try_future!(vm.global_env().new_global_thunk(function));
        vm.call_thunk(closure)
            .map(|(vm, value)| {
                ExecuteValue {
                    id: module_id,
                    expr: expr,
                    typ: typ,
                    value: vm.root_value(value),
                }
            })
            .map_err(Error::from)
            .boxed()
    }
    fn load_script(
        self,
        _compiler: &mut Compiler,
        vm: &'vm Thread,
        filename: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFutureValue<'vm, (), Error> {
        use check::metadata;

        let CompileValue {
            mut expr,
            typ,
            function,
        } = self;
        let (metadata, _) = metadata::metadata(&*vm.get_env(), expr.borrow_mut());
        let closure = try_future!(vm.global_env().new_global_thunk(function));
        let filename = filename.to_string();
        vm.call_thunk(closure)
            .map_err(Error::from)
            .and_then(move |(_, value)| {
                try_future!(vm.set_global(
                    closure.function.name.clone(),
                    typ,
                    metadata,
                    value,
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
    #[cfg_attr(feature = "serde_derive_state", serde(state))] pub function: CompiledFunction,
}

#[cfg(feature = "serde")]
impl<'vm, 'de, D> Executable<'vm, ()> for Precompiled<D>
where
    D: ::serde::Deserializer<'de>,
{
    type Expr = ();

    fn run_expr(
        self,
        _compiler: &mut Compiler,
        vm: &'vm Thread,
        filename: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFutureValue<'vm, ExecuteValue<'vm, Self::Expr>, Error> {
        use vm::serialization::DeSeed;

        let module: Module = try_future!(
            DeSeed::new(vm)
                .deserialize(self.0)
                .map_err(|err| err.to_string())
        );
        let module_id = module.function.id.clone();
        if filename != module_id.as_ref() {
            return FutureValue::sync(Err(
                format!("filenames do not match `{}` != `{}`", filename, module_id).into(),
            )).boxed();
        }
        let typ = module.typ;
        let closure = try_future!(vm.global_env().new_global_thunk(module.function));
        vm.call_thunk(closure)
            .map(|(vm, value)| {
                ExecuteValue {
                    id: module_id,
                    expr: (),
                    typ: typ,
                    value: vm.root_value(value),
                }
            })
            .map_err(Error::from)
            .boxed()
    }
    fn load_script(
        self,
        compiler: &mut Compiler,
        vm: &'vm Thread,
        name: &str,
        _expr_str: &str,
        _: (),
    ) -> BoxFutureValue<'vm, (), Error> {
        use vm::serialization::DeSeed;
        use vm::internal::Global;

        let Global {
            metadata,
            typ,
            value,
            id: _,
        } = try_future!(
            DeSeed::new(vm)
                .deserialize(self.0)
                .map_err(|err| err.to_string())
        );
        let id = compiler.symbols.symbol(name);
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
        function,
    } = self_
        .compile(compiler, thread, file, expr_str, arg)
        .map_err(Error::from)
        .map_err(Either::Left)?;
    let module = Module {
        typ,
        metadata: Metadata::default(),
        function,
    };
    module
        .serialize_state(serializer, &SeSeed::new(thread))
        .map_err(Either::Right)
}

pub fn run_io<'vm, E>(
    vm: &'vm Thread,
    v: ExecuteValue<'vm, E>,
) -> BoxFutureValue<'vm, (RootedValue<&'vm Thread>, ArcType), Error> {
    use check::check_signature;
    use vm::api::{VmType, IO};
    use vm::api::generic::A;

    let ExecuteValue {
        typ: actual, value, ..
    } = v;
    if check_signature(&*vm.get_env(), &actual, &IO::<A>::make_forall_type(vm)) {
        vm.execute_io(*value)
            .map(move |(_, value)| {
                // The type of the new value will be `a` instead of `IO a`
                let actual = resolve::remove_aliases_cow(&*vm.get_env(), &actual);
                let actual = match **actual {
                    Type::App(_, ref arg) => arg[0].clone(),
                    _ => ice!("ICE: Expected IO type found: `{}`", actual),
                };
                (vm.root_value(value), actual)
            })
            .map_err(Error::from)
            .boxed()
    } else {
        FutureValue::sync(Ok((value, actual))).boxed()
    }
}
