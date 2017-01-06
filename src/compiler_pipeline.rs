
//! Advanced compiler pipeline which ensures that the compilation phases are run in order even if
//! not the entire compilation procedure is needed.
//!
//! Each trait in this module represents a stage in a full compilation so to only run compilation
//! up until and including typechecking the `Typecheckable` trait can be used. Furthermore, if
//! compilation should continue at some point after typechecking has succeeded, the result of
//! typechecking (`TypecheckValue`) can be used as input to the next stage, ensuring that it is
//! difficult to forget a stage.

use std::borrow::{Borrow, BorrowMut};

use futures::Future;

use base::ast::SpannedExpr;
use base::error::InFile;
use base::types::ArcType;
use base::source::Source;
use base::symbol::{Name, NameBuf, Symbol, SymbolModule};

use vm::compiler::CompiledFunction;
use vm::macros::MacroExpander;
use vm::thread::{RootedValue, Thread, ThreadInternal};

use {Compiler, Result};

/// Result type of successful macro expansion
pub struct MacroValue<E> {
    pub expr: E,
}

pub trait MacroExpandable {
    type Expr: BorrowMut<SpannedExpr<Symbol>>;

    fn expand_macro(self,
                    compiler: &mut Compiler,
                    thread: &Thread,
                    file: &str)
                    -> Result<MacroValue<Self::Expr>>
        where Self: Sized,
    {
        let mut macros = MacroExpander::new(thread);
        let expr = self.expand_macro_with(compiler, &mut macros, file)?;
        macros.finish()?;
        Ok(expr)
    }

    fn expand_macro_with(self,
                         compiler: &mut Compiler,
                         macros: &mut MacroExpander,
                         file: &str)
                         -> Result<MacroValue<Self::Expr>>;
}

impl<'s> MacroExpandable for &'s str {
    type Expr = SpannedExpr<Symbol>;

    fn expand_macro_with(self,
                         compiler: &mut Compiler,
                         macros: &mut MacroExpander,
                         file: &str)
                         -> Result<MacroValue<Self::Expr>> {

        compiler.parse_expr(file, self)
            .map_err(From::from)
            .and_then(|mut expr| {
                expr.expand_macro_with(compiler, macros, file)?;
                Ok(MacroValue { expr: expr })
            })
    }
}

impl<'s> MacroExpandable for &'s mut SpannedExpr<Symbol> {
    type Expr = &'s mut SpannedExpr<Symbol>;

    fn expand_macro_with(self,
                         compiler: &mut Compiler,
                         macros: &mut MacroExpander,
                         file: &str)
                         -> Result<MacroValue<Self::Expr>> {
        if compiler.implicit_prelude {
            compiler.include_implicit_prelude(file, self);
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

    fn typecheck(self,
                 compiler: &mut Compiler,
                 thread: &Thread,
                 file: &str,
                 expr_str: &str)
                 -> Result<TypecheckValue<Self::Expr>> {
        self.typecheck_expected(compiler, thread, file, expr_str, None)
    }
    fn typecheck_expected(self,
                          compiler: &mut Compiler,
                          thread: &Thread,
                          file: &str,
                          expr_str: &str,
                          expected_type: Option<&ArcType>)
                          -> Result<TypecheckValue<Self::Expr>>;
}

impl<T> Typecheckable for T
    where T: MacroExpandable,
{
    type Expr = T::Expr;

    fn typecheck_expected(self,
                          compiler: &mut Compiler,
                          thread: &Thread,
                          file: &str,
                          expr_str: &str,
                          expected_type: Option<&ArcType>)
                          -> Result<TypecheckValue<Self::Expr>> {

        self.expand_macro(compiler, thread, file)
            .and_then(|expr| {
                expr.typecheck_expected(compiler, thread, file, expr_str, expected_type)
            })
    }
}

impl<E> Typecheckable for MacroValue<E>
    where E: BorrowMut<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn typecheck_expected(mut self,
                          compiler: &mut Compiler,
                          thread: &Thread,
                          file: &str,
                          expr_str: &str,
                          expected_type: Option<&ArcType>)
                          -> Result<TypecheckValue<Self::Expr>> {
        use check::typecheck::Typecheck;

        let env = thread.get_env();
        let mut tc = Typecheck::new(file.into(), &mut compiler.symbols, &*env);

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

    fn compile(self,
               compiler: &mut Compiler,
               thread: &Thread,
               file: &str,
               expr_str: &str,
               arg: Extra)
               -> Result<CompileValue<Self::Expr>>;
}
impl<'a, 'b, T> Compileable<Option<&'b ArcType>> for T
    where T: Typecheckable,
{
    type Expr = T::Expr;

    fn compile(self,
               compiler: &mut Compiler,
               thread: &Thread,
               file: &str,
               expr_str: &str,
               expected_type: Option<&'b ArcType>)
               -> Result<CompileValue<Self::Expr>> {

        self.typecheck_expected(compiler, thread, file, expr_str, expected_type)
            .and_then(|tc_value| tc_value.compile(compiler, thread, file, expr_str, ()))
    }
}
impl<E, Extra> Compileable<Extra> for TypecheckValue<E>
    where E: Borrow<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn compile(self,
               compiler: &mut Compiler,
               thread: &Thread,
               filename: &str,
               expr_str: &str,
               _: Extra)
               -> Result<CompileValue<Self::Expr>> {
        use vm::compiler::Compiler;
        debug!("Compile `{}`", filename);
        let mut function = {
            let env = thread.get_env();
            let name = Name::new(filename);
            let name = NameBuf::from(name.module());
            let symbols = SymbolModule::new(String::from(AsRef::<str>::as_ref(&name)),
                                            &mut compiler.symbols);
            let source = Source::new(expr_str);
            let mut compiler = Compiler::new(&*env,
                                             thread.global_env(),
                                             symbols,
                                             &source,
                                             filename.to_string(),
                                             compiler.emit_debug_info);
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
    pub expr: E,
    pub typ: ArcType,
    pub value: RootedValue<&'vm Thread>,
}

pub trait Executable<Extra> {
    type Expr;

    fn run_expr<'vm>(self,
                     compiler: &mut Compiler,
                     vm: &'vm Thread,
                     name: &str,
                     expr_str: &str,
                     arg: Extra)
                     -> Result<ExecuteValue<'vm, Self::Expr>>;
    fn load_script(self,
                   compiler: &mut Compiler,
                   vm: &Thread,
                   filename: &str,
                   expr_str: &str,
                   arg: Extra)
                   -> Result<()>;
}
impl<C, Extra> Executable<Extra> for C
    where C: Compileable<Extra>,
          C::Expr: BorrowMut<SpannedExpr<Symbol>>,
{
    type Expr = C::Expr;

    fn run_expr<'vm>(self,
                     compiler: &mut Compiler,
                     vm: &'vm Thread,
                     name: &str,
                     expr_str: &str,
                     arg: Extra)
                     -> Result<ExecuteValue<'vm, Self::Expr>> {

        self.compile(compiler, vm, name, expr_str, arg)
            .and_then(|v| v.run_expr(compiler, vm, name, expr_str, ()))
    }
    fn load_script(self,
                   compiler: &mut Compiler,
                   vm: &Thread,
                   filename: &str,
                   expr_str: &str,
                   arg: Extra)
                   -> Result<()> {

        self.compile(compiler, vm, filename, expr_str, arg)
            .and_then(|v| v.load_script(compiler, vm, filename, expr_str, ()))
    }
}
impl<E> Executable<()> for CompileValue<E>
    where E: BorrowMut<SpannedExpr<Symbol>>,
{
    type Expr = E;

    fn run_expr<'vm>(self,
                     _compiler: &mut Compiler,
                     vm: &'vm Thread,
                     name: &str,
                     _expr_str: &str,
                     _: ())
                     -> Result<ExecuteValue<'vm, Self::Expr>> {

        let CompileValue { expr, typ, mut function } = self;
        function.id = Symbol::from(name);
        let closure = vm.global_env().new_global_thunk(function)?;
        let (_, value) = vm.call_thunk(closure)?.wait()?;
        Ok(ExecuteValue {
            expr: expr,
            typ: typ,
            value: vm.root_value_ref(value),
        })
    }
    fn load_script(self,
                   _compiler: &mut Compiler,
                   vm: &Thread,
                   filename: &str,
                   _expr_str: &str,
                   _: ())
                   -> Result<()> {
        use check::metadata;

        let CompileValue { mut expr, typ, function } = self;
        let metadata = metadata::metadata(&*vm.get_env(), expr.borrow_mut());
        let closure = vm.global_env().new_global_thunk(function)?;
        let (_, value) = vm.call_thunk(closure)?.wait()?;
        vm.set_global(closure.function.name.clone(), typ, metadata, value)?;
        info!("Loaded module `{}` filename", filename);
        Ok(())
    }
}
