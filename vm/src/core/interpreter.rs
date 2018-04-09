use base::ast::{Literal, TypedIdent};
use base::fnv::FnvSet;
use base::kind::{ArcKind, KindEnv};
use base::merge::merge_iter;
use base::scoped_map::ScopedMap;
use base::symbol::{Symbol, SymbolRef};
use base::types::{Alias, ArcType, TypeEnv};
use core::optimize::{walk_expr_alloc, DifferentLifetime, ExprProducer, SameLifetime, Visitor};
use core::{self, Allocator, CExpr, Closure, Expr, LetBinding, Named, Pattern};
use std::ops::{Deref, DerefMut};
use types::*;

use {Error, Result};

fn is_variable_in_expression<'a, I>(iter: I, expr: CExpr) -> bool
where
    I: IntoIterator<Item = &'a Symbol>,
{
    struct FreeVars(FnvSet<Symbol>);
    impl<'e> Visitor<'e, 'e> for FreeVars {
        type Producer = SameLifetime<'e>;

        fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
            match *expr {
                Expr::Ident(ref id, ..) => {
                    self.0.insert(id.name.clone());
                    None
                }
                _ => walk_expr_alloc(self, expr),
            }
        }
        fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
            None
        }
    }
    let mut free_vars = FreeVars(FnvSet::default());
    free_vars.visit_expr(expr);
    iter.into_iter().any(|field| free_vars.0.contains(field))
}

#[derive(Copy, Clone, Debug)]
enum Reduced<L, G> {
    Local(L),
    Global(G),
}

type ReducedExpr<'l, 'g> = Reduced<CExpr<'l>, CExpr<'g>>;

impl<'l, 'g> ReducedExpr<'l, 'g> {
    fn into_local(self, allocator: &'l Allocator<'l>) -> CExpr<'l> {
        match self {
            Reduced::Local(e) => e,
            Reduced::Global(e) => DifferentLifetime::new(allocator).produce(e),
        }
    }
    fn as_ref(&self) -> &Expr {
        match *self {
            Reduced::Local(e) | Reduced::Global(e) => e,
        }
    }
}

macro_rules! match_reduce {
    ($expr: expr, $wrapper: ident; $($pat: pat => $alt: expr),*) => {
        match $expr {
            Reduced::Local(e) => {
                let $wrapper = Reduced::Local;
                match *e {
                    $($pat => $alt),*
                }
            }
            Reduced::Global(e) => {
                let $wrapper = Reduced::Global;
                match *e {
                    $($pat => $alt),*
                }
            }
        }
    }
}

impl<'l, 'g> From<CExpr<'l>> for ReducedExpr<'l, 'g> {
    fn from(expr: CExpr<'l>) -> Self {
        Reduced::Local(expr)
    }
}

pub struct Pure<'a, 'l: 'a, 'g: 'a>(bool, &'a Compiler<'g, 'l>, &'a mut FunctionEnvs<'l, 'g>);

impl<'a, 'l, 'g, 'expr> Visitor<'l, 'expr> for Pure<'a, 'l, 'g> {
    type Producer = DifferentLifetime<'l, 'expr>;

    fn visit_expr(&mut self, expr: CExpr<'expr>) -> Option<CExpr<'l>> {
        if !self.0 {
            return None;
        }
        match *expr {
            Expr::Call(f, _) => {
                match *f {
                    Expr::Ident(ref id, ..) => {
                        match self.1.find(&id.name, self.2) {
                            Some(variable) => match variable {
                                Binding::Expr(expr) => {
                                    self.visit_expr(expr.as_ref());
                                }
                                Binding::Closure(closure) => {
                                    self.visit_expr(closure.as_ref().1.as_ref());
                                }
                                Binding::None => self.0 = false,
                            },
                            // If we can't resolve the identifier to an expression it is a
                            // primitive function which can be impure
                            // FIXME Let primitive functions mark themselves as pure somehow
                            None => if !id.name.as_ref().starts_with("#") {
                                self.0 = false;
                            },
                        }
                    }
                    _ => (),
                }
                walk_expr_alloc(self, expr)
            }
            Expr::Let(ref bind, expr) => {
                match bind.expr {
                    // Creating a group of closures is always pure (though calling them may not be)
                    Named::Recursive(_) => (),
                    Named::Expr(expr) => {
                        walk_expr_alloc(self, expr);
                    }
                }
                walk_expr_alloc(self, expr)
            }
            _ => walk_expr_alloc(self, expr),
        }
    }
    fn detach_allocator(&self) -> Option<&'l Allocator<'l>> {
        None
    }
}

enum TailCall<'a, T> {
    Tail(CExpr<'a>),
    Value(T),
}

pub type ClosureRef<'a> = (&'a [TypedIdent<Symbol>], CExpr<'a>);

type ReducedClosure<'l, 'g> = Reduced<ClosureRef<'l>, ClosureRef<'g>>;

impl<'l, 'g> ReducedClosure<'l, 'g> {
    fn as_ref(&self) -> (&[TypedIdent<Symbol>], ReducedExpr<'l, 'g>) {
        match *self {
            Reduced::Local((a, e)) => (a, Reduced::Local(e)),
            Reduced::Global((a, e)) => (a, Reduced::Global(e)),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Binding<E, C> {
    Expr(E),
    Closure(C),
    None,
}

impl<'l, 'g, C> From<ReducedExpr<'l, 'g>> for Binding<ReducedExpr<'l, 'g>, C> {
    fn from(expr: ReducedExpr<'l, 'g>) -> Self {
        Binding::Expr(expr)
    }
}

impl<'l, 'g, E> From<ReducedClosure<'l, 'g>> for Binding<E, ReducedClosure<'l, 'g>> {
    fn from(expr: ReducedClosure<'l, 'g>) -> Self {
        Binding::Closure(expr)
    }
}

type StackBinding<'l, 'g> = Binding<ReducedExpr<'l, 'g>, ReducedClosure<'l, 'g>>;

struct FunctionEnv<'l, 'g> {
    /// The variables currently in scope in the this function.
    stack: ScopedMap<Symbol, StackBinding<'l, 'g>>,
}

struct FunctionEnvs<'l, 'g> {
    envs: Vec<FunctionEnv<'l, 'g>>,
}

impl<'l, 'g> Deref for FunctionEnvs<'l, 'g> {
    type Target = FunctionEnv<'l, 'g>;
    fn deref(&self) -> &FunctionEnv<'l, 'g> {
        self.envs.last().expect("FunctionEnv")
    }
}

impl<'l, 'g> DerefMut for FunctionEnvs<'l, 'g> {
    fn deref_mut(&mut self) -> &mut FunctionEnv<'l, 'g> {
        self.envs.last_mut().expect("FunctionEnv")
    }
}

impl<'l, 'g> FunctionEnvs<'l, 'g> {
    fn new() -> FunctionEnvs<'l, 'g> {
        FunctionEnvs { envs: vec![] }
    }

    fn start_function(&mut self, compiler: &mut Compiler) {
        compiler.stack_types.enter_scope();
        compiler.stack_constructors.enter_scope();
        self.envs.push(FunctionEnv::new());
    }

    fn end_function(&mut self, compiler: &mut Compiler) -> FunctionEnv<'l, 'g> {
        compiler.stack_types.exit_scope();
        compiler.stack_constructors.exit_scope();
        self.envs.pop().expect("FunctionEnv in scope")
    }

    fn push_stack_var<T>(&mut self, compiler: &Compiler<'g, 'l>, s: Symbol, expr: T)
    where
        T: Into<StackBinding<'l, 'g>>,
    {
        let expr = expr.into();
        let expr = {
            let mut p = Pure(true, compiler, self);
            match expr {
                Binding::Expr(expr) => {
                    p.visit_expr(expr.as_ref());
                }
                Binding::Closure(_) | Binding::None => (),
            }
            // Only allow pure expression to be folded
            if p.0 {
                expr
            } else {
                Binding::None
            }
        };
        self.new_stack_var(s, expr)
    }
}

impl<'l, 'g> FunctionEnv<'l, 'g> {
    fn new() -> FunctionEnv<'l, 'g> {
        FunctionEnv {
            stack: ScopedMap::new(),
        }
    }

    fn push_unknown_stack_var(&mut self, s: Symbol) {
        self.new_stack_var(s, Binding::None)
    }

    fn new_stack_var(&mut self, s: Symbol, expr: StackBinding<'l, 'g>) {
        self.stack.insert(s, expr);
    }

    fn exit_scope(&mut self) -> VmIndex {
        let mut count = 0;
        for _ in self.stack.exit_scope() {
            count += 1;
        }
        count
    }
}

pub type GlobalBinding<'a> = Binding<CExpr<'a>, ClosureRef<'a>>;

pub struct Compiler<'a, 'e> {
    allocator: &'e Allocator<'e>,
    globals: &'a Fn(&Symbol) -> Option<GlobalBinding<'a>>,
    stack_constructors: ScopedMap<Symbol, ArcType>,
    stack_types: ScopedMap<Symbol, Alias<Symbol, ArcType>>,
    bindings: Vec<LetBinding<'e>>,
}

impl<'a, 'e> KindEnv for Compiler<'a, 'e> {
    fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
        None
    }
}

impl<'a, 'e> TypeEnv for Compiler<'a, 'e> {
    fn find_type(&self, _id: &SymbolRef) -> Option<&ArcType> {
        None
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        self.stack_types.get(id)
    }
}

impl<'a, 'e> Compiler<'a, 'e> {
    pub fn new(
        allocator: &'e Allocator<'e>,
        globals: &'a Fn(&Symbol) -> Option<GlobalBinding<'a>>,
    ) -> Compiler<'a, 'e> {
        Compiler {
            allocator,
            globals,
            stack_constructors: ScopedMap::new(),
            stack_types: ScopedMap::new(),
            bindings: Vec::new(),
        }
    }

    fn find(
        &self,
        id: &Symbol,
        current: &mut FunctionEnvs<'e, 'a>,
    ) -> Option<StackBinding<'e, 'a>> {
        current
            .stack
            .get(id)
            .cloned()
            .or_else(|| {
                let i = current.envs.len() - 1;
                let (rest, _current) = current.envs.split_at_mut(i);
                rest.iter()
                    .rev()
                    .filter_map(|env| env.stack.get(id).cloned())
                    .next()
            })
            .or_else(|| {
                (self.globals)(id).map(|global| match global {
                    Binding::Expr(expr) => Binding::Expr(Reduced::Global(expr)),
                    Binding::Closure(c) => Binding::Closure(Reduced::Global(c)),
                    Binding::None => Binding::None,
                })
            })
    }

    /// Compiles an expression to a zero argument function which can be directly fed to the
    /// interpreter
    pub fn compile_expr(&mut self, expr: CExpr<'e>) -> Result<CExpr<'e>> {
        let mut env = FunctionEnvs::new();

        env.start_function(self);
        debug!("Interpreting: {}", expr);
        let new_expr = self.compile(expr, &mut env)?;
        env.end_function(self);
        Ok(new_expr
            .map(|expr| expr.into_local(self.allocator))
            .unwrap_or(expr))
    }

    fn load_identifier(
        &self,
        id: &Symbol,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<StackBinding<'e, 'a>> {
        match self.find(id, function) {
            Some(expr) => {
                if let Binding::Expr(e) = expr {
                    debug!("Loading `{}` as `{}`", id, e.as_ref());
                } else {
                    debug!("Unable to fold `{}`", id);
                }
                Ok(expr)
            }
            // Can't inline what we can't resolve
            None => Ok(Binding::None),
        }
    }

    fn walk_expr(
        &mut self,
        expr: CExpr<'e>,
        functions: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<Option<ReducedExpr<'e, 'a>>> {
        struct ReplaceVisitor<'a: 'f, 'e: 'f, 'f> {
            compiler: &'f mut Compiler<'a, 'e>,
            functions: &'f mut FunctionEnvs<'e, 'a>,
            error: Option<Error>,
        }
        impl<'a, 'e, 'f> Visitor<'e, 'e> for ReplaceVisitor<'a, 'e, 'f> {
            type Producer = SameLifetime<'e>;

            fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
                match self.compiler.compile(expr, self.functions) {
                    Err(err) => {
                        self.error = Some(err);
                        None
                    }
                    Ok(opt) => opt.map(|expr| expr.into_local(self.allocator())),
                }
            }
            fn detach_allocator(&self) -> Option<&'e Allocator<'e>> {
                Some(self.compiler.allocator)
            }
        }

        let mut visitor = ReplaceVisitor {
            compiler: self,
            functions,
            error: None,
        };
        let new_expr = walk_expr_alloc(&mut visitor, expr);
        match visitor.error {
            Some(err) => Err(err),
            None => Ok(new_expr.map(Reduced::Local)),
        }
    }

    fn compile(
        &mut self,
        mut expr: CExpr<'e>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<Option<ReducedExpr<'e, 'a>>> {
        // Store a stack of expressions which need to be cleaned up after this "tailcall" loop is
        // done
        function.stack.enter_scope();
        let scope_start = self.bindings.len();
        loop {
            match self.compile_(expr, function)? {
                TailCall::Tail(tail) => expr = tail,
                TailCall::Value(mut value) => {
                    let allocator = self.allocator;
                    for bind in self.bindings.drain(scope_start..).rev() {
                        let variable_in_value = {
                            let body = value.as_ref().map_or(expr, |v| v.as_ref());
                            match bind.expr {
                                Named::Recursive(ref closures) => is_variable_in_expression(
                                    closures.iter().map(|closure| &closure.name.name),
                                    body,
                                ),
                                Named::Expr(_) => {
                                    is_variable_in_expression(Some(&bind.name.name), body)
                                }
                            }
                        };
                        if variable_in_value {
                            value = Some(Reduced::Local(&*self.allocator.arena.alloc(Expr::Let(
                                bind,
                                value.map_or(expr, |value| value.into_local(allocator)),
                            ))));
                        }
                    }
                    return Ok(value);
                }
            }
        }
    }

    fn compile_(
        &mut self,
        expr: CExpr<'e>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<TailCall<'e, Option<ReducedExpr<'e, 'a>>>> {
        let reduced = match *expr {
            Expr::Const(_, _) => Some(Reduced::Local(expr)),
            Expr::Ident(ref id, _) => match self.load_identifier(&id.name, function)? {
                Binding::Expr(expr) => Some(expr),
                _ => None,
            },
            Expr::Let(ref let_binding, ref body) => {
                self.stack_constructors.enter_scope();
                let new_named = match let_binding.expr {
                    core::Named::Expr(ref bind_expr) => {
                        let reduced = self.compile(bind_expr, function)?;
                        function.push_stack_var(
                            self,
                            let_binding.name.name.clone(),
                            Binding::Expr(reduced.unwrap_or(Reduced::Local(bind_expr))),
                        );
                        reduced.map(|e| Named::Expr(e.into_local(self.allocator)))
                    }
                    core::Named::Recursive(ref closures) => {
                        for closure in closures.iter() {
                            function.push_stack_var(
                                self,
                                closure.name.name.clone(),
                                Reduced::Local((&closure.args[..], closure.expr)),
                            );
                        }
                        let mut result = Ok(());
                        let new_closures = merge_iter(
                            closures,
                            |closure| {
                                function.stack.enter_scope();

                                let new_body = match self.compile_lambda(
                                    &closure.name,
                                    &closure.args,
                                    &closure.expr,
                                    function,
                                ) {
                                    Ok(b) => b,
                                    Err(err) => {
                                        result = Err(err);
                                        return None;
                                    }
                                };
                                let new_body = new_body.map(|expr| Closure {
                                    pos: closure.pos,
                                    name: closure.name.clone(),
                                    args: closure.args.clone(),
                                    expr: expr.into_local(self.allocator),
                                });

                                function.exit_scope();

                                new_body
                            },
                            Clone::clone,
                        ).map(Named::Recursive);
                        result?;
                        new_closures
                    }
                };
                if let Some(expr) = new_named {
                    self.bindings.push(LetBinding {
                        expr,
                        ..let_binding.clone()
                    });
                }
                return Ok(TailCall::Tail(body));
            }
            Expr::Call(f, args) => {
                let f = self.compile(f, function)?.unwrap_or(Reduced::Local(f));
                match *f.as_ref() {
                    Expr::Ident(ref id, ..) => {
                        if id.name.as_ref().starts_with("#") && args.len() == 2 {
                            self.reduce_primitive_binop(function, expr, id, args)?
                        } else {
                            match self.load_identifier(&id.name, function)? {
                                Binding::Closure(closure) => {
                                    function.start_function(self);
                                    let (closure_args, closure_body) = closure.as_ref();
                                    // FIXME Avoid doing into_local here somehow
                                    let closure_body = closure_body.into_local(self.allocator);
                                    for (name, value) in closure_args.iter().zip(args) {
                                        function.push_stack_var(
                                            self,
                                            name.name.clone(),
                                            Reduced::Local(value),
                                        );
                                    }
                                    let expr = self.compile(closure_body, function)?;
                                    function.end_function(self);
                                    expr
                                }
                                _ => self.walk_expr(expr, function)?,
                            }
                        }
                    }
                    _ => self.walk_expr(expr, function)?,
                }
            }
            Expr::Match(expr, alts) => {
                let expr = self.compile(expr, function)?
                    .unwrap_or(Reduced::Local(expr));
                for alt in alts {
                    self.stack_constructors.enter_scope();
                    function.stack.enter_scope();
                    match alt.pattern {
                        Pattern::Constructor(_, ref args) => for arg in args.iter() {
                            function.push_unknown_stack_var(arg.name.clone());
                        },
                        Pattern::Record { .. } => {
                            self.compile_let_pattern(&alt.pattern, expr, function)?;
                        }
                        Pattern::Ident(ref id) => {
                            function.push_stack_var(self, id.name.clone(), expr);
                        }
                        Pattern::Literal(_) => (),
                    }
                    let new_expr = self.compile(&alt.expr, function)?
                        .unwrap_or(Reduced::Local(&alt.expr));
                    function.exit_scope();
                    self.stack_constructors.exit_scope();
                    match alt.pattern {
                        Pattern::Record(ref fields) if alts.len() == 1 => {
                            let fields = fields
                                .iter()
                                .map(|field| field.1.as_ref().unwrap_or(&field.0.name));
                            if !is_variable_in_expression(fields, new_expr.as_ref()) {
                                debug!("Removing redundant match `{}`", alt.pattern);
                                return Ok(TailCall::Value(Some(new_expr)));
                            }
                        }
                        _ => (),
                    }
                }
                None
            }
            Expr::Data(..) => self.walk_expr(expr, function)?,
        };
        Ok(TailCall::Value(reduced))
    }

    fn compile_let_pattern(
        &mut self,
        pattern: &Pattern,
        pattern_expr: ReducedExpr<'e, 'a>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<()> {
        fn peek_through_lets<'l, 'g, 'e>(
            compiler: &mut Compiler<'g, 'l>,
            function: &mut FunctionEnvs<'l, 'g>,
            expr: CExpr<'e>,
        ) -> Option<CExpr<'e>> {
            fn peek_through_lets_(expr: CExpr) -> CExpr {
                match *expr {
                    Expr::Let(_, body) => peek_through_lets_(body),
                    _ => expr,
                }
            }
            let mut p = Pure(true, compiler, function);
            p.visit_expr(expr);
            if p.0 {
                Some(peek_through_lets_(expr))
            } else {
                None
            }
        }
        let pattern_expr = match pattern_expr {
            Reduced::Local(expr) => {
                Reduced::Local(peek_through_lets(self, function, expr).unwrap_or(expr))
            }
            Reduced::Global(expr) => {
                Reduced::Global(peek_through_lets(self, function, expr).unwrap_or(expr))
            }
        };
        match *pattern {
            Pattern::Ident(ref name) => {
                function.push_stack_var(self, name.name.clone(), pattern_expr);
            }
            Pattern::Record(ref fields) => {
                match_reduce!{
                    pattern_expr, wrap;

                    Expr::Data(ref data_id, ref exprs, _, _) => {
                        for pattern_field in fields {
                            let field = data_id
                                .typ
                                .row_iter()
                                .position(|field| field.name.name_eq(&pattern_field.0.name))
                                .expect("ICE: Record field does not exist");
                            let field_name = pattern_field
                                .1
                                .as_ref()
                                .unwrap_or(&pattern_field.0.name)
                                .clone();
                            let expr = match exprs[field] {
                                Expr::Ident(ref id, _) => self.load_identifier(&id.name, function)?,
                                ref expr => wrap(expr).into(),
                            };
                            function.push_stack_var(self, field_name, expr);
                        }
                    },
                    _ => ice!("Expected record, got `{}` at {:?}", pattern_expr.as_ref(), pattern)
                }
            }
            Pattern::Constructor(..) => ice!("constructor pattern in let"),
            Pattern::Literal(..) => ice!("literal pattern in let"),
        }
        Ok(())
    }

    fn compile_lambda(
        &mut self,
        _id: &TypedIdent,
        args: &[TypedIdent],
        body: CExpr<'e>,
        function: &mut FunctionEnvs<'e, 'a>,
    ) -> Result<Option<ReducedExpr<'e, 'a>>> {
        function.start_function(self);

        function.stack.enter_scope();
        for arg in args {
            function.push_unknown_stack_var(arg.name.clone());
        }
        let body = self.compile(body, function)?;

        function.exit_scope();

        function.end_function(self);
        Ok(body)
    }

    fn reduce_primitive_binop(
        &mut self,
        function: &mut FunctionEnvs<'e, 'a>,
        expr: CExpr<'e>,
        id: &TypedIdent<Symbol>,
        args: &'e [Expr<'e>],
    ) -> Result<Option<ReducedExpr<'e, 'a>>> {
        macro_rules! binop {
            () => {{
                let f: fn(_, _) -> _ = match id.name.as_ref().chars().last().unwrap() {
                    '+' => |l, r| l + r,
                    '-' => |l, r| l - r,
                    '*' => |l, r| l * r,
                    '/' => |l, r| l / r,
                    _ => return Err(format!("Invalid binop `{}`", id.name).into()),
                };
                f
            }
            }
        }

        let l = self.compile(&args[0], function)?;
        let r = self.compile(&args[1], function)?;
        Ok(match (
            l.as_ref().map(|l| l.as_ref()),
            r.as_ref().map(|r| r.as_ref()),
        ) {
            (Some(&Expr::Const(Literal::Int(l), ..)), Some(&Expr::Const(Literal::Int(r), ..))) => {
                let f = binop!();
                Some(Reduced::Local(
                    self.allocator
                        .arena
                        .alloc(Expr::Const(Literal::Int(f(l, r)), expr.span())),
                ))
            }
            (
                Some(&Expr::Const(Literal::Float(l), ..)),
                Some(&Expr::Const(Literal::Float(r), ..)),
            ) => {
                let f = binop!();
                Some(Reduced::Local(
                    self.allocator
                        .arena
                        .alloc(Expr::Const(Literal::Float(f(l, r)), expr.span())),
                ))
            }
            _ => match *expr {
                Expr::Call(f, args) => {
                    let new_args = self.allocator.arena.alloc_extend(vec![
                        l.map_or(args[0].clone(), |l| l.into_local(self.allocator).clone()),
                        r.map_or(args[1].clone(), |r| r.into_local(self.allocator).clone()),
                    ]);
                    Some(Reduced::Local(&*self.allocator
                        .arena
                        .alloc(Expr::Call(f, new_args))))
                }
                _ => unreachable!(),
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use base::symbol::Symbols;

    use core::grammar::ExprParser;
    use core::*;

    macro_rules! assert_eq_expr {
        ($actual:expr, $expected:expr) => {

            assert_eq_expr!($actual, $expected, |_: &Symbol| None)
        };
        ($actual:expr, $expected:expr, $globals:expr) => {{
            let mut symbols = Symbols::new();
            let globals = $globals;

            let allocator = Allocator::new();

            let actual_expr = ExprParser::new()
                .parse(&mut symbols, &allocator, $actual)
                .unwrap();

            let actual_expr = {
                Compiler::new(&allocator, &globals)
                    .compile_expr(allocator.arena.alloc(actual_expr))
                    .unwrap()
            };

            let expected_expr = ExprParser::new()
                .parse(&mut symbols, &allocator, $expected)
                .unwrap();

            assert_deq!(*actual_expr, expected_expr);
        }
        }
    }

    #[test]
    fn fold_constant_variable() {
        let _ = ::env_logger::try_init();

        assert_eq_expr!("let x = 1 in x ", " 1 ");
    }

    #[test]
    fn fold_multiple_constant_variables() {
        let _ = ::env_logger::try_init();

        assert_eq_expr!("let x = 1 in let y = x in y ", " 1 ");
    }

    #[test]
    fn fold_record_pattern_match() {
        let _ = ::env_logger::try_init();

        assert_eq_expr!("let x = 1 in match { x } with | { x } -> x end", "1");
    }

    #[test]
    fn dont_remove_let_that_cant_be_folded() {
        let _ = ::env_logger::try_init();

        let expr = r#"
        let x = f 1 in
        x"#;
        assert_eq_expr!(expr, expr);
    }

    #[test]
    fn fold_global() {
        let _ = ::env_logger::try_init();

        let global_alloc = Allocator::new();
        let global: CExpr = global_alloc
            .arena
            .alloc(Expr::Const(Literal::Int(1), Span::default()));

        let expr = r#"
        x"#;
        assert_eq_expr!(expr, "1", move |_: &_| Some(Binding::Expr(global)));
    }

    #[test]
    fn fold_primitive_op() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            (#Int+) 1 2
        "#;
        assert_eq_expr!(expr, "3");
    }

    #[test]
    fn fold_function_call() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            let f x y = (#Int+) x y
            in f 1 2
        "#;
        assert_eq_expr!(expr, "3");
    }

    #[test]
    fn fold_function_call_with_unknown_parameters() {
        let _ = ::env_logger::try_init();

        let expr = r#"
            let f x y = (#Int+) x y in
            let g y = f 2 y in
            g
        "#;
        assert_eq_expr!(
            expr,
            r#"
            let g y = (#Int+) 2 y in
            g
        "#
        );
    }

    // TODO
    #[test]
    #[ignore]
    fn fold_global_function_call_with_unknown_parameters() {
        let _ = ::env_logger::try_init();
        let mut symbols = Symbols::new();
        let global_allocator = Allocator::new();
        let global = ExprParser::new()
            .parse(
                &mut symbols,
                &global_allocator,
                "let f x y = (#Int+) x y in { f }",
            )
            .unwrap();
        let global: CExpr = global_allocator.arena.alloc(global);

        let expr = r#"
            let g y = (match global with | { f } -> f end) 2 y in
            g
        "#;
        assert_eq_expr!(
            expr,
            r#"
            let g y = (#Int+) 2 y in
            g
        "#,
            move |s: &Symbol| if s.as_ref() == "f" {
                match *global {
                    Expr::Let(ref bind, _) => match bind.expr {
                        Named::Recursive(ref closures) => {
                            Some(Binding::Closure((&closures[0].args[..], closures[0].expr)))
                        }
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            } else {
                Some(Binding::Expr(global))
            }
        );
    }
}
