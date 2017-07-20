use std::ops::{Deref, DerefMut};
use interner::InternedStr;
use base::ast::{Literal, TypedIdent, Typed, DisplayEnv, SpannedExpr};
use base::fnv::FnvSet;
use base::resolve;
use base::kind::{ArcKind, KindEnv};
use base::types::{self, Alias, ArcType, BuiltinType, RecordSelector, Type, TypeEnv};
use base::scoped_map::ScopedMap;
use base::symbol::{Symbol, SymbolRef, SymbolModule};
use base::pos::{Line, NO_EXPANSION};
use base::source::Source;
use core::{self, Allocator, Expr, Pattern};
use core::optimize::{Visitor, walk_expr_alloc};
use types::*;
use vm::GlobalVmState;
use source_map::{LocalMap, SourceMap};
use self::Variable::*;

use {Error, Result};

pub type CExpr<'a> = &'a core::Expr<'a>;

pub struct FreeVars(FnvSet<Symbol>);

impl<'e> Visitor<'e> for FreeVars {
    fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
        match *expr {
            Expr::Ident(ref id, ..) => {
                self.0.insert(id.name.clone());
                None
            }
            _ => walk_expr_alloc(self, expr),
        }
    }
    fn allocator(&self) -> &'e Allocator<'e> {
        unreachable!()
    }
}

pub struct Pure(bool);

impl<'e> Visitor<'e> for Pure {
    fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
        if !self.0 {
            return None;
        }
        match *expr {
            Expr::Call(..) => {
                // FIXME Don't treat all function calls as impure
                self.0 = false;
                None
            }
            _ => walk_expr_alloc(self, expr),
        }
    }
    fn allocator(&self) -> &'e Allocator<'e> {
        unreachable!()
    }
}

#[derive(Clone, Debug)]
pub enum Variable<'a, G> {
    Stack(Option<&'a Expr<'a>>),
    Global(G),
    Constructor(VmTag, VmIndex),
}

/// Field accesses on records can either be by name in the case of polymorphic records or by offset
/// when the record is non-polymorphic (which is faster)
enum FieldAccess {
    Name,
    Index(VmIndex),
}

enum TailCall<'a, T> {
    Tail(CExpr<'a>),
    Value(T),
}

struct FunctionEnv<'a> {
    /// The variables currently in scope in the this function.
    stack: ScopedMap<Symbol, Option<&'a Expr<'a>>>,
}

struct FunctionEnvs<'a> {
    envs: Vec<FunctionEnv<'a>>,
}

impl<'a> Deref for FunctionEnvs<'a> {
    type Target = FunctionEnv<'a>;
    fn deref(&self) -> &FunctionEnv<'a> {
        self.envs.last().expect("FunctionEnv")
    }
}

impl<'a> DerefMut for FunctionEnvs<'a> {
    fn deref_mut(&mut self) -> &mut FunctionEnv<'a> {
        self.envs.last_mut().expect("FunctionEnv")
    }
}

impl<'a> FunctionEnvs<'a> {
    fn new() -> FunctionEnvs<'a> {
        FunctionEnvs { envs: vec![] }
    }

    fn start_function(&mut self, compiler: &mut Compiler) {
        compiler.stack_types.enter_scope();
        compiler.stack_constructors.enter_scope();
        self.envs.push(FunctionEnv::new());
    }

    fn end_function(&mut self, compiler: &mut Compiler) -> FunctionEnv<'a> {
        compiler.stack_types.exit_scope();
        compiler.stack_constructors.exit_scope();
        self.envs.pop().expect("FunctionEnv in scope")
    }
}

impl<'a> FunctionEnv<'a> {
    fn new() -> FunctionEnv<'a> {
        FunctionEnv {
            stack: ScopedMap::new(),
        }
    }

    fn push_unknown_stack_var(&mut self, compiler: &Compiler, s: Symbol) {
        self.new_stack_var(compiler, s, None)
    }

    fn push_stack_var(&mut self, compiler: &Compiler, s: Symbol, expr: &'a Expr<'a>) {
        self.new_stack_var(compiler, s, Some(expr))
    }

    fn new_stack_var(&mut self, compiler: &Compiler, s: Symbol, mut expr: Option<&'a Expr<'a>>) {
        expr = expr.and_then(|expr| {
            // Only allow pure expression to be folded
            let mut p = Pure(true);
            p.visit_expr(expr);
            if p.0 {
                Some(expr)
            } else {
                None
            }
        });
        self.stack.insert(s, expr);
    }

    fn exit_scope(&mut self, compiler: &Compiler) -> VmIndex {
        let mut count = 0;
        for x in self.stack.exit_scope() {
            count += 1;
        }
        count
    }
}

pub struct Compiler<'a, 'e> {
    allocator: &'e Allocator<'e>,
    symbols: SymbolModule<'a>,
    stack_constructors: ScopedMap<Symbol, ArcType>,
    stack_types: ScopedMap<Symbol, Alias<Symbol, ArcType>>,
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

    fn find_record(
        &self,
        _fields: &[Symbol],
        _selector: RecordSelector,
    ) -> Option<(ArcType, ArcType)> {
        None
    }
}

impl<'a, 'e> Compiler<'a, 'e> {
    pub fn new(allocator: &'e Allocator<'e>, mut symbols: SymbolModule<'a>) -> Compiler<'a, 'e> {
        Compiler {
            allocator,
            symbols,
            stack_constructors: ScopedMap::new(),
            stack_types: ScopedMap::new(),
        }
    }

    fn find(&self, id: &Symbol, current: &mut FunctionEnvs<'e>) -> Option<Variable<'e, VmIndex>> {
        let variable = self.stack_constructors
            .iter()
            .filter_map(|(_, typ)| match **typ {
                Type::Variant(ref row) => {
                    row.row_iter()
                        .enumerate()
                        .find(|&(_, field)| field.name == *id)
                }
                _ => None,
            })
            .next()
            .map(|(tag, field)| {
                Constructor(
                    tag as VmIndex,
                    types::arg_iter(&field.typ).count() as VmIndex,
                )
            })
            .or_else(|| {
                current.stack.get(id).map(|&expr| Stack(expr)).or_else(|| {
                    let i = current.envs.len() - 1;
                    let (rest, current) = current.envs.split_at_mut(i);
                    rest.iter()
                        .rev()
                        .filter_map(|env| env.stack.get(id).map(|&expr| Stack(expr)))
                        .next()
                })
            });
        variable.and_then(|variable: Variable<'e, VmIndex>| match variable {
            Stack(i) => Some(Stack(i)),
            Global(s) => None,
            Constructor(tag, args) => Some(Constructor(tag, args)),
        })
    }

    fn find_field(&self, typ: &ArcType, field: &Symbol) -> Option<FieldAccess> {
        // Remove all type aliases to get the actual record type
        let typ = resolve::remove_aliases_cow(self, typ);
        let mut iter = typ.row_iter();
        match iter.by_ref().position(|f| f.name.name_eq(field)) {
            Some(index) => {
                for _ in iter.by_ref() {}
                Some(if **iter.current_type() == Type::EmptyRow {
                    // Non-polymorphic record, access by index
                    FieldAccess::Index(index as VmIndex)
                } else {
                    FieldAccess::Name
                })
            }
            None => None,
        }
    }

    /// Compiles an expression to a zero argument function which can be directly fed to the
    /// interpreter
    pub fn compile_expr(&mut self, expr: CExpr<'e>) -> Result<CExpr<'e>> {
        let mut env = FunctionEnvs::new();

        env.start_function(self);
        debug!("Interpreting: {}", expr);
        let new_expr = self.compile(expr, &mut env)?;
        env.end_function(self);
        Ok(new_expr.unwrap_or(expr))
    }

    fn load_identifier(
        &self,
        id: &Symbol,
        function: &mut FunctionEnvs<'e>,
    ) -> Result<Option<&'e Expr<'e>>> {
        match self.find(id, function) {
            Some(variable) => {
                match variable {
                    Stack(expr) => {
                        if let Some(e) = expr {
                            debug!("Loading `{}` as `{}`", id, e);
                        } else {
                            debug!("Unable to fold `{}`", id);
                        }
                        Ok(expr)
                    }
                    Global(index) => Ok(None),
                    Constructor(..) => Ok(None),
                }
            }
            // Can't inline what we can't resolve
            None => Ok(None)
        }
    }

    fn walk_expr(
        &mut self,
        expr: CExpr<'e>,
        functions: &mut FunctionEnvs<'e>,
    ) -> Result<Option<CExpr<'e>>> {
        struct ReplaceVisitor<'a: 'f, 'e: 'f, 'f> {
            compiler: &'f mut Compiler<'a, 'e>,
            functions: &'f mut FunctionEnvs<'e>,
            error: Option<Error>,
        }
        impl<'a, 'e, 'f> Visitor<'e> for ReplaceVisitor<'a, 'e, 'f> {
            fn visit_expr(&mut self, expr: CExpr<'e>) -> Option<CExpr<'e>> {
                match self.compiler.compile(expr, self.functions) {
                    Err(err) => {
                        self.error = Some(err);
                        None
                    }
                    Ok(expr) => expr,
                }
            }
            fn allocator(&self) -> &'e Allocator<'e> {
                self.compiler.allocator
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
            None => Ok(new_expr),
        }
    }

    fn compile(
        &mut self,
        mut expr: CExpr<'e>,
        function: &mut FunctionEnvs<'e>,
    ) -> Result<Option<CExpr<'e>>> {
        // Store a stack of expressions which need to be cleaned up after this "tailcall" loop is
        // done
        function.stack.enter_scope();
        loop {
            match self.compile_(expr, function)? {
                TailCall::Tail(tail) => expr = tail,
                TailCall::Value(value) => return Ok(value),
            }
        }
    }

    fn compile_(
        &mut self,
        expr: CExpr<'e>,
        function: &mut FunctionEnvs<'e>,
    ) -> Result<TailCall<'e, Option<CExpr<'e>>>> {
        let reduced = match *expr {
            Expr::Const(_, _) => Some(expr),
            Expr::Ident(ref id, _) => self.load_identifier(&id.name, function)?,
            Expr::Let(ref let_binding, ref body) => {
                self.stack_constructors.enter_scope();
                match let_binding.expr {
                    core::Named::Expr(ref bind_expr) => {
                        let reduced = self.compile(bind_expr, function)?;
                        function.push_stack_var(
                            self,
                            let_binding.name.name.clone(),
                            reduced.unwrap_or(bind_expr),
                        );
                    }
                    core::Named::Recursive(ref closures) => {
                        for closure in closures.iter() {
                            function.push_unknown_stack_var(self, closure.name.name.clone());
                        }
                        for closure in closures {
                            function.stack.enter_scope();

                            self.compile_lambda(
                                &closure.name,
                                &closure.args,
                                &closure.expr,
                                function,
                            )?;

                            function.exit_scope(self);
                        }
                    }
                }
                return Ok(TailCall::Tail(body));
            }
            Expr::Call(..) => {
                self.walk_expr(expr, function)?
            }
            Expr::Match(expr, alts) => {
                let expr = self.compile(expr, function)?.unwrap_or(expr);
                let typ = expr.env_type_of(self);
                for alt in alts {
                    self.stack_constructors.enter_scope();
                    function.stack.enter_scope();
                    match alt.pattern {
                        Pattern::Constructor(_, ref args) => {
                            for arg in args.iter() {
                                function.push_unknown_stack_var(self, arg.name.clone());
                            }
                        }
                        Pattern::Record { .. } => {
                            let typ = &expr.env_type_of(self);
                            self.compile_let_pattern(&alt.pattern, expr, typ, function)?;
                        }
                        Pattern::Ident(ref id) => {
                            function.push_stack_var(self, id.name.clone(), expr);
                        }
                    }
                    let new_expr = self.compile(&alt.expr, function)?.unwrap_or(&alt.expr);
                    function.exit_scope(self);
                    self.stack_constructors.exit_scope();
                    match alt.pattern {
                        Pattern::Record(ref fields) if alts.len() == 1 => {
                            let mut free_vars = FreeVars(FnvSet::default());
                            free_vars.visit_expr(new_expr);
                            let free_vars_in_expr = fields.iter().any(|field| {
                                let field_name = field.1.as_ref().unwrap_or(&field.0.name);
                                free_vars.0.contains(field_name)
                            });
                            if !free_vars_in_expr {
                                debug!("Removing redundant match `{}`", alt.pattern);
                                return Ok(TailCall::Value(Some(new_expr)));
                            }
                        }
                        _ => (),
                    }
                }
                None
            }
            Expr::Data(ref id, exprs, ..) => self.walk_expr(expr, function)?,
        };
        Ok(TailCall::Value(reduced))
    }

    fn compile_let_pattern(
        &mut self,
        pattern: &Pattern,
        pattern_expr: &'e Expr<'e>,
        pattern_type: &ArcType,
        function: &mut FunctionEnvs<'e>,
    ) -> Result<()> {
        match *pattern {
            Pattern::Ident(ref name) => {
                function.push_stack_var(self, name.name.clone(), pattern_expr);
            }
            Pattern::Record(ref fields) => {
                let typ = resolve::remove_aliases(self, pattern_type.clone());
                match *pattern_expr {
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
                            function.push_stack_var(self, field_name, &exprs[field]);
                        }
                    }
                    _ => panic!("Expected record, got {} at {:?}", typ, pattern),
                }
            }
            Pattern::Constructor(..) => panic!("constructor pattern in let"),
        }
        Ok(())
    }

    fn compile_lambda(
        &mut self,
        id: &TypedIdent,
        args: &[TypedIdent],
        body: CExpr<'e>,
        function: &mut FunctionEnvs<'e>,
    ) -> Result<()> {
        function.start_function(self);

        function.stack.enter_scope();
        for arg in args {
            function.push_unknown_stack_var(self, arg.name.clone());
        }
        self.compile(body, function)?;

        function.exit_scope(self);

        function.end_function(self);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use base::symbol::Symbols;

    use core::*;
    use core::grammar::parse_Expr as parse_core_expr;

    macro_rules! assert_eq_expr {
        ($actual: expr, $expected: expr) => { {
            let mut symbols = Symbols::new();

            let allocator = Allocator::new();
    
            let actual_expr = parse_core_expr(&mut symbols, &allocator, $actual)
                .unwrap();

            let actual_expr = {
                let symbols = SymbolModule::new("test".to_string(), &mut symbols);
                Compiler::new(&allocator, symbols)
                    .compile_expr(allocator.arena.alloc(actual_expr))
                    .unwrap()
            };

            let expected_expr = parse_core_expr(&mut symbols, &allocator, $expected)
                .unwrap();
            
            assert_deq!(*actual_expr, expected_expr);
        } }
    }

    #[test]
    fn fold_constant_variable() {
        let _ = ::env_logger::init();

        assert_eq_expr!("let x = 1 in x ", " 1 ");
    }

    #[test]
    fn fold_multiple_constant_variables() {
        let _ = ::env_logger::init();

        assert_eq_expr!("let x = 1 in let y = x in y ", " 1 ");
    }

    #[test]
    fn fold_record_pattern_match() {
        let _ = ::env_logger::init();

        assert_eq_expr!("let x = 1 in match { x } with | { x } -> x end", "1");
    }

    #[test]
    fn dont_remove_let_that_cant_be_folded() {
        let _ = ::env_logger::init();

        let expr = r#"
        let x = f 1 in
        x"#;
        assert_eq_expr!(expr, expr);
    }
}
