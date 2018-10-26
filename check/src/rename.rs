use base::{
    ast::{
        self, DisplayEnv, Do, Expr, MutVisitor, Pattern, SpannedAlias, SpannedAstType, SpannedExpr,
        TypedIdent,
    },
    pos::{self, BytePos, Span},
    scoped_map::ScopedMap,
    symbol::{Symbol, SymbolModule},
    types::Type,
};

struct Environment {
    stack: ScopedMap<Symbol, (Symbol, Span<BytePos>)>,
}

pub fn rename(symbols: &mut SymbolModule, expr: &mut SpannedExpr<Symbol>) {
    enum TailCall {
        TailCall,
        Return,
    }

    struct RenameVisitor<'a: 'b, 'b> {
        symbols: &'b mut SymbolModule<'a>,
        env: Environment,
    }

    impl<'a, 'b> RenameVisitor<'a, 'b> {
        fn new_pattern(&mut self, pattern: &mut ast::SpannedPattern<Symbol>) {
            match pattern.value {
                Pattern::Record {
                    ref mut fields,
                    ref mut implicit_import,
                    ..
                } => {
                    for field in fields {
                        match field.value {
                            Some(ref mut pat) => self.new_pattern(pat),
                            None => {
                                let id = field.name.value.clone();
                                field.name.value = self.stack_var(id, pattern.span);
                            }
                        }
                    }
                    if let Some(ref mut implicit_import) = *implicit_import {
                        let new_name =
                            self.stack_var(implicit_import.value.clone(), implicit_import.span);
                        implicit_import.value = new_name;
                    }
                }
                Pattern::Ident(ref mut id) => {
                    let new_name = self.stack_var(id.name.clone(), pattern.span);
                    id.name = new_name;
                }
                Pattern::As(ref mut id, ref mut pat) => {
                    let new_name = self.stack_var(id.value.clone(), pattern.span);
                    id.value = new_name;
                    self.new_pattern(pat)
                }
                Pattern::Tuple { ref mut elems, .. } => {
                    for elem in elems {
                        self.new_pattern(elem);
                    }
                }
                Pattern::Constructor(_, ref mut args) => {
                    for arg in args {
                        self.new_pattern(arg);
                    }
                }
                Pattern::Literal(_) | Pattern::Error => (),
            }
        }

        fn stack_var(&mut self, id: Symbol, span: Span<BytePos>) -> Symbol {
            use std::fmt::Write;

            let old_id = id.clone();
            let name = self.symbols.string(&id).to_owned();
            let mut new_name = format!("{}:{}", name, span.start());
            let mut i = 0;
            while self.symbols.contains_name(&new_name) {
                let truncate_len = new_name
                    .trim_right_matches(|c: char| c.is_digit(10) || c == '_')
                    .len();
                new_name.truncate(truncate_len);

                write!(new_name, "_{}", i).unwrap();
                i += 1;
            }
            let new_id = self.symbols.symbol(new_name);
            debug!("Rename binding `{:?}` = `{:?}`", (&old_id), (&new_id),);
            self.env.stack.insert(old_id, (new_id.clone(), span));
            new_id
        }

        fn stack_type(&mut self, span: Span<BytePos>, alias: &mut SpannedAlias<Symbol>) {
            let new = self.symbols.scoped_symbol(alias.value.name.declared_name());
            self.env
                .stack
                .insert(alias.value.name.clone(), (new.clone(), span));
            alias.value.name = new;
        }

        /// Renames `id` to the unique identifier which have the type `expected`
        /// Returns `Some(new_id)` if renaming was necessary or `None` if no renaming was necessary
        /// as `id` was currently unique (#Int+, #Float*, etc)
        fn rename(&self, id: &Symbol) -> Option<Symbol> {
            self.env.stack.get(id).map(|t| t.0.clone())
        }

        fn rename_expr(&mut self, expr: &mut SpannedExpr<Symbol>) -> TailCall {
            match expr.value {
                Expr::Ident(ref mut id)
                    // FIXME Still allow renaming of variants somehow without causing resolution
                    // problems with types
                    if !id.name.declared_name().starts_with(char::is_uppercase) =>
                {
                    if let Some(new_id) = self.rename(&id.name) {
                        debug!("Rename identifier {} = {}", id.name, new_id);
                        id.name = new_id;
                    }
                }
                Expr::Record {
                    ref mut exprs,
                    ref mut base,
                    ..
                } => {
                    for expr_field in exprs {
                        match expr_field.value {
                            Some(ref mut expr) => self.visit_expr(expr),
                            None => {
                                if let Some(new_id) = self.rename(&expr_field.name.value) {
                                    debug!("Rename record field {} = {}", expr_field.name, new_id);
                                    expr_field.name.value = new_id;
                                }
                            }
                        }
                    }

                    if let Some(ref mut base) = *base {
                        self.visit_expr(base);
                    }
                }
                Expr::Infix {
                    ref mut lhs,
                    ref mut op,
                    ref mut rhs,
                    ref mut implicit_args,
                } => {
                    if let Some(new_id) = self.rename(&op.value.name) {
                        debug!(
                            "Rename {} = {}",
                            self.symbols.string(&op.value.name),
                            self.symbols.string(&new_id)
                        );
                        op.value.name = new_id;
                    }
                    self.visit_expr(lhs);
                    self.visit_expr(rhs);
                    for arg in implicit_args {
                        self.visit_expr(arg);
                    }
                }
                Expr::Match(ref mut expr, ref mut alts) => {
                    self.visit_expr(expr);
                    for alt in alts {
                        self.env.stack.enter_scope();
                        self.new_pattern(&mut alt.pattern);
                        self.visit_expr(&mut alt.expr);
                        self.env.stack.exit_scope();
                    }
                }
                Expr::LetBindings(ref mut bindings, _) => {
                    self.env.stack.enter_scope();

                    let is_recursive = bindings.is_recursive();

                    for bind in bindings.iter_mut() {
                        if !is_recursive {
                            self.visit_expr(&mut bind.expr);
                        }
                        if let Some(ref mut typ) = bind.typ {
                            self.visit_ast_type(typ.as_mut())
                        }
                        self.new_pattern(&mut bind.name);
                    }

                    if is_recursive {
                        for bind in bindings {
                            self.env.stack.enter_scope();
                            for arg in &mut bind.args {
                                arg.name.value.name =
                                    self.stack_var(arg.name.value.name.clone(), arg.name.span);
                            }
                            self.visit_expr(&mut bind.expr);
                            self.env.stack.exit_scope();
                        }
                    }

                    return TailCall::TailCall;
                }
                Expr::Lambda(ref mut lambda) => {
                    self.env.stack.enter_scope();

                    for arg in &mut lambda.args {
                        arg.name.value.name =
                            self.stack_var(arg.name.value.name.clone(), expr.span);
                    }

                    self.visit_expr(&mut lambda.body);

                    self.env.stack.exit_scope();
                }
                Expr::TypeBindings(ref mut bindings, _) => {
                    self.env.stack.enter_scope();
                    for bind in &mut **bindings {
                        self.stack_type(expr.span, &mut bind.alias);
                    }
                    for bind in bindings {
                        self.visit_alias(&mut bind.alias);
                    }

                    return TailCall::TailCall;
                }
                Expr::Do(Do {
                    ref mut id,
                    ref mut bound,
                    ref mut flat_map_id,
                    ..
                }) => {
                    let flat_map = self.symbols.symbol("flat_map");
                    *flat_map_id = Some(Box::new(pos::spanned(
                        id.span,
                        Expr::Ident(TypedIdent {
                            name: flat_map,
                            typ: Type::hole(),
                        }),
                    )));

                    let flat_map_id = flat_map_id
                        .as_mut()
                        .unwrap_or_else(|| ice!("flat_map_id not set before renaming"));

                    self.visit_expr(flat_map_id);
                    self.visit_expr(bound);

                    self.env.stack.enter_scope();

                    id.value.name = self.stack_var(id.value.name.clone(), id.span);

                    return TailCall::TailCall;
                }

                _ => ast::walk_mut_expr(self, expr),
            }
            TailCall::Return
        }
    }

    impl<'a, 'b, 'c> MutVisitor<'c> for RenameVisitor<'a, 'b> {
        type Ident = Symbol;

        fn visit_expr(&mut self, mut expr: &mut SpannedExpr<Self::Ident>) {
            let mut i = 0;
            loop {
                match self.rename_expr(expr) {
                    TailCall::Return => break,
                    TailCall::TailCall => {
                        expr = match { expr }.value {
                            Expr::LetBindings(_, ref mut new_expr)
                            | Expr::TypeBindings(_, ref mut new_expr)
                            | Expr::Do(Do {
                                body: ref mut new_expr,
                                ..
                            }) => new_expr,
                            _ => ice!("Only Let and Type expressions can tailcall"),
                        };
                        i += 1;
                    }
                }
            }

            for _ in 0..i {
                self.env.stack.exit_scope();
            }
        }

        fn visit_ast_type(&mut self, s: &'c mut SpannedAstType<Self::Ident>) {
            match s.value {
                Type::ExtendRow { ref mut types, .. } => {
                    for field in types {
                        if let Some(alias) = field.typ.try_get_alias_mut() {
                            if let Some(new_name) = self.rename(&field.name) {
                                alias.name = new_name;
                            }
                        }
                    }
                }
                Type::Ident(ref mut id) => {
                    if let Some(new_id) = self.rename(id) {
                        *id = new_id;
                    }
                }
                _ => (),
            }
            ast::walk_mut_ast_type(self, s)
        }
    }

    let mut visitor = RenameVisitor {
        symbols: symbols,
        env: Environment {
            stack: ScopedMap::new(),
        },
    };
    visitor.visit_expr(expr);
}
