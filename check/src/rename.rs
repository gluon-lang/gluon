use itertools::Itertools;

use crate::base::{
    ast::{
        self, AstType, DisplayEnv, Do, Expr, MutVisitor, Pattern, SpannedAlias, SpannedExpr,
        TypedIdent,
    },
    fnv::FnvMap,
    pos::{self, ByteOffset, BytePos, Span},
    scoped_map::ScopedMap,
    source::Source,
    symbol::{Symbol, SymbolData, SymbolModule},
    types::{ArcType, Type},
};

struct Environment {
    stack: ScopedMap<Symbol, (Symbol, Span<BytePos>)>,
}

pub fn rename<'s, 'ast>(
    source: &'s (dyn Source + 's),
    symbols: &mut SymbolModule,
    ast_arena: ast::ArenaRef<'s, 'ast, Symbol>,
    expr: &mut SpannedExpr<'ast, Symbol>,
) {
    enum TailCall {
        TailCall,
        Return,
    }

    struct RenameVisitor<'a: 'b, 'b, 's, 'ast> {
        source: &'s (dyn Source + 's),
        symbols: &'b mut SymbolModule<'a>,
        seen_symbols: FnvMap<Symbol, u32>,
        scope: Vec<Symbol>,
        env: Environment,
        ast_arena: ast::ArenaRef<'s, 'ast, Symbol>,
        hole: ArcType,
    }

    impl<'a, 'b, 's, 'ast> RenameVisitor<'a, 'b, 's, 'ast> {
        fn new_pattern(&mut self, pattern: &mut ast::SpannedPattern<Symbol>) {
            match pattern.value {
                Pattern::Record {
                    ref mut fields,
                    ref mut implicit_import,
                    ..
                } => {
                    for (name, value) in ast::pattern_values_mut(fields) {
                        match value {
                            Some(pat) => self.new_pattern(pat),
                            None => {
                                let id = name.value.clone();
                                name.value = self.stack_var(id, pattern.span);
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
                    for elem in &mut **elems {
                        self.new_pattern(elem);
                    }
                }
                Pattern::Constructor(_, ref mut args) => {
                    for arg in &mut **args {
                        self.new_pattern(arg);
                    }
                }
                Pattern::Literal(_) | Pattern::Error => (),
            }
        }

        // Renames the symbol to be unique in this module
        fn stack_var(&mut self, id: Symbol, span: Span<BytePos>) -> Symbol {
            let mut location = self
                .source
                .location(span.start())
                .map(|location| (location.line.0 + 1, location.column.0 + 1))
                .unwrap_or_else(|| (span.start().0, 0));
            let new_id = self.symbols.symbol(SymbolData {
                global: false,
                name: id.as_str(),
                location: Some(location),
            });

            let index = self.seen_symbols.entry(new_id.clone()).or_default();
            let new_id = if *index == 0 {
                *index += 1;
                new_id
            } else {
                // TODO More reliable way of generating unique symbols
                *index += 1;
                location.1 += *index;
                self.symbols.symbol(SymbolData {
                    global: false,
                    name: id.as_str(),
                    location: Some(location),
                })
            };

            debug!("Rename binding `{:?}` = `{:?}`", id, new_id);

            self.env.stack.insert(id, (new_id.clone(), span));

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

        fn rename_expr(&mut self, expr: &mut SpannedExpr<'ast, Symbol>) -> TailCall {
            match expr.value {
                Expr::Ident(ref mut id)
                    // FIXME Still allow renaming of variants somehow without causing resolution
                    // problems with types
                    if !id.name.declared_name().starts_with(char::is_uppercase) =>
                {
                    if let Some(new_id) = self.rename(&id.name) {
                        id.name = new_id;
                    }
                }
                Expr::Record {
                    ref mut exprs,
                    ref mut base,
                    ..
                } => {
                    for expr_field in &mut **exprs {
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
                    for arg in &mut **implicit_args {
                        self.visit_expr(arg);
                    }
                }
                Expr::Match(ref mut expr, ref mut alts) => {
                    self.visit_expr(expr);
                    for alt in &mut **alts {
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
                            if let Pattern::Ident(id) = &bind.name.value {
                                self.scope.push(id.name.clone());
                            }

                            self.visit_expr(&mut bind.expr);

                            if let Pattern::Ident(_) = &bind.name.value {
                                self.scope.pop();
                            }
                        }
                        if let Some(ref mut typ) = bind.typ {
                            self.visit_ast_type(typ)
                        }
                        self.new_pattern(&mut bind.name);
                    }

                    if is_recursive {
                        for bind in bindings {
                            self.env.stack.enter_scope();
                            for arg in &mut *bind.args {
                                arg.name.value.name =
                                    self.stack_var(arg.name.value.name.clone(), arg.name.span);
                            }

                            if let Pattern::Ident(id) = &bind.name.value {
                                self.scope.push(id.name.clone());
                            }

                            self.visit_expr(&mut bind.expr);

                            if let Pattern::Ident(_) = &bind.name.value {
                                self.scope.pop();
                            }

                            self.env.stack.exit_scope();
                        }
                    }

                    return TailCall::TailCall;
                }
                Expr::Lambda(ref mut lambda) => {
                    let location = self.source.location(expr.span.start()).unwrap_or_else(|| ice!("Lambda without source location"));
                    let name = format!(
                        "{}.{}",
                        self.symbols.module(),
                        self.scope.iter().map(|s| s.as_str()).format("."),
                    );
                    lambda.id.name = self.symbols.symbol(SymbolData {
                        global: false,
                        location: Some((location.line.0 + 1, location.column.0 + 1)),
                        name,
                    });

                    self.env.stack.enter_scope();

                    for arg in &mut *lambda.args {
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
                    for bind in &mut **bindings {
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
                    let flat_map = self.symbols.simple_symbol("flat_map");
                    *flat_map_id = Some(self.ast_arena.alloc(pos::spanned(
                        Span::new(expr.span.end(), expr.span.start() + ByteOffset::from(2)),
                        Expr::Ident(TypedIdent {
                            name: flat_map,
                            typ: self.hole.clone(),
                        }),
                    )));

                    let flat_map_id = flat_map_id
                        .as_mut()
                        .unwrap_or_else(|| ice!("flat_map_id not set before renaming"));

                    self.visit_expr(flat_map_id);
                    self.visit_expr(bound);

                    self.env.stack.enter_scope();

                    if let Some(ref mut id) = *id {
                        self.visit_pattern(id);
                    }

                    return TailCall::TailCall;
                }

                _ => ast::walk_mut_expr(self, expr),
            }
            TailCall::Return
        }
    }

    impl<'a, 'b, 'c, 's, 'ast> MutVisitor<'c, 'ast> for RenameVisitor<'a, 'b, 's, 'ast> {
        type Ident = Symbol;

        fn visit_pattern(&mut self, pattern: &mut ast::SpannedPattern<'ast, Symbol>) {
            self.new_pattern(pattern);
        }

        fn visit_expr(&mut self, mut expr: &mut SpannedExpr<'ast, Self::Ident>) {
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

        fn visit_ast_type(&mut self, s: &'c mut AstType<'ast, Self::Ident>) {
            match &mut **s {
                Type::ExtendTypeRow { types, .. } => {
                    for field in &mut **types {
                        if let Some(alias) = field.typ.try_get_alias_mut() {
                            if let Some(new_name) = self.rename(&field.name.value) {
                                alias.name = new_name;
                            }
                        }
                    }
                }
                Type::Projection(ids) => {
                    // The first id refers to a local variable so we need to rename it
                    if let Some(new_id) = self.rename(&mut ids[0]) {
                        ids[0] = new_id;
                    }
                }
                Type::Ident(id) => {
                    if let Some(new_id) = self.rename(&id.name) {
                        id.name = new_id;
                    }
                }
                _ => (),
            }
            ast::walk_mut_ast_type(self, s)
        }
    }

    let mut visitor = RenameVisitor {
        source,
        symbols: symbols,
        seen_symbols: Default::default(),
        scope: Vec::new(),
        env: Environment {
            stack: ScopedMap::new(),
        },
        ast_arena,
        hole: Type::hole(),
    };
    visitor.visit_expr(expr);
}
