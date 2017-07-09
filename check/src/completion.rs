//! Primitive auto completion and type quering on ASTs

use std::iter::once;
use std::cmp::Ordering;

use base::ast::{Expr, SpannedExpr, SpannedPattern, Pattern, TypedIdent, Typed, Visitor, walk_expr,
                walk_pattern};
use base::fnv::FnvMap;
use base::metadata::Metadata;
use base::resolve;
use base::pos::{BytePos, Span, NO_EXPANSION};
use base::scoped_map::ScopedMap;
use base::symbol::Symbol;
use base::types::{AliasData, ArcType, Type, TypeEnv};

trait OnFound {
    fn on_ident(&mut self, ident: &TypedIdent) {
        let _ = ident;
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        let _ = pattern;
    }

    fn on_alias(&mut self, alias: &AliasData<Symbol, ArcType>) {
        let _ = alias;
    }

    fn expr(&mut self, expr: &SpannedExpr<Symbol>);

    fn pattern(&mut self, pattern: &SpannedPattern<Symbol>);

    fn ident(&mut self, context: &SpannedExpr<Symbol>, ident: &Symbol, typ: &ArcType);

    /// Location points to whitespace
    fn nothing(&mut self);

    fn nothing_pattern(&mut self) {}

    fn found(&self) -> bool;
}

struct GetType<E> {
    env: E,
    typ: Option<ArcType>,
}

impl<E: TypeEnv> OnFound for GetType<E> {
    fn expr(&mut self, expr: &SpannedExpr<Symbol>) {
        self.typ = Some(expr.env_type_of(&self.env));
    }

    fn ident(&mut self, _context: &SpannedExpr<Symbol>, _: &Symbol, typ: &ArcType) {
        self.typ = Some(typ.clone());
    }

    fn pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        self.typ = Some(pattern.env_type_of(&self.env));
    }

    fn nothing(&mut self) {}

    fn found(&self) -> bool {
        self.typ.is_some()
    }
}

#[derive(Debug, PartialEq)]
pub struct Suggestion {
    pub name: String,
    pub typ: ArcType,
}

struct Suggest<E> {
    env: E,
    stack: ScopedMap<Symbol, ArcType>,
    patterns: ScopedMap<Symbol, ArcType>,
    result: Vec<Suggestion>,
}

fn expr_iter<'e>(
    stack: &'e ScopedMap<Symbol, ArcType>,
    expr: &'e SpannedExpr<Symbol>,
) -> Box<Iterator<Item = (&'e Symbol, &'e ArcType)> + 'e> {
    if let Expr::Ident(ref ident) = expr.value {
        Box::new(stack.iter().filter(move |&(k, _)| {
            k.declared_name().starts_with(ident.name.declared_name())
        }))
    } else {
        Box::new(None.into_iter())
    }
}

impl<E> Suggest<E>
where
    E: TypeEnv,
{
    fn ident_iter(&self, context: &SpannedExpr<Symbol>, ident: &Symbol) -> Vec<(Symbol, ArcType)> {
        if let Expr::Projection(ref expr, _, _) = context.value {
            let typ = resolve::remove_aliases(&self.env, expr.env_type_of(&self.env));
            let id = ident.as_ref();
            typ.row_iter()
                .filter(move |field| field.name.as_ref().starts_with(id))
                .map(|field| (field.name.clone(), field.typ.clone()))
                .collect()
        } else {
            vec![]
        }
    }
}

impl<E: TypeEnv> OnFound for Suggest<E> {
    fn on_ident(&mut self, ident: &TypedIdent) {
        self.stack.insert(ident.name.clone(), ident.typ.clone());
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        match pattern.value {
            Pattern::Record {
                ref typ,
                fields: ref field_ids,
                ref types,
                ..
            } => {
                let unaliased = resolve::remove_aliases(&self.env, typ.clone());
                for ast_field in types {
                    if let Some(field) = unaliased.type_field_iter().find(|field| {
                        field.name == ast_field.name.value
                    })
                    {
                        self.on_alias(&field.typ);
                    }
                }
                for field in field_ids {
                    match field.value {
                        Some(_) => (),
                        None => {

                            let name = field.name.value.clone();
                            let typ = unaliased.row_iter()
                                .find(|f| f.name.name_eq(&name))
                                .map(|f| f.typ.clone())
                                // If we did not find a matching field in the type, default to a
                                // type hole so that the user at least gets completion on the name
                                .unwrap_or_else(|| Type::hole());
                            self.stack.insert(name, typ);
                        }
                    }
                }
            }
            Pattern::Ident(ref id) => {
                self.stack.insert(id.name.clone(), id.typ.clone());
            }
            Pattern::Tuple { elems: ref args, .. } |
            Pattern::Constructor(_, ref args) => {
                for arg in args {
                    self.on_pattern(arg);
                }
            }
            Pattern::Error => (),
        }
    }

    fn on_alias(&mut self, alias: &AliasData<Symbol, ArcType>) {
        // Insert variant constructors into the local scope
        let aliased_type = alias.unresolved_type();
        if let Type::Variant(ref row) = **aliased_type {
            for field in row.row_iter().cloned() {
                self.stack.insert(field.name.clone(), field.typ.clone());
                self.patterns.insert(field.name, field.typ);
            }
        }
    }

    fn expr(&mut self, expr: &SpannedExpr<Symbol>) {
        self.result.extend(
            expr_iter(&self.stack, expr).map(|(k, typ)| {

                Suggestion {
                    name: k.declared_name().into(),
                    typ: typ.clone(),
                }
            }),
        );
    }

    fn pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        let prefix = match pattern.value {
            Pattern::Constructor(ref id, _) |
            Pattern::Ident(ref id) => id.as_ref(),
            _ => "",
        };
        self.result.extend(
            self.patterns
                .iter()
                .filter(|&(ref name, _)| name.declared_name().starts_with(prefix))
                .map(|(name, typ)| {
                    Suggestion {
                        name: name.declared_name().into(),
                        typ: typ.clone(),
                    }
                }),
        );
    }

    fn ident(&mut self, context: &SpannedExpr<Symbol>, ident: &Symbol, _: &ArcType) {
        let iter = self.ident_iter(context, ident);
        self.result.extend(iter.into_iter().map(|(name, typ)| {
            Suggestion {
                name: name.declared_name().into(),
                typ: typ,
            }
        }));
    }

    fn nothing(&mut self) {
        self.result.extend(self.stack.iter().map(|(name, typ)| {
            Suggestion {
                name: name.declared_name().into(),
                typ: typ.clone(),
            }
        }));
    }

    fn nothing_pattern(&mut self) {
        self.result.extend(self.patterns.iter().map(|(name, typ)| {
            Suggestion {
                name: name.declared_name().into(),
                typ: typ.clone(),
            }
        }))
    }

    fn found(&self) -> bool {
        !self.result.is_empty()
    }
}

struct GetMetadata<'a> {
    env: &'a FnvMap<Symbol, Metadata>,
    result: Option<&'a Metadata>,
}

impl<'a> OnFound for GetMetadata<'a> {
    fn expr(&mut self, expr: &SpannedExpr<Symbol>) {
        if let Expr::Ident(ref id) = expr.value {
            self.result = self.env.get(&id.name);
        }
    }

    fn ident(&mut self, context: &SpannedExpr<Symbol>, id: &Symbol, _typ: &ArcType) {
        match context.value {
            Expr::Projection(ref expr, _, _) => {
                if let Expr::Ident(ref expr_id) = expr.value {
                    self.result = self.env.get(&expr_id.name).and_then(|metadata| {
                        metadata.module.get(id.as_ref())
                    });
                }
            }
            Expr::Infix(..) => {
                self.result = self.env.get(id);
            }
            _ => (),
        }
    }

    fn pattern(&mut self, _pattern: &SpannedPattern<Symbol>) {}


    fn nothing(&mut self) {}

    fn found(&self) -> bool {
        self.result.is_some()
    }
}

struct MetadataSuggest<'a, E> {
    env: &'a FnvMap<Symbol, Metadata>,
    suggest: Suggest<E>,
    ident: &'a str,
    result: Option<&'a Metadata>,
}

impl<'a, E: TypeEnv> OnFound for MetadataSuggest<'a, E> {
    fn on_ident(&mut self, ident: &TypedIdent) {
        self.suggest.on_ident(ident)
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        self.suggest.on_pattern(pattern)
    }

    fn expr(&mut self, expr: &SpannedExpr<Symbol>) {
        let suggestion = expr_iter(&self.suggest.stack, expr).find(|&(name, _)| {
            name.declared_name() == self.ident
        });
        if let Some((name, _)) = suggestion {
            self.result = self.env.get(name);
        }
    }

    fn ident(&mut self, context: &SpannedExpr<Symbol>, _: &Symbol, _typ: &ArcType) {
        match context.value {
            Expr::Projection(ref expr, _, _) => {
                if let Expr::Ident(ref expr_ident) = expr.value {
                    self.result = self.env.get(&expr_ident.name).and_then(|metadata| {
                        metadata.module.get(self.ident)
                    });
                }
            }
            _ => (),
        }
    }

    fn pattern(&mut self, _pattern: &SpannedPattern<Symbol>) {}

    fn nothing(&mut self) {
        self.result = self.suggest
            .stack
            .iter()
            .find(|&(ref name, _)| name.declared_name() == self.ident)
            .and_then(|t| self.env.get(t.0));
    }

    fn found(&self) -> bool {
        self.result.is_some()
    }
}

struct FindVisitor<F> {
    pos: BytePos,
    on_found: F,
}

impl<F> FindVisitor<F> {
    fn select_spanned<I, S, T>(&self, iter: I, mut span: S) -> (bool, Option<T>)
    where
        I: IntoIterator<Item = T>,
        S: FnMut(&T) -> Span<BytePos>,
    {
        let mut iter = iter.into_iter().peekable();
        let mut prev = None;
        loop {
            match iter.peek() {
                Some(expr) => {
                    match span(expr).containment(&self.pos) {
                        Ordering::Equal => {
                            break;
                        }
                        Ordering::Less if prev.is_some() => {
                            // Select the previous expression
                            return (true, prev);
                        }
                        _ => (),
                    }
                }
                None => return (true, prev),
            }
            prev = iter.next();
        }
        (false, iter.next())
    }
}

struct VisitUnExpanded<'e, F: 'e>(&'e mut FindVisitor<F>);

impl<'e, F> Visitor for VisitUnExpanded<'e, F>
where
    F: OnFound,
{
    type Ident = Symbol;

    fn visit_expr(&mut self, e: &SpannedExpr<Self::Ident>) {
        if !self.0.on_found.found() {
            if e.span.expansion_id == NO_EXPANSION {
                self.0.visit_expr(e);
            } else {
                match e.value {
                    Expr::TypeBindings(ref type_bindings, _) => {
                        for type_binding in type_bindings {
                            self.0.on_found.on_alias(&type_binding.alias.value);
                        }
                    }
                    _ => (),
                }
                walk_expr(self, e);
            }
        }
    }

    fn visit_pattern(&mut self, e: &SpannedPattern<Self::Ident>) {
        if e.span.expansion_id == NO_EXPANSION {
            self.0.visit_pattern(e);
        } else {
            // Add variables into scope
            self.0.on_found.on_pattern(e);
            walk_pattern(self, &e.value);
        }
    }
}

impl<F> FindVisitor<F>
where
    F: OnFound,
{
    fn visit_one<'e, I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'e SpannedExpr<Symbol>>,
    {
        let (_, expr) = self.select_spanned(iter, |e| e.span);
        self.visit_expr(expr.unwrap());
    }

    fn visit_pattern(&mut self, current: &SpannedPattern<Symbol>) {
        match current.value {
            Pattern::Constructor(ref id, ref args) => {
                let id_span = Span::new(
                    current.span.start,
                    current.span.start + BytePos::from(id.as_ref().len()),
                );
                if id_span.containment(&self.pos) == Ordering::Equal {
                    self.on_found.pattern(current);
                    return;
                }
                let (_, pattern) = self.select_spanned(args, |e| e.span);
                match pattern {
                    Some(pattern) => self.visit_pattern(pattern),
                    None => self.on_found.nothing_pattern(),
                }
            }
            Pattern::Record { ref fields, .. } => {
                let (_, field) = self.select_spanned(fields, |field| {
                    field.value.as_ref().map_or(current.span, |p| p.span)
                });
                if let Some(pattern) = field.and_then(|field| field.value.as_ref()) {
                    self.visit_pattern(pattern);
                }
            }
            Pattern::Tuple { ref elems, .. } => {
                let (_, field) = self.select_spanned(elems, |elem| elem.span);
                self.visit_pattern(field.unwrap());
            }
            Pattern::Ident(_) |
            Pattern::Error => {
                if current.span.containment(&self.pos) == Ordering::Equal {
                    self.on_found.pattern(current)
                } else {
                    self.on_found.nothing_pattern()
                }
            }
        }
    }

    fn visit_expr(&mut self, current: &SpannedExpr<Symbol>) {
        // When inside a macro expanded expression we do a exhaustive search for an unexpanded
        // expression
        if current.span.expansion_id != NO_EXPANSION {
            VisitUnExpanded(self).visit_expr(current);
            return;
        }
        match current.value {
            Expr::Ident(_) | Expr::Literal(_) => {
                if current.span.containment(&self.pos) == Ordering::Equal {
                    self.on_found.expr(current)
                } else {
                    self.on_found.nothing()
                }
            }
            Expr::App(ref func, ref args) => {
                self.visit_one(once(&**func).chain(args));
            }
            Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                self.visit_one([pred, if_true, if_false].iter().map(|x| &***x))
            }
            Expr::Match(ref expr, ref alts) => {
                let iter = once(Ok(&**expr)).chain(alts.iter().map(Err));
                let (_, sel) = self.select_spanned(iter, |x| match *x {
                    Ok(e) => e.span,
                    Err(alt) => Span::new(alt.pattern.span.start, alt.expr.span.end),
                });
                match sel.unwrap() {
                    Ok(expr) => self.visit_expr(expr),
                    Err(alt) => {
                        self.on_found.on_pattern(&alt.pattern);
                        let iter = [Ok(&alt.pattern), Err(&alt.expr)];
                        let (_, sel) = self.select_spanned(iter.iter().cloned(), |x| match *x {
                            Ok(p) => p.span,
                            Err(e) => e.span,
                        });
                        match sel.unwrap() {
                            Ok(pattern) => self.visit_pattern(pattern),
                            Err(expr) => self.visit_expr(expr),
                        }
                    }
                }
            }
            Expr::Infix(ref l, ref op, ref r) => {
                match (l.span.containment(&self.pos), r.span.containment(&self.pos)) {
                    (Ordering::Greater, Ordering::Less) => {
                        self.on_found.ident(current, &op.value.name, &op.value.typ)
                    }
                    (_, Ordering::Greater) |
                    (_, Ordering::Equal) => self.visit_expr(r),
                    _ => self.visit_expr(l),
                }
            }
            Expr::LetBindings(ref bindings, ref expr) => {
                for bind in bindings {
                    self.on_found.on_pattern(&bind.name);
                }
                match self.select_spanned(bindings, |b| b.expr.span) {
                    (false, Some(bind)) => {
                        for arg in &bind.args {
                            self.on_found.on_ident(arg);
                        }
                        self.visit_expr(&bind.expr)
                    }
                    _ => self.visit_expr(expr),
                }
            }
            Expr::TypeBindings(ref type_bindings, ref expr) => {
                for type_binding in type_bindings {
                    self.on_found.on_alias(&type_binding.alias.value);
                }
                self.visit_expr(expr)
            }
            Expr::Projection(ref expr, ref id, ref typ) => {
                if expr.span.containment(&self.pos) <= Ordering::Equal {
                    self.visit_expr(expr);
                } else {
                    self.on_found.ident(current, id, typ);
                }
            }
            Expr::Array(ref array) => self.visit_one(&array.exprs),
            Expr::Record { ref exprs, .. } => {
                let exprs = exprs.iter().filter_map(|tup| tup.value.as_ref());
                if let (_, Some(expr)) = self.select_spanned(exprs, |e| e.span) {
                    self.visit_expr(expr);
                }
            }
            Expr::Lambda(ref lambda) => {
                for arg in &lambda.args {
                    self.on_found.on_ident(arg);
                }
                self.visit_expr(&lambda.body)
            }
            Expr::Tuple { elems: ref exprs, .. } |
            Expr::Block(ref exprs) => self.visit_one(exprs),
            Expr::Error => (),
        };
    }
}

pub fn find<T>(env: &T, expr: &SpannedExpr<Symbol>, pos: BytePos) -> Result<ArcType, ()>
where
    T: TypeEnv,
{
    let mut visitor = FindVisitor {
        pos: pos,
        on_found: GetType {
            env: env,
            typ: None,
        },
    };
    visitor.visit_expr(expr);
    visitor.on_found.typ.ok_or(())
}

pub fn suggest<T>(env: &T, expr: &SpannedExpr<Symbol>, pos: BytePos) -> Vec<Suggestion>
where
    T: TypeEnv,
{
    let mut visitor = FindVisitor {
        pos: pos,
        on_found: Suggest {
            env: env,
            stack: ScopedMap::new(),
            patterns: ScopedMap::new(),
            result: Vec::new(),
        },
    };
    visitor.visit_expr(expr);
    visitor.on_found.result
}

pub fn get_metadata<'a>(
    env: &'a FnvMap<Symbol, Metadata>,
    expr: &SpannedExpr<Symbol>,
    pos: BytePos,
) -> Option<&'a Metadata> {
    let mut visitor = FindVisitor {
        pos: pos,
        on_found: GetMetadata {
            env: env,
            result: None,
        },
    };
    visitor.visit_expr(expr);
    visitor.on_found.result
}

pub fn suggest_metadata<'a, T>(
    env: &'a FnvMap<Symbol, Metadata>,
    type_env: &T,
    expr: &SpannedExpr<Symbol>,
    pos: BytePos,
    name: &'a str,
) -> Option<&'a Metadata>
where
    T: TypeEnv,
{
    let mut visitor = FindVisitor {
        pos: pos,
        on_found: MetadataSuggest {
            env: env,
            suggest: Suggest {
                env: type_env,
                stack: ScopedMap::new(),
                patterns: ScopedMap::new(),
                result: Vec::new(),
            },
            ident: name,
            result: None,
        },
    };
    visitor.visit_expr(expr);
    visitor.on_found.result
}
