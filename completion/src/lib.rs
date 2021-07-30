//! Primitive auto completion and type quering on ASTs
#![doc(html_root_url = "https://docs.rs/gluon_completion/0.17.2")] // # GLUON

extern crate gluon_base as base;

use std::{borrow::Cow, cmp::Ordering, iter::once, path::PathBuf, sync::Arc};

use codespan::ByteOffset;

use either::Either;

use crate::base::{
    ast::{
        self, walk_expr, walk_pattern, AstType, Expr, Pattern, PatternField, SpannedExpr,
        SpannedIdent, SpannedPattern, Typed, TypedIdent, Visitor,
    },
    filename_to_module,
    fnv::{FnvMap, FnvSet},
    kind::ArcKind,
    metadata::Metadata,
    pos::{self, BytePos, HasSpan, Span, Spanned},
    resolve,
    scoped_map::ScopedMap,
    symbol::{Name, Symbol, SymbolRef},
    types::{
        walk_type_, AliasData, ArcType, ControlVisitation, Generic, NullInterner, Type, TypeEnv,
        TypeExt,
    },
};

#[derive(Clone, Debug)]
pub struct Found<'a, 'ast> {
    pub match_: Option<Match<'a, 'ast>>,
    pub near_matches: Vec<Match<'a, 'ast>>,
    pub enclosing_matches: Vec<Match<'a, 'ast>>,
}

impl<'a, 'ast> Found<'a, 'ast> {
    fn enclosing_match(&self) -> &Match<'a, 'ast> {
        self.enclosing_matches.last().unwrap()
    }
}

#[derive(Clone, Debug)]
pub enum Match<'a, 'ast> {
    Expr(&'a SpannedExpr<'ast, Symbol>),
    Pattern(&'a SpannedPattern<'ast, Symbol>),
    Ident(Span<BytePos>, &'a Symbol, ArcType),
    Type(Span<BytePos>, &'a SymbolRef, ArcKind),
}

impl<'a, 'ast> Match<'a, 'ast> {
    pub fn span(&self) -> Span<BytePos> {
        match *self {
            Match::Expr(expr) => expr.span,
            Match::Pattern(pattern) => pattern.span,
            Match::Ident(span, ..) | Match::Type(span, ..) => span,
        }
    }
}

trait OnFound {
    fn on_ident(&mut self, ident: &TypedIdent) {
        let _ = ident;
    }

    fn on_type_ident(&mut self, ident: &Generic<Symbol>) {
        let _ = ident;
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        let _ = pattern;
    }

    fn on_alias(&mut self, alias: &AliasData<Symbol, ArcType>) {
        let _ = alias;
    }
}

impl OnFound for () {}

impl<'a, T> OnFound for &'a mut T
where
    T: OnFound + 'a,
{
    fn on_ident(&mut self, ident: &TypedIdent) {
        (**self).on_ident(ident)
    }

    fn on_type_ident(&mut self, ident: &Generic<Symbol>) {
        (**self).on_type_ident(ident)
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        (**self).on_pattern(pattern)
    }

    fn on_alias(&mut self, alias: &AliasData<Symbol, ArcType>) {
        (**self).on_alias(alias)
    }
}

#[derive(Debug, PartialEq)]
pub struct Suggestion {
    pub name: String,
    pub typ: Either<ArcKind, ArcType>,
}

struct Suggest<E> {
    env: E,
    stack: ScopedMap<Symbol, ArcType>,
    type_stack: ScopedMap<Symbol, ArcKind>,
    patterns: ScopedMap<Symbol, ArcType>,
}

impl<E> Suggest<E>
where
    E: TypeEnv<Type = ArcType>,
{
    fn new(env: E) -> Suggest<E> {
        Suggest {
            env,
            stack: ScopedMap::new(),
            type_stack: ScopedMap::new(),
            patterns: ScopedMap::new(),
        }
    }
}

impl<E> OnFound for Suggest<E>
where
    E: TypeEnv<Type = ArcType>,
{
    fn on_ident(&mut self, ident: &TypedIdent) {
        self.stack.insert(ident.name.clone(), ident.typ.clone());
    }

    fn on_type_ident(&mut self, gen: &Generic<Symbol>) {
        self.type_stack.insert(gen.id.clone(), gen.kind.clone());
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        match &pattern.value {
            Pattern::As(id, pat) => {
                self.stack.insert(
                    id.value.clone(),
                    pat.try_type_of(&self.env).unwrap_or_else(|_| Type::hole()),
                );
                self.on_pattern(pat);
            }
            Pattern::Ident(id) => {
                self.stack.insert(id.name.clone(), id.typ.clone());
            }
            Pattern::Record { typ, fields, .. } => {
                let unaliased =
                    resolve::remove_aliases(&self.env, NullInterner::new(), typ.clone());
                for field in &**fields {
                    match field {
                        PatternField::Type { name } => {
                            if let Some(field) = unaliased
                                .type_field_iter()
                                .find(|field| field.name.name_eq(&name.value))
                            {
                                self.on_alias(&field.typ);
                            }
                        }
                        PatternField::Value { name, value } => match value {
                            Some(ref value) => self.on_pattern(value),
                            None => {
                                let name = name.value.clone();
                                let typ = unaliased
                                    .row_iter()
                                    .find(|f| f.name.name_eq(&name))
                                    .map(|f| f.typ.clone())
                                    // If we did not find a matching field in the type, default to a
                                    // type hole so that the user at least gets completion on the name
                                    .unwrap_or_else(Type::hole);
                                self.stack.insert(name, typ);
                            }
                        },
                    }
                }
            }
            Pattern::Tuple { elems: args, .. } | Pattern::Constructor(_, args) => {
                for arg in &**args {
                    self.on_pattern(arg);
                }
            }
            Pattern::Literal(_) | Pattern::Error => (),
        }
    }

    fn on_alias(&mut self, alias: &AliasData<Symbol, ArcType>) {
        // Insert variant constructors into the local scope
        let aliased_type = alias.unresolved_type().remove_forall();
        if let Type::Variant(ref row) = **aliased_type {
            for field in row.row_iter().cloned() {
                self.stack.insert(field.name.clone(), field.typ.clone());
                self.patterns.insert(field.name, field.typ);
            }
        }
        self.type_stack.insert(
            alias.name.clone(),
            alias
                .unresolved_type()
                .kind(&Default::default())
                .into_owned(),
        );
    }
}

#[derive(Debug)]
enum MatchState<'a, 'ast> {
    NotFound,
    Empty,
    Found(Match<'a, 'ast>),
}

struct FindVisitor<'a, 'ast, F> {
    pos: BytePos,
    on_found: F,
    found: MatchState<'a, 'ast>,
    enclosing_matches: Vec<Match<'a, 'ast>>,
    near_matches: Vec<Match<'a, 'ast>>,

    /// The span of the currently inspected expression, used to determine if a position is in that
    /// expression or outside it (macro expanded)
    source_span: Span<BytePos>,
}

impl<'a, 'ast, F> FindVisitor<'a, 'ast, F> {
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
                    match span(expr).containment(self.pos) {
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

    fn is_macro_expanded(&self, span: Span<BytePos>) -> bool {
        span.start().0 == 0 || !self.source_span.contains(span)
    }
}

struct VisitUnExpanded<'a: 'e, 'e, 'ast, F: 'e>(&'e mut FindVisitor<'a, 'ast, F>);

impl<'a, 'e, 'ast, F> Visitor<'a, 'ast> for VisitUnExpanded<'a, 'e, 'ast, F>
where
    F: OnFound,
{
    type Ident = Symbol;

    fn visit_expr(&mut self, e: &'a SpannedExpr<'ast, Self::Ident>) {
        if let MatchState::NotFound = self.0.found {
            if !self.0.is_macro_expanded(e.span) {
                self.0.visit_expr(e);
            } else {
                match e.value {
                    Expr::TypeBindings(ref type_bindings, ref e) => {
                        for type_binding in &**type_bindings {
                            self.0.on_found.on_alias(
                                type_binding
                                    .finalized_alias
                                    .as_ref()
                                    .expect("ICE: Expected alias to be set"),
                            );
                        }
                        self.0.visit_expr(e);
                    }
                    Expr::LetBindings(ref bindings, ref e) => {
                        for binding in bindings {
                            self.0.on_found.on_pattern(&binding.name);
                        }
                        self.0.visit_expr(e);
                    }
                    _ => walk_expr(self, e),
                }
            }
        }
    }

    fn visit_pattern(&mut self, e: &'a SpannedPattern<'ast, Self::Ident>) {
        if !self.0.is_macro_expanded(e.span) {
            self.0.visit_pattern(e);
        } else {
            // Add variables into scope
            self.0.on_found.on_pattern(e);
            walk_pattern(self, &e.value);
        }
    }
}

enum Variant<'a, 'ast> {
    Pattern(&'a SpannedPattern<'ast, Symbol>),
    Ident(&'a SpannedIdent<Symbol>),
    FieldIdent(&'a Spanned<Symbol, BytePos>, &'a ArcType),
    Type(&'a AstType<'ast, Symbol>),
    Expr(&'a SpannedExpr<'ast, Symbol>),
}

impl<'a, 'ast, F> FindVisitor<'a, 'ast, F>
where
    F: OnFound,
{
    fn visit_one<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a SpannedExpr<'ast, Symbol>>,
    {
        let (_, expr) = self.select_spanned(iter, |e| e.span);
        self.visit_expr(expr.unwrap());
    }

    fn visit_any<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = Variant<'a, 'ast>>,
    {
        let (_, sel) = self.select_spanned(iter, |x| match *x {
            Variant::Pattern(p) => p.span,
            Variant::Ident(e) => e.span,
            Variant::FieldIdent(e, _) => e.span,
            Variant::Type(t) => t.span(),
            Variant::Expr(e) => e.span,
        });

        match sel {
            Some(sel) => match sel {
                Variant::Pattern(pattern) => self.visit_pattern(pattern),
                Variant::Ident(ident) => {
                    if ident.span.containment(self.pos) == Ordering::Equal {
                        self.found = MatchState::Found(Match::Ident(
                            ident.span,
                            &ident.value.name,
                            ident.value.typ.clone(),
                        ));
                    } else {
                        self.found = MatchState::Empty;
                    }
                }
                Variant::FieldIdent(ident, record_type) => {
                    if ident.span.containment(self.pos) == Ordering::Equal {
                        let record_type = resolve::remove_aliases(
                            &crate::base::ast::EmptyEnv::default(),
                            NullInterner::new(),
                            record_type.clone(),
                        );
                        let either = record_type
                            .row_iter()
                            .find(|field| field.name.name_eq(&ident.value))
                            .map(|field| Either::Left(field.typ.clone()))
                            .or_else(|| {
                                record_type
                                    .type_field_iter()
                                    .find(|field| field.name.name_eq(&ident.value))
                                    .map(|field| {
                                        Either::Right(
                                            field.typ.kind(&Default::default()).into_owned(),
                                        )
                                    })
                            })
                            .unwrap_or_else(|| Either::Left(Type::hole()));

                        self.found = MatchState::Found(match either {
                            Either::Left(typ) => Match::Ident(ident.span, &ident.value, typ),
                            Either::Right(kind) => Match::Type(ident.span, &ident.value, kind),
                        });
                    } else {
                        self.found = MatchState::Empty;
                    }
                }
                Variant::Type(t) => self.visit_ast_type(t),
                Variant::Expr(expr) => self.visit_expr(expr),
            },
            None => self.found = MatchState::Empty,
        }
    }

    fn visit_pattern(&mut self, current: &'a SpannedPattern<'ast, Symbol>) {
        if current.span.containment(self.pos) == Ordering::Equal {
            self.enclosing_matches.push(Match::Pattern(current));
        } else {
            self.near_matches.push(Match::Pattern(current));
        }

        match current.value {
            Pattern::As(_, ref pat) => self.visit_pattern(pat),
            Pattern::Constructor(ref id, ref args) => {
                let id_span = Span::new(
                    current.span.start(),
                    current.span.start() + ByteOffset::from(id.as_ref().len() as i64),
                );
                if id_span.containment(self.pos) == Ordering::Equal {
                    self.found = MatchState::Found(Match::Pattern(current));
                    return;
                }
                let (_, pattern) = self.select_spanned(&**args, |e| e.span);
                match pattern {
                    Some(pattern) => self.visit_pattern(pattern),
                    None => self.found = MatchState::Empty,
                }
            }
            Pattern::Record {
                ref typ,
                ref fields,
                ..
            } => {
                let (on_whitespace, selected) =
                    self.select_spanned(&**fields, |field| match field {
                        PatternField::Type { name } => name.span,
                        PatternField::Value { name, value } => Span::new(
                            name.span.start(),
                            value.as_ref().map_or(name.span.end(), |p| p.span.end()),
                        ),
                    });

                if on_whitespace {
                    self.found = MatchState::Empty;
                } else if let Some(either) = selected {
                    match either {
                        PatternField::Type { name } => {
                            if name.span.containment(self.pos) == Ordering::Equal {
                                let field_type = typ
                                    .type_field_iter()
                                    .find(|it| it.name.name_eq(&name.value))
                                    .map(|it| it.typ.as_type())
                                    .unwrap_or(typ);
                                self.found = MatchState::Found(Match::Ident(
                                    name.span,
                                    &name.value,
                                    field_type.clone(),
                                ));
                            } else {
                                self.found = MatchState::Empty;
                            }
                        }
                        PatternField::Value { name, value } => {
                            match (name.span.containment(self.pos), &value) {
                                (Ordering::Equal, _) => {
                                    let field_type = typ
                                        .row_iter()
                                        .find(|it| it.name.name_eq(&name.value))
                                        .map(|it| &it.typ)
                                        .unwrap_or(typ);
                                    self.found = MatchState::Found(Match::Ident(
                                        name.span,
                                        &name.value,
                                        field_type.clone(),
                                    ));
                                }
                                (Ordering::Greater, &Some(ref pattern)) => {
                                    self.visit_pattern(pattern)
                                }
                                _ => self.found = MatchState::Empty,
                            }
                        }
                    }
                } else {
                    self.found = MatchState::Empty;
                }
            }
            Pattern::Tuple { ref elems, .. } => {
                let (_, field) = self.select_spanned(&**elems, |elem| elem.span);
                self.visit_pattern(field.unwrap());
            }
            Pattern::Ident(_) | Pattern::Literal(_) | Pattern::Error => {
                self.found = if current.span.containment(self.pos) == Ordering::Equal {
                    MatchState::Found(Match::Pattern(current))
                } else {
                    MatchState::Empty
                };
            }
        }
    }

    fn visit_expr(&mut self, current: &'a SpannedExpr<'ast, Symbol>) {
        // When inside a macro expanded expression we do a exhaustive search for an unexpanded
        // expression
        if self.is_macro_expanded(current.span) {
            VisitUnExpanded(self).visit_expr(current);
            return;
        }

        if current.span.containment(self.pos) == Ordering::Equal {
            self.enclosing_matches.push(Match::Expr(current));
        } else {
            self.near_matches.push(Match::Expr(current));
        }

        match current.value {
            Expr::Ident(_) | Expr::Literal(_) => {
                self.found = if current.span.containment(self.pos) == Ordering::Equal {
                    MatchState::Found(Match::Expr(current))
                } else {
                    MatchState::Empty
                };
            }
            Expr::App {
                ref func, ref args, ..
            } => {
                self.visit_one(once(&**func).chain(&**args));
            }
            Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                self.visit_one([pred, if_true, if_false].iter().map(|x| &***x))
            }
            Expr::Match(ref expr, ref alts) => {
                let iter = once(Ok(&**expr)).chain(alts.iter().map(Err));
                let (_, sel) = self.select_spanned(iter, |x| match *x {
                    Ok(e) => e.span,
                    Err(alt) => Span::new(alt.pattern.span.start(), alt.expr.span.end()),
                });
                match sel.unwrap() {
                    Ok(expr) => {
                        self.enclosing_matches.push(Match::Expr(expr));
                        self.visit_expr(expr)
                    }
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
            Expr::Infix {
                ref lhs,
                ref op,
                ref rhs,
                ..
            } => match (
                lhs.span.containment(self.pos),
                rhs.span.containment(self.pos),
            ) {
                (Ordering::Greater, Ordering::Less) => {
                    self.found = MatchState::Found(Match::Ident(
                        op.span,
                        &op.value.name,
                        op.value.typ.clone(),
                    ));
                }
                (_, Ordering::Greater) | (_, Ordering::Equal) => self.visit_expr(rhs),
                _ => self.visit_expr(lhs),
            },
            Expr::LetBindings(ref bindings, ref expr) => {
                if bindings.is_recursive() {
                    for bind in bindings {
                        self.on_found.on_pattern(&bind.name);
                    }
                }
                match self.select_spanned(bindings, |b| {
                    Span::new(b.name.span.start(), b.expr.span.end())
                }) {
                    (false, Some(bind)) => {
                        for arg in &*bind.args {
                            self.on_found.on_ident(&arg.name.value);
                        }

                        let iter = once(Variant::Pattern(&bind.name))
                            .chain(bind.args.iter().map(|arg| Variant::Ident(&arg.name)))
                            .chain(bind.typ.iter().map(Variant::Type))
                            .chain(once(Variant::Expr(&bind.expr)));
                        self.visit_any(iter)
                    }
                    _ => {
                        if !bindings.is_recursive() {
                            for bind in bindings {
                                self.on_found.on_pattern(&bind.name);
                            }
                        }
                        self.visit_expr(expr)
                    }
                }
            }
            Expr::TypeBindings(ref type_bindings, ref expr) => {
                for type_binding in &**type_bindings {
                    self.on_found.on_alias(
                        type_binding
                            .finalized_alias
                            .as_ref()
                            .expect("ICE: Expected alias to be set"),
                    );
                }
                let iter = type_bindings
                    .iter()
                    .map(Either::Left)
                    .chain(Some(Either::Right(expr)));
                match self.select_spanned(iter, |x| x.either(|b| b.span(), |e| e.span)) {
                    (_, Some(either)) => match either {
                        Either::Left(bind) => {
                            if bind.name.span.containment(self.pos) == Ordering::Equal {
                                self.found = MatchState::Found(Match::Type(
                                    bind.name.span,
                                    &bind.alias.value.name,
                                    bind.alias.value.kind(&Default::default()).into_owned(),
                                ));
                            } else {
                                for param in bind.alias.value.params() {
                                    self.on_found.on_type_ident(param);
                                }
                                self.visit_ast_type(bind.alias.value.aliased_type())
                            }
                        }
                        Either::Right(expr) => self.visit_expr(expr),
                    },
                    _ => unreachable!(),
                }
            }
            Expr::Projection(ref expr, ref id, ref typ) => {
                if expr.span.containment(self.pos) <= Ordering::Equal {
                    self.visit_expr(expr);
                } else {
                    self.enclosing_matches.push(Match::Expr(current));
                    self.found = MatchState::Found(Match::Ident(current.span, id, typ.clone()));
                }
            }
            Expr::Array(ref array) => self.visit_one(&*array.exprs),
            Expr::Record {
                ref base,
                typ: ref record_type,
                ..
            } => {
                let iter = current
                    .value
                    .field_iter()
                    .flat_map(|either| {
                        either
                            .map_left(|field| once(Variant::FieldIdent(&field.name, record_type)))
                            .map_right(|field| {
                                once(Variant::FieldIdent(&field.name, record_type))
                                    .chain(field.value.as_ref().map(Variant::Expr))
                            })
                    })
                    .chain(base.as_ref().map(|base| Variant::Expr(base)));
                self.visit_any(iter)
            }
            Expr::Lambda(ref lambda) => {
                for arg in &*lambda.args {
                    self.on_found.on_ident(&arg.name.value);
                }

                let selection = self.select_spanned(&*lambda.args, |arg| arg.name.span);
                match selection {
                    (false, Some(arg)) => {
                        self.found = MatchState::Found(Match::Ident(
                            arg.name.span,
                            &arg.name.value.name,
                            arg.name.value.typ.clone(),
                        ));
                    }
                    _ => self.visit_expr(&lambda.body),
                }
            }
            Expr::Tuple {
                elems: ref exprs, ..
            }
            | Expr::Block(ref exprs) => {
                if exprs.is_empty() {
                    self.found = MatchState::Found(Match::Expr(current));
                } else {
                    self.visit_one(&**exprs)
                }
            }
            Expr::Do(ref do_expr) => {
                let iter = do_expr
                    .id
                    .as_ref()
                    .map(Either::Left)
                    .into_iter()
                    .chain(once(Either::Right(&do_expr.bound)))
                    .chain(once(Either::Right(&do_expr.body)));
                match self.select_spanned(iter, |x| x.either(|i| i.span, |e| e.span)) {
                    (_, Some(either)) => match either {
                        Either::Left(ident) => self.visit_pattern(ident),
                        Either::Right(expr) => self.visit_expr(expr),
                    },
                    _ => unreachable!(),
                }
            }
            Expr::MacroExpansion {
                ref replacement, ..
            } => self.visit_expr(replacement),
            Expr::Annotated(..) => unimplemented!(), // FIXME
            Expr::Error(..) => (),
        }
    }

    fn visit_ast_type(&mut self, typ: &'a AstType<'ast, Symbol>) {
        match **typ {
            // ExtendRow do not have spans set properly so recurse unconditionally
            Type::ExtendRow { .. } | Type::ExtendTypeRow { .. } => (),
            _ if typ.span().containment(self.pos) != Ordering::Equal => return,
            _ => (),
        }
        match **typ {
            Type::Ident(ref id) => {
                self.found = MatchState::Found(Match::Type(typ.span(), &id.name, id.typ.clone()));
            }

            Type::Builtin(ref builtin) => {
                self.found = MatchState::Found(Match::Type(
                    typ.span(),
                    builtin.symbol(),
                    typ.kind(&Default::default()).into_owned(),
                ));
            }

            Type::Generic(ref gen) => {
                self.found = MatchState::Found(Match::Type(typ.span(), &gen.id, gen.kind.clone()));
            }

            Type::Alias(ref alias) => {
                self.found = MatchState::Found(Match::Type(
                    typ.span(),
                    &alias.name,
                    typ.kind(&Default::default()).into_owned(),
                ));
            }

            Type::Forall(ref params, ref typ) => {
                for param in &**params {
                    self.on_found.on_type_ident(param);
                }

                self.visit_ast_type(typ);
            }

            _ => walk_type_(
                typ,
                &mut ControlVisitation(|typ: &'a AstType<'ast, Symbol>| self.visit_ast_type(typ)),
            ),
        }
    }
}

fn complete_at<'a, 'ast, F>(
    on_found: F,
    source_span: Span<BytePos>,
    expr: &'a SpannedExpr<'ast, Symbol>,
    pos: BytePos,
) -> Result<Found<'a, 'ast>, ()>
where
    F: OnFound,
{
    let mut visitor = FindVisitor {
        pos: pos,
        on_found: on_found,
        found: MatchState::NotFound,
        enclosing_matches: vec![Match::Expr(expr)],
        near_matches: vec![],
        source_span,
    };
    visitor.visit_expr(expr);
    let enclosing_matches = visitor.enclosing_matches;
    let near_matches = visitor.near_matches;
    match visitor.found {
        MatchState::Found(match_) => Ok(Found {
            match_: Some(match_),
            enclosing_matches,
            near_matches,
        }),
        MatchState::Empty => Ok(Found {
            match_: None,
            enclosing_matches,
            near_matches,
        }),
        MatchState::NotFound => Err(()),
    }
}

pub trait Extract<'a>: Sized {
    type Output;
    fn extract(self, found: &Found<'a, '_>) -> Result<Self::Output, ()>;
    fn match_extract(self, match_: &Match<'a, '_>) -> Result<Self::Output, ()>;
}

#[derive(Clone, Copy)]
pub struct TypeAt<'a> {
    pub env: &'a dyn TypeEnv<Type = ArcType>,
}
impl<'a> Extract<'a> for TypeAt<'a> {
    type Output = Either<ArcKind, ArcType>;
    fn extract(self, found: &Found<'a, '_>) -> Result<Self::Output, ()> {
        match found.match_ {
            Some(ref match_) => self.match_extract(match_),
            None => self.match_extract(found.enclosing_match()),
        }
    }

    fn match_extract(self, found: &Match) -> Result<Self::Output, ()> {
        Ok(match *found {
            Match::Expr(expr) => expr
                .try_type_of(self.env)
                .map(Either::Right)
                .map_err(|_| ())?,
            Match::Ident(_, _, ref typ) => Either::Right(typ.clone()),
            Match::Type(_, _, ref kind) => Either::Left(kind.clone()),
            Match::Pattern(pattern) => pattern
                .try_type_of(self.env)
                .map(Either::Right)
                .map_err(|_| ())?,
        })
    }
}

#[derive(Clone, Copy)]
pub struct IdentAt;
impl<'a> Extract<'a> for IdentAt {
    type Output = &'a SymbolRef;
    fn extract(self, found: &Found<'a, '_>) -> Result<Self::Output, ()> {
        match found.match_ {
            Some(ref match_) => self.match_extract(match_),
            None => self.match_extract(found.enclosing_match()),
        }
    }

    fn match_extract(self, found: &Match<'a, '_>) -> Result<Self::Output, ()> {
        Ok(match found {
            Match::Expr(Spanned {
                value: Expr::Ident(id),
                ..
            })
            | Match::Pattern(Spanned {
                value: Pattern::Ident(id),
                ..
            }) => &id.name,
            Match::Ident(_, id, _) => id,
            Match::Pattern(Spanned {
                value: Pattern::As(id, _),
                ..
            }) => &id.value,
            Match::Type(_, id, _) => id,
            _ => return Err(()),
        })
    }
}

#[derive(Copy, Clone)]
pub struct SpanAt;
impl<'a> Extract<'a> for SpanAt {
    type Output = Span<BytePos>;
    fn extract(self, found: &Found) -> Result<Self::Output, ()> {
        match found.match_ {
            Some(ref match_) => self.match_extract(match_),
            None => self.match_extract(found.enclosing_match()),
        }
    }

    fn match_extract(self, found: &Match) -> Result<Self::Output, ()> {
        Ok(found.span())
    }
}

macro_rules! tuple_extract {
    ($first: ident) => {
    };
    ($first: ident $($id: ident)+) => {
        tuple_extract_!{$first $($id)+}
        tuple_extract!{$($id)+}
    };
}

macro_rules! tuple_extract_ {
    ($($id: ident)*) => {
        #[allow(non_snake_case)]
        impl<'a, $($id : Extract<'a>),*> Extract<'a> for ( $($id),* ) {
            type Output = ( $($id::Output),* );
            fn extract(self, found: &Found<'a, '_>) -> Result<Self::Output, ()> {
                let ( $($id),* ) = self;
                Ok(( $( $id.extract(found)? ),* ))
            }
            fn match_extract(self, found: &Match<'a, '_>) -> Result<Self::Output, ()> {
                let ( $($id),* ) = self;
                Ok(( $( $id.match_extract(found)? ),* ))
            }
        }
    };
}

tuple_extract! {A B C D E F G H}

pub fn completion<'a, 'ast, T>(
    extract: T,
    source_span: Span<BytePos>,
    expr: &'a SpannedExpr<'ast, Symbol>,
    pos: BytePos,
) -> Result<T::Output, ()>
where
    T: Extract<'a>,
{
    let found = complete_at((), source_span, expr, pos)?;
    extract.extract(&found)
}

pub fn find<'ast, T>(
    env: &T,
    source_span: Span<BytePos>,
    expr: &SpannedExpr<'ast, Symbol>,
    pos: BytePos,
) -> Result<Either<ArcKind, ArcType>, ()>
where
    T: TypeEnv<Type = ArcType>,
{
    let extract = TypeAt { env };
    completion(extract, source_span, expr, pos)
}

pub fn find_all_symbols<'ast>(
    source_span: Span<BytePos>,
    expr: &SpannedExpr<'ast, Symbol>,
    pos: BytePos,
) -> Result<(String, Vec<Span<BytePos>>), ()> {
    let extract = IdentAt;
    completion(extract, source_span, expr, pos).map(|symbol| {
        struct ExtractIdents<'b> {
            result: Vec<Span<BytePos>>,
            symbol: &'b SymbolRef,
        }
        impl<'a, 'b> Visitor<'a, '_> for ExtractIdents<'b> {
            type Ident = Symbol;

            fn visit_expr(&mut self, e: &'a SpannedExpr<Self::Ident>) {
                match e.value {
                    Expr::Ident(ref id) if id.name == *self.symbol => {
                        self.result.push(e.span);
                    }
                    _ => walk_expr(self, e),
                }
            }

            fn visit_pattern(&mut self, p: &'a SpannedPattern<Self::Ident>) {
                match p.value {
                    Pattern::As(ref id, ref pat) if id.value == *self.symbol => {
                        self.result.push(p.span);
                        walk_pattern(self, &pat.value);
                    }
                    Pattern::Ident(ref id) if id.name == *self.symbol => {
                        self.result.push(p.span);
                    }
                    _ => walk_pattern(self, &p.value),
                }
            }
        }
        let mut visitor = ExtractIdents {
            result: Vec::new(),
            symbol,
        };
        visitor.visit_expr(expr);
        (visitor.symbol.declared_name().to_string(), visitor.result)
    })
}

pub fn symbol<'a, 'ast>(
    source_span: Span<BytePos>,
    expr: &'a SpannedExpr<'ast, Symbol>,
    pos: BytePos,
) -> Result<&'a SymbolRef, ()> {
    let extract = IdentAt;
    completion(extract, source_span, expr, pos)
}

pub type SpCompletionSymbol<'a, 'ast> = Spanned<CompletionSymbol<'a, 'ast>, BytePos>;

#[derive(Debug, PartialEq)]
pub struct CompletionSymbol<'a, 'ast> {
    pub name: &'a Symbol,
    pub content: CompletionSymbolContent<'a, 'ast>,
    pub children: Vec<SpCompletionSymbol<'a, 'ast>>,
}

#[derive(Debug, PartialEq)]
pub enum CompletionValueKind {
    Parameter,
    Binding,
}

#[derive(Debug, PartialEq)]
pub enum CompletionSymbolContent<'a, 'ast> {
    Value {
        typ: &'a ArcType,
        kind: CompletionValueKind,
        expr: Option<&'a SpannedExpr<'ast, Symbol>>,
    },
    Type {
        typ: &'a AstType<'ast, Symbol>,
    },
}

pub fn all_symbols<'a, 'ast>(
    source_span: Span<BytePos>,
    expr: &'a SpannedExpr<'ast, Symbol>,
) -> Vec<SpCompletionSymbol<'a, 'ast>> {
    struct AllIdents<'r, 'a, 'ast> {
        source_span: Span<BytePos>,
        result: &'r mut Vec<Spanned<CompletionSymbol<'a, 'ast>, BytePos>>,
    }

    impl<'a, 'ast> Visitor<'a, 'ast> for AllIdents<'_, 'a, 'ast> {
        type Ident = Symbol;

        fn visit_ast_type(&mut self, typ: &'a ast::AstType<'ast, Self::Ident>) {
            match &**typ {
                Type::Record(_) | Type::Variant(_) | Type::Effect(_) => {
                    for field in base::types::row_iter(typ) {
                        let mut children = Vec::new();
                        idents_of(self.source_span, &field.typ, &mut children);
                        self.result.push(pos::spanned(
                            field.name.span,
                            CompletionSymbol {
                                name: &field.name.value,
                                content: CompletionSymbolContent::Type { typ: &field.typ },
                                children,
                            },
                        ));
                    }
                }
                _ => ast::walk_ast_type(self, typ),
            }
        }

        fn visit_expr(&mut self, e: &'a SpannedExpr<'ast, Self::Ident>) {
            if self.source_span.contains(e.span) {
                let source_span = self.source_span;
                match &e.value {
                    Expr::TypeBindings(binds, expr) => {
                        self.result.extend(binds.iter().map(|bind| {
                            let mut children = Vec::new();
                            idents_of(source_span, &bind.alias, &mut children);

                            pos::spanned(
                                bind.name.span,
                                CompletionSymbol {
                                    name: bind
                                        .finalized_alias
                                        .as_ref()
                                        .map(|alias| &alias.name)
                                        .unwrap_or(&bind.name.value),
                                    content: CompletionSymbolContent::Type {
                                        typ: &bind.alias.unresolved_type(),
                                    },
                                    children,
                                },
                            )
                        }));

                        self.visit_expr(expr);
                    }
                    Expr::LetBindings(binds, expr) => {
                        for bind in binds {
                            let mut children = Vec::new();

                            children.extend(bind.args.iter().map(|arg| {
                                pos::spanned(
                                    arg.name.span,
                                    CompletionSymbol {
                                        name: &arg.name.value.name,
                                        content: CompletionSymbolContent::Value {
                                            typ: &arg.name.value.typ,
                                            kind: CompletionValueKind::Parameter,
                                            expr: None,
                                        },
                                        children: Vec::new(),
                                    },
                                )
                            }));

                            idents_of(source_span, &bind.expr, &mut children);

                            match &bind.name.value {
                                Pattern::Ident(id) => {
                                    self.result.push(pos::spanned(
                                        bind.name.span,
                                        CompletionSymbol {
                                            name: &id.name,
                                            content: CompletionSymbolContent::Value {
                                                typ: &id.typ,
                                                kind: CompletionValueKind::Binding,
                                                expr: Some(&bind.expr),
                                            },
                                            children,
                                        },
                                    ));
                                }
                                _ => self.result.extend(children),
                            }
                        }

                        self.visit_expr(expr);
                    }
                    _ => walk_expr(self, e),
                }
            } else {
                walk_expr(self, e);
            }
        }
    }

    trait Visit<'a, 'ast> {
        type Ident: 'a + 'ast;
        fn visit(&'a self, visitor: &mut impl Visitor<'a, 'ast, Ident = Self::Ident>);
    }

    impl<'a, 'ast, I> Visit<'a, 'ast> for SpannedExpr<'ast, I>
    where
        I: 'a + 'ast,
    {
        type Ident = I;
        fn visit(&'a self, visitor: &mut impl Visitor<'a, 'ast, Ident = Self::Ident>) {
            visitor.visit_expr(self)
        }
    }

    impl<'a, 'ast, I> Visit<'a, 'ast> for ArcType<I>
    where
        I: 'a + 'ast,
    {
        type Ident = I;
        fn visit(&'a self, visitor: &mut impl Visitor<'a, 'ast, Ident = Self::Ident>) {
            visitor.visit_typ(self)
        }
    }

    impl<'a, 'ast, I> Visit<'a, 'ast> for ast::AstType<'ast, I>
    where
        I: 'a + 'ast,
    {
        type Ident = I;
        fn visit(&'a self, visitor: &mut impl Visitor<'a, 'ast, Ident = Self::Ident>) {
            visitor.visit_ast_type(self)
        }
    }

    impl<'a, 'ast, I> Visit<'a, 'ast> for ast::SpannedAlias<'ast, I>
    where
        I: 'a + 'ast,
    {
        type Ident = I;
        fn visit(&'a self, visitor: &mut impl Visitor<'a, 'ast, Ident = Self::Ident>) {
            visitor.visit_alias(self)
        }
    }

    fn idents_of<'a, 'ast>(
        source_span: Span<BytePos>,
        v: &'a impl Visit<'a, 'ast, Ident = Symbol>,
        result: &mut Vec<Spanned<CompletionSymbol<'a, 'ast>, BytePos>>,
    ) {
        let mut visitor = AllIdents {
            source_span,
            result,
        };
        v.visit(&mut visitor)
    }

    let mut result = Vec::new();
    idents_of(source_span, expr, &mut result);
    result
}

pub fn suggest<'ast, T>(
    env: &T,
    source_span: Span<BytePos>,
    expr: &SpannedExpr<'ast, Symbol>,
    pos: BytePos,
) -> Vec<Suggestion>
where
    T: TypeEnv<Type = ArcType>,
{
    SuggestionQuery::default().suggest(env, source_span, expr, pos)
}

pub struct SuggestionQuery {
    pub paths: Vec<PathBuf>,
    pub modules: Vec<Cow<'static, str>>,
    pub prefix_filter: bool,
    pub span: Option<Span<BytePos>>,
}

impl Default for SuggestionQuery {
    fn default() -> Self {
        SuggestionQuery {
            paths: Vec::new(),
            modules: Vec::new(),
            prefix_filter: true,
            span: None,
        }
    }
}

impl SuggestionQuery {
    pub fn new() -> Self {
        Self::default()
    }

    fn filter(&self, name: &str, prefix: &str) -> bool {
        !self.prefix_filter || name.starts_with(prefix)
    }

    fn suggest_fields_of_type(
        &self,
        result: &mut Vec<Suggestion>,
        fields: &[PatternField<'_, Symbol>],
        prefix: &str,
        typ: &ArcType,
    ) {
        let existing_fields: FnvSet<&str> = ast::pattern_names(fields)
            .map(|name| name.value.as_ref())
            .collect();

        let should_suggest = |name: &str| {
            // Filter out fields that has already been defined in the pattern
            (!existing_fields.contains(name) && self.filter(name, prefix))
                // But keep exact matches to keep that suggestion when the user has typed a whole
                // field
                || name == prefix
        };

        let fields = typ
            .row_iter()
            .filter(|field| should_suggest(field.name.declared_name()))
            .map(|field| Suggestion {
                name: field.name.declared_name().into(),
                typ: Either::Right(field.typ.clone()),
            });
        let types = typ
            .type_field_iter()
            .filter(|field| should_suggest(field.name.declared_name()))
            .map(|field| Suggestion {
                name: field.name.declared_name().into(),
                typ: Either::Right(field.typ.clone().into_type()),
            });
        result.extend(fields.chain(types));
    }

    fn expr_iter<'e, 'ast>(
        &'e self,
        stack: &'e ScopedMap<Symbol, ArcType>,
        expr: &'e SpannedExpr<'ast, Symbol>,
    ) -> impl Iterator<Item = (&'e Symbol, &'e ArcType)> {
        if let Expr::Ident(ref ident) = expr.value {
            Either::Left(
                stack.iter().filter(move |&(k, _)| {
                    self.filter(k.declared_name(), ident.name.declared_name())
                }),
            )
        } else {
            Either::Right(None.into_iter())
        }
    }

    pub fn suggest<'ast, T>(
        &self,
        env: &T,
        source_span: Span<BytePos>,
        expr: &SpannedExpr<'ast, Symbol>,
        pos: BytePos,
    ) -> Vec<Suggestion>
    where
        T: TypeEnv<Type = ArcType>,
    {
        let mut suggest = Suggest::new(env);

        let found = match complete_at(&mut suggest, source_span, expr, pos) {
            Ok(x) => x,
            Err(()) => return vec![],
        };
        let mut result = vec![];

        let enclosing_match = found.enclosing_matches.last().unwrap();
        match found.match_ {
            Some(match_) => match match_ {
                Match::Expr(expr) => match expr.value {
                    Expr::Ident(ref id) if id.name.is_global() => {
                        let name = id.name.definition_name();
                        self.suggest_module_import(env, name, &mut result);
                    }
                    Expr::Ident(ref id) => {
                        self.suggest_local(
                            &mut result,
                            &suggest,
                            &enclosing_match,
                            id.name.declared_name(),
                        );
                    }
                    _ => self.suggest_local(&mut result, &suggest, &enclosing_match, ""),
                },

                Match::Pattern(pattern) => {
                    let prefix = match pattern.value {
                        Pattern::Constructor(ref id, _) | Pattern::Ident(ref id) => id.as_ref(),
                        Pattern::Record { ref fields, .. } => {
                            if let Ok(typ) = expr.try_type_of(&env) {
                                let typ = resolve::remove_aliases(env, NullInterner::new(), typ);
                                self.suggest_fields_of_type(&mut result, fields, "", &typ);
                            }
                            ""
                        }
                        _ => "",
                    };
                    result.extend(
                        suggest
                            .patterns
                            .iter()
                            .filter(|&(name, _)| self.filter(name.declared_name(), prefix))
                            .map(|(name, typ)| Suggestion {
                                name: name.declared_name().into(),
                                typ: Either::Right(typ.clone()),
                            }),
                    );
                }
                Match::Ident(_, ident, _) => match *enclosing_match {
                    Match::Expr(context) => match context.value {
                        Expr::Projection(ref expr, _, _) => {
                            if let Ok(typ) = expr.try_type_of(&env) {
                                let typ = resolve::remove_aliases(&env, NullInterner::new(), typ);
                                let id = ident.as_ref();

                                let iter = typ
                                    .row_iter()
                                    .filter(move |field| self.filter(field.name.as_ref(), id))
                                    .map(|field| (field.name.clone(), field.typ.clone()));
                                result.extend(iter.map(|(name, typ)| Suggestion {
                                    name: name.declared_name().into(),
                                    typ: Either::Right(typ),
                                }));
                            }
                        }
                        Expr::Ident(ref id) if id.name.is_global() => {
                            self.suggest_module_import(env, id.name.as_pretty_str(), &mut result);
                        }
                        _ => {
                            self.suggest_local(
                                &mut result,
                                &suggest,
                                enclosing_match,
                                ident.declared_name(),
                            );

                            if let Expr::Record { .. } = context.value {
                                self.suggest_local_type(
                                    &mut result,
                                    &suggest,
                                    enclosing_match,
                                    ident.declared_name(),
                                );
                            }
                        }
                    },
                    Match::Pattern(&Spanned {
                        value:
                            Pattern::Record {
                                ref typ,
                                ref fields,
                                ..
                            },
                        ..
                    }) => {
                        let typ = resolve::remove_aliases_cow(env, NullInterner::new(), typ);
                        self.suggest_fields_of_type(
                            &mut result,
                            fields,
                            ident.declared_name(),
                            &typ,
                        );
                    }
                    _ => (),
                },

                Match::Type(_, ident, _) => self.suggest_local_type(
                    &mut result,
                    &suggest,
                    enclosing_match,
                    ident.declared_name(),
                ),
            },

            None => match *enclosing_match {
                Match::Expr(..) | Match::Ident(..) => {
                    self.suggest_local(&mut result, &suggest, &enclosing_match, "");
                    if let Match::Expr(Spanned {
                        value: Expr::Record { .. },
                        ..
                    }) = *enclosing_match
                    {
                        self.suggest_local_type(&mut result, &suggest, enclosing_match, "");
                    }
                }

                Match::Type(_, ident, _) => self.suggest_local_type(
                    &mut result,
                    &suggest,
                    enclosing_match,
                    ident.declared_name(),
                ),

                Match::Pattern(pattern) => match pattern.value {
                    Pattern::Record { ref fields, .. } => {
                        if let Ok(typ) = pattern.try_type_of(env) {
                            let typ = resolve::remove_aliases(env, NullInterner::new(), typ);
                            self.suggest_fields_of_type(&mut result, fields, "", &typ);
                        }
                    }
                    _ => result.extend(suggest.patterns.iter().map(|(name, typ)| Suggestion {
                        name: name.declared_name().into(),
                        typ: Either::Right(typ.clone()),
                    })),
                },
            },
        }
        result
    }

    fn suggest_local<T>(
        &self,
        result: &mut Vec<Suggestion>,
        suggest: &Suggest<T>,
        context: &Match,
        ident: &str,
    ) where
        T: TypeEnv<Type = ArcType>,
    {
        result.extend(
            suggest
                .stack
                .iter()
                .filter(move |&(k, _)| self.filter(k.declared_name(), ident))
                .filter(|&(k, _)| match context {
                    // If inside a record expression, remove any fields that have already been used
                    Match::Expr(&Spanned {
                        value:
                            Expr::Record {
                                ref types,
                                ref exprs,
                                ..
                            },
                        ..
                    }) => exprs
                        .iter()
                        .map(|field| &field.name)
                        .chain(types.iter().map(|field| &field.name))
                        .all(|already_used_field| already_used_field.value != *k),
                    _ => true,
                })
                .map(|(k, typ)| Suggestion {
                    name: k.declared_name().into(),
                    typ: Either::Right(typ.clone()),
                }),
        )
    }

    fn suggest_local_type<T>(
        &self,
        result: &mut Vec<Suggestion>,
        suggest: &Suggest<T>,
        context: &Match,
        ident: &str,
    ) where
        T: TypeEnv<Type = ArcType>,
    {
        result.extend(
            suggest
                .type_stack
                .iter()
                .filter(|&(k, _)| self.filter(k.declared_name(), ident))
                .filter(|&(k, _)| match context {
                    // If inside a record expression, remove any fields that have already been used
                    Match::Expr(&Spanned {
                        value:
                            Expr::Record {
                                ref types,
                                ref exprs,
                                ..
                            },
                        ..
                    }) => exprs
                        .iter()
                        .map(|field| &field.name)
                        .chain(types.iter().map(|field| &field.name))
                        .all(|already_used_field| already_used_field.value != *k),
                    _ => true,
                })
                .map(|(name, kind)| Suggestion {
                    name: name.declared_name().into(),
                    typ: Either::Left(kind.clone()),
                }),
        );
    }

    fn suggest_module_import<T>(&self, env: &T, path: &str, suggestions: &mut Vec<Suggestion>)
    where
        T: TypeEnv<Type = ArcType>,
    {
        use std::ffi::OsStr;
        let path = Name::new(path);

        let base = PathBuf::from(path.module().as_str().replace(".", "/"));

        let modules = self
            .paths
            .iter()
            .flat_map(|root| {
                let walk_root = root.join(&*base);
                walkdir::WalkDir::new(walk_root)
                    .into_iter()
                    .filter_map(|entry| entry.ok())
                    .filter_map(move |entry| {
                        if entry.file_type().is_file()
                            && entry.path().extension() == Some(OsStr::new("glu"))
                        {
                            let unprefixed_file = entry
                                .path()
                                .strip_prefix(&*root)
                                .expect("Root is not a prefix of path from walk_dir");
                            unprefixed_file.to_str().map(filename_to_module)
                        } else {
                            None
                        }
                    })
            })
            .collect::<Vec<String>>();

        suggestions.extend(
            modules
                .iter()
                .map(|s| &s[..])
                .chain(self.modules.iter().map(|s| &s[..]))
                .filter(|module| self.filter(module, path.as_str()))
                .map(|module| {
                    let name = module[path.module().as_str().len()..]
                        .trim_start_matches('.')
                        .split('.')
                        .next()
                        .unwrap()
                        .to_string();
                    Suggestion {
                        name,
                        typ: Either::Right(
                            env.find_type(SymbolRef::new(module))
                                .unwrap_or_else(Type::hole),
                        ),
                    }
                }),
        );

        suggestions.sort_by(|l, r| l.name.cmp(&r.name));
        suggestions.dedup_by(|l, r| l.name == r.name);
    }

    pub fn suggest_metadata<'a, 'b, 'ast, T>(
        &self,
        env: &'a FnvMap<Symbol, Arc<Metadata>>,
        type_env: &T,
        source_span: Span<BytePos>,
        expr: &'b SpannedExpr<'ast, Symbol>,
        pos: BytePos,
        name: &str,
    ) -> Option<&'a Metadata>
    where
        T: TypeEnv<Type = ArcType>,
    {
        let mut suggest = Suggest::new(type_env);
        complete_at(&mut suggest, source_span, expr, pos)
            .ok()
            .and_then(|found| {
                let enclosing_match = found.enclosing_matches.last().unwrap();
                match found.match_ {
                    Some(match_) => match match_ {
                        Match::Expr(expr) => {
                            let suggestion = self
                                .expr_iter(&suggest.stack, expr)
                                .find(|&(stack_name, _)| stack_name.declared_name() == name);
                            if let Some((name, _)) = suggestion {
                                env.get(name)
                            } else {
                                None
                            }
                        }

                        Match::Ident(_, _, _) => match *enclosing_match {
                            Match::Expr(&Spanned {
                                value: Expr::Projection(ref expr, _, _),
                                ..
                            }) => {
                                if let Expr::Ident(ref expr_ident) = expr.value {
                                    env.get(&expr_ident.name)
                                        .and_then(|metadata| metadata.module.get(name))
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        },
                        _ => None,
                    },

                    None => match *enclosing_match {
                        Match::Expr(..) | Match::Ident(..) => suggest
                            .stack
                            .iter()
                            .find(|&(stack_name, _)| stack_name.declared_name() == name)
                            .and_then(|t| env.get(t.0)),

                        _ => None,
                    },
                }
            })
            .map(|m| &**m)
    }
}

#[derive(Debug, PartialEq)]
pub struct SignatureHelp {
    pub name: String,
    pub typ: ArcType,
    pub index: Option<u32>,
}

pub fn signature_help<'ast>(
    env: &dyn TypeEnv<Type = ArcType>,
    source_span: Span<BytePos>,
    expr: &SpannedExpr<'ast, Symbol>,
    pos: BytePos,
) -> Option<SignatureHelp> {
    complete_at((), source_span, expr, pos)
        .ok()
        .and_then(|found| {
            let applications = found
                .enclosing_matches
                .iter()
                .chain(&found.near_matches)
                .rev()
                // Stop searching for an application if it would mean we exit a nested expression
                // Ie. `test { abc = func }`
                //                     ^
                // Should not return the signature for `test` but for `func`
                .take_while(|enclosing_match| match **enclosing_match {
                    Match::Expr(expr) => match expr.value {
                        Expr::Ident(..)
                        | Expr::Literal(..)
                        | Expr::Projection(..)
                        | Expr::App { .. }
                        | Expr::Tuple { .. } => true,
                        Expr::Record {
                            ref exprs,
                            ref base,
                            ..
                        } => exprs.is_empty() && base.is_none(),
                        _ => false,
                    },
                    _ => false,
                })
                .filter_map(|enclosing_match| match *enclosing_match {
                    Match::Expr(expr) => match expr.value {
                        Expr::App {
                            ref func, ref args, ..
                        } => func.try_type_of(env).ok().map(|typ| {
                            let name = match func.value {
                                Expr::Ident(ref id) => id.name.declared_name().to_string(),
                                Expr::Projection(_, ref name, _) => {
                                    name.declared_name().to_string()
                                }
                                _ => "".to_string(),
                            };
                            let index = if args.first().map_or(false, |arg| pos >= arg.span.start())
                            {
                                Some(
                                    args.iter()
                                        .position(|arg| pos <= arg.span.end())
                                        .unwrap_or_else(|| args.len())
                                        as u32,
                                )
                            } else {
                                None
                            };
                            SignatureHelp { name, typ, index }
                        }),
                        _ => None,
                    },
                    _ => None,
                });
            let any_expr = found
                .enclosing_matches
                .iter()
                .chain(&found.near_matches)
                .rev()
                .filter_map(|enclosing_match| match *enclosing_match {
                    Match::Expr(expr) => {
                        let name = match expr.value {
                            Expr::Ident(ref id) => id.name.declared_name().to_string(),
                            Expr::Projection(_, ref name, _) => name.declared_name().to_string(),
                            _ => "".to_string(),
                        };

                        expr.value.try_type_of(env).ok().map(|typ| SignatureHelp {
                            name,
                            typ,
                            index: if pos > expr.span.end() { Some(0) } else { None },
                        })
                    }
                    _ => None,
                });
            applications.chain(any_expr).next()
        })
}

pub fn get_metadata<'a, 'ast>(
    env: &'a FnvMap<Symbol, Arc<Metadata>>,
    source_span: Span<BytePos>,
    expr: &'a SpannedExpr<'ast, Symbol>,
    pos: BytePos,
) -> Option<&'a Metadata> {
    complete_at((), source_span, expr, pos)
        .ok()
        .and_then(|found| {
            let e = found.enclosing_match().clone();
            found.match_.map(|m| (m, e))
        })
        .and_then(|(match_, enclosing_match)| match match_ {
            Match::Expr(expr) => {
                if let Expr::Ident(ref id) = expr.value {
                    env.get(&id.name)
                } else {
                    None
                }
            }
            Match::Ident(_, id, _typ) => match enclosing_match {
                Match::Expr(&Spanned {
                    value: Expr::Projection(ref expr, _, _),
                    ..
                }) => {
                    if let Expr::Ident(ref expr_id) = expr.value {
                        env.get(&expr_id.name)
                            .and_then(|metadata| metadata.module.get(id.as_str()))
                    } else {
                        None
                    }
                }
                Match::Expr(&Spanned {
                    value: Expr::Infix { .. },
                    ..
                }) => env.get(id),
                _ => env.get(id),
            },
            _ => None,
        })
        .map(|m| &**m)
}

pub fn suggest_metadata<'a, 'ast, T>(
    env: &'a FnvMap<Symbol, Arc<Metadata>>,
    type_env: &T,
    source_span: Span<BytePos>,
    expr: &'a SpannedExpr<'ast, Symbol>,
    pos: BytePos,
    name: &'a str,
) -> Option<&'a Metadata>
where
    T: TypeEnv<Type = ArcType>,
{
    SuggestionQuery::new().suggest_metadata(env, type_env, source_span, expr, pos, name)
}
