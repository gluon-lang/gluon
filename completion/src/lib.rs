//! Primitive auto completion and type quering on ASTs
#![doc(html_root_url = "https://docs.rs/gluon_completion/0.6.2")] // # GLUON

extern crate either;

extern crate gluon_base as base;

use std::iter::once;
use std::cmp::Ordering;

use either::Either;

use base::ast::{walk_expr, walk_pattern, AstType, Expr, Pattern, SpannedExpr, SpannedIdent,
                SpannedPattern, Typed, TypedIdent, Visitor};
use base::fnv::FnvMap;
use base::kind::{ArcKind, Kind};
use base::metadata::Metadata;
use base::resolve;
use base::pos::{self, BytePos, HasSpan, Span, Spanned, NO_EXPANSION};
use base::scoped_map::ScopedMap;
use base::symbol::Symbol;
use base::types::{walk_type_, AliasData, ArcType, ControlVisitation, Generic, Type, TypeEnv};

pub struct Found<'a> {
    pub match_: Option<Match<'a>>,
    pub enclosing_match: Match<'a>,
}

#[derive(Clone)]
pub enum Match<'a> {
    Expr(&'a SpannedExpr<Symbol>),
    Pattern(&'a SpannedPattern<Symbol>),
    Ident(Span<BytePos>, &'a Symbol, &'a ArcType),
    Type(Span<BytePos>, &'a Symbol, ArcKind),
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
    fn new(env: E) -> Suggest<E> {
        Suggest {
            env,
            stack: ScopedMap::new(),
            type_stack: ScopedMap::new(),
            patterns: ScopedMap::new(),
        }
    }

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

    fn on_type_ident(&mut self, gen: &Generic<Symbol>) {
        self.type_stack.insert(gen.id.clone(), gen.kind.clone());
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<Symbol>) {
        match pattern.value {
            Pattern::As(_, ref pat) => {
                self.on_pattern(pat);
            }
            Pattern::Ident(ref id) => {
                self.stack.insert(id.name.clone(), id.typ.clone());
            }
            Pattern::Record {
                ref typ,
                fields: ref field_ids,
                ref types,
                ..
            } => {
                let unaliased = resolve::remove_aliases(&self.env, typ.clone());
                for ast_field in types {
                    if let Some(field) = unaliased
                        .type_field_iter()
                        .find(|field| field.name == ast_field.name.value)
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
            Pattern::Tuple {
                elems: ref args, ..
            } |
            Pattern::Constructor(_, ref args) => for arg in args {
                self.on_pattern(arg);
            },
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
        self.type_stack.insert(
            alias.name.clone(),
            alias.unresolved_type().kind().into_owned(),
        );
    }
}

struct FindVisitor<'a, F> {
    pos: BytePos,
    on_found: F,
    found: Option<Option<Match<'a>>>,
    enclosing_match: Match<'a>,
}

impl<'a, F> FindVisitor<'a, F> {
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

struct VisitUnExpanded<'a: 'e, 'e, F: 'e>(&'e mut FindVisitor<'a, F>);

impl<'a, 'e, F> Visitor<'a> for VisitUnExpanded<'a, 'e, F>
where
    F: OnFound,
{
    type Ident = Symbol;

    fn visit_expr(&mut self, e: &'a SpannedExpr<Self::Ident>) {
        if self.0.found.is_none() {
            if e.span.expansion_id == NO_EXPANSION {
                self.0.visit_expr(e);
            } else {
                match e.value {
                    Expr::TypeBindings(ref type_bindings, ref e) => {
                        for type_binding in type_bindings {
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

    fn visit_pattern(&mut self, e: &'a SpannedPattern<Self::Ident>) {
        if e.span.expansion_id == NO_EXPANSION {
            self.0.visit_pattern(e);
        } else {
            // Add variables into scope
            self.0.on_found.on_pattern(e);
            walk_pattern(self, &e.value);
        }
    }
}

impl<'a, F> FindVisitor<'a, F>
where
    F: OnFound,
{
    fn visit_one<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a SpannedExpr<Symbol>>,
    {
        let (_, expr) = self.select_spanned(iter, |e| e.span);
        self.visit_expr(expr.unwrap());
    }

    fn visit_pattern(&mut self, current: &'a SpannedPattern<Symbol>) {
        if current.span.containment(&self.pos) == Ordering::Equal {
            self.enclosing_match = Match::Pattern(current);
        }
        match current.value {
            Pattern::As(_, ref pat) => self.visit_pattern(pat),
            Pattern::Constructor(ref id, ref args) => {
                let id_span = Span::new(
                    current.span.start,
                    current.span.start + BytePos::from(id.as_ref().len()),
                );
                if id_span.containment(&self.pos) == Ordering::Equal {
                    self.found = Some(Some(Match::Pattern(current)));
                    return;
                }
                let (_, pattern) = self.select_spanned(args, |e| e.span);
                match pattern {
                    Some(pattern) => self.visit_pattern(pattern),
                    None => self.found = Some(None),
                }
            }
            Pattern::Record { ref fields, .. } => {
                let (_, field) = self.select_spanned(fields, |field| {
                    Span::new(
                        field.name.span.start,
                        field
                            .value
                            .as_ref()
                            .map_or(field.name.span.end, |p| p.span.end),
                    )
                });
                if let Some(field) = field {
                    if field.name.span.containment(&self.pos) != Ordering::Greater {
                        self.found = Some(None);
                    } else if let Some(ref pattern) = field.value {
                        self.visit_pattern(pattern)
                    }
                }
            }
            Pattern::Tuple { ref elems, .. } => {
                let (_, field) = self.select_spanned(elems, |elem| elem.span);
                self.visit_pattern(field.unwrap());
            }
            Pattern::Ident(_) | Pattern::Error => {
                self.found = Some(if current.span.containment(&self.pos) == Ordering::Equal {
                    Some(Match::Pattern(current))
                } else {
                    None
                });
            }
        }
    }

    fn visit_expr(&mut self, current: &'a SpannedExpr<Symbol>) {
        // When inside a macro expanded expression we do a exhaustive search for an unexpanded
        // expression
        if current.span.expansion_id != NO_EXPANSION {
            VisitUnExpanded(self).visit_expr(current);
            return;
        }
        if current.span.containment(&self.pos) == Ordering::Equal {
            self.enclosing_match = Match::Expr(current);
        }
        match current.value {
            Expr::Ident(_) | Expr::Literal(_) => {
                self.found = Some(if current.span.containment(&self.pos) == Ordering::Equal {
                    Some(Match::Expr(current))
                } else {
                    None
                });
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
                    Ok(expr) => {
                        self.enclosing_match = Match::Expr(expr);
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
            Expr::Infix(ref l, ref op, ref r) => {
                match (l.span.containment(&self.pos), r.span.containment(&self.pos)) {
                    (Ordering::Greater, Ordering::Less) => {
                        self.found =
                            Some(Some(Match::Ident(op.span, &op.value.name, &op.value.typ)));
                    }
                    (_, Ordering::Greater) | (_, Ordering::Equal) => self.visit_expr(r),
                    _ => self.visit_expr(l),
                }
            }
            Expr::LetBindings(ref bindings, ref expr) => {
                for bind in bindings {
                    self.on_found.on_pattern(&bind.name);
                }
                match self.select_spanned(bindings, |b| Span::new(b.name.span.start, b.expr.span.end))
                {
                    (false, Some(bind)) => {
                        for arg in &bind.args {
                            self.on_found.on_ident(&arg.value);
                        }

                        enum Variant<'a> {
                            Pattern(&'a SpannedPattern<Symbol>),
                            Ident(&'a SpannedIdent<Symbol>),
                            Type(&'a AstType<Symbol>),
                            Expr(&'a SpannedExpr<Symbol>),
                        }
                        let iter = once(Variant::Pattern(&bind.name))
                            .chain(bind.args.iter().map(Variant::Ident))
                            .chain(bind.typ.iter().map(Variant::Type))
                            .chain(once(Variant::Expr(&bind.expr)));
                        let (_, sel) = self.select_spanned(iter, |x| match *x {
                            Variant::Pattern(p) => p.span,
                            Variant::Ident(e) => e.span,
                            Variant::Type(t) => t.span(),
                            Variant::Expr(e) => e.span,
                        });

                        match sel.unwrap() {
                            Variant::Pattern(pattern) => self.visit_pattern(pattern),
                            Variant::Ident(ident) => {
                                self.found = Some(Some(Match::Ident(
                                    ident.span,
                                    &ident.value.name,
                                    &ident.value.typ,
                                )));
                            }
                            Variant::Type(t) => self.visit_ast_type(t),
                            Variant::Expr(expr) => self.visit_expr(expr),
                        }
                    }
                    _ => self.visit_expr(expr),
                }
            }
            Expr::TypeBindings(ref type_bindings, ref expr) => {
                for type_binding in type_bindings {
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
                            if bind.name.span.containment(&self.pos) == Ordering::Equal {
                                self.found = Some(Some(Match::Type(
                                    bind.name.span,
                                    &bind.alias.value.name,
                                    bind.alias.value.unresolved_type().kind().into_owned(),
                                )));
                            } else {
                                for param in bind.alias.value.params() {
                                    self.on_found.on_type_ident(&param);
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
                if expr.span.containment(&self.pos) <= Ordering::Equal {
                    self.visit_expr(expr);
                } else {
                    self.enclosing_match = Match::Expr(current);
                    self.found = Some(Some(Match::Ident(current.span, id, typ)));
                }
            }
            Expr::Array(ref array) => self.visit_one(&array.exprs),
            Expr::Record {
                ref exprs,
                ref base,
                ..
            } => {
                let exprs = exprs
                    .iter()
                    .filter_map(|tup| tup.value.as_ref())
                    .chain(base.as_ref().map(|base| &**base));
                if let (_, Some(expr)) = self.select_spanned(exprs, |e| e.span) {
                    self.visit_expr(expr);
                }
            }
            Expr::Lambda(ref lambda) => {
                for arg in &lambda.args {
                    self.on_found.on_ident(&arg.value);
                }

                let selection = self.select_spanned(&lambda.args, |arg| arg.span);
                match selection {
                    (false, Some(arg)) => {
                        self.found = Some(Some(
                            Match::Ident(arg.span, &arg.value.name, &arg.value.typ),
                        ));
                    }
                    _ => self.visit_expr(&lambda.body),
                }
            }
            Expr::Tuple {
                elems: ref exprs, ..
            } |
            Expr::Block(ref exprs) => if exprs.is_empty() {
                self.found = Some(Some(Match::Expr(current)));
            } else {
                self.visit_one(exprs)
            },
            Expr::Error(..) => (),
        }
    }

    fn visit_ast_type(&mut self, typ: &'a AstType<Symbol>) {
        match **typ {
            // ExtendRow do not have spans set properly so recurse unconditionally
            Type::ExtendRow { .. } => (),
            _ if typ.span().containment(&self.pos) != Ordering::Equal => return,
            _ => (),
        }
        match **typ {
            Type::Ident(ref id) => {
                self.found = Some(Some(Match::Type(typ.span(), id, Kind::hole())));
            }

            Type::Generic(ref gen) => {
                self.found = Some(Some(Match::Type(typ.span(), &gen.id, gen.kind.clone())));
            }

            Type::Alias(ref alias) => {
                self.found = Some(Some(Match::Type(
                    typ.span(),
                    &alias.name,
                    typ.kind().into_owned(),
                )));
            }

            Type::Forall(ref params, ref typ, _) => {
                for param in params {
                    self.on_found.on_type_ident(param);
                }

                self.visit_ast_type(typ);
            }

            _ => walk_type_(
                typ,
                &mut ControlVisitation(|typ: &'a AstType<Symbol>| self.visit_ast_type(typ)),
            ),
        }
    }
}

fn complete_at<F>(on_found: F, expr: &SpannedExpr<Symbol>, pos: BytePos) -> Result<Found, ()>
where
    F: OnFound,
{
    let mut visitor = FindVisitor {
        pos: pos,
        on_found: on_found,
        found: None,
        enclosing_match: Match::Expr(expr),
    };
    visitor.visit_expr(expr);
    let enclosing_match = visitor.enclosing_match;
    visitor
        .found
        .map(|match_| {
            Found {
                match_,
                enclosing_match,
            }
        })
        .ok_or(())
}

pub trait Extract: Sized {
    type Output;
    fn extract(self, found: &Found) -> Result<Self::Output, ()>;
    fn match_extract(self, match_: &Match) -> Result<Self::Output, ()>;
}

#[derive(Clone, Copy)]
pub struct TypeAt<'a> {
    pub env: &'a TypeEnv,
}
impl<'a> Extract for TypeAt<'a> {
    type Output = ArcType;
    fn extract(self, found: &Found) -> Result<Self::Output, ()> {
        match found.match_ {
            Some(ref match_) => self.match_extract(match_),
            None => self.match_extract(&found.enclosing_match),
        }
    }

    fn match_extract(self, found: &Match) -> Result<Self::Output, ()> {
        Ok(match *found {
            Match::Expr(expr) => expr.env_type_of(self.env),
            Match::Ident(_, _, typ) => typ.clone(),
            Match::Type(..) => return Err(()),
            Match::Pattern(pattern) => pattern.env_type_of(self.env),
        })
    }
}

#[derive(Clone, Copy)]
pub struct IdentAt;
impl Extract for IdentAt {
    type Output = Symbol;
    fn extract(self, found: &Found) -> Result<Self::Output, ()> {
        match found.match_ {
            Some(ref match_) => self.match_extract(match_),
            None => self.match_extract(&found.enclosing_match),
        }
    }

    fn match_extract(self, found: &Match) -> Result<Self::Output, ()> {
        Ok(match *found {
            Match::Expr(&Spanned {
                value: Expr::Ident(ref id),
                ..
            }) => id.name.clone(),
            Match::Ident(_, id, _) => id.clone(),
            Match::Pattern(&Spanned {
                value: Pattern::Ident(ref id),
                ..
            }) => id.name.clone(),
            Match::Pattern(&Spanned {
                value: Pattern::As(ref id, _),
                ..
            }) => id.clone(),
            _ => return Err(()),
        })
    }
}

#[derive(Copy, Clone)]
pub struct SpanAt;
impl Extract for SpanAt {
    type Output = Span<BytePos>;
    fn extract(self, found: &Found) -> Result<Self::Output, ()> {
        match found.match_ {
            Some(ref match_) => self.match_extract(match_),
            None => self.match_extract(&found.enclosing_match),
        }
    }

    fn match_extract(self, found: &Match) -> Result<Self::Output, ()> {
        Ok(match *found {
            Match::Expr(expr) => expr.span,
            Match::Ident(span, _, _) => span,
            Match::Type(span, _, _) => span,
            Match::Pattern(pattern) => pattern.span,
        })
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
        impl<$($id : Extract),*> Extract for ( $($id),* ) {
            type Output = ( $($id::Output),* );
            fn extract(self, found: &Found) -> Result<Self::Output, ()> {
                let ( $($id),* ) = self;
                Ok(( $( $id.extract(found)? ),* ))
            }
            fn match_extract(self, found: &Match) -> Result<Self::Output, ()> {
                let ( $($id),* ) = self;
                Ok(( $( $id.match_extract(found)? ),* ))
            }
        }
    };
}

tuple_extract!{A B C D E F G H}

pub fn completion<T>(extract: T, expr: &SpannedExpr<Symbol>, pos: BytePos) -> Result<T::Output, ()>
where
    T: Extract,
{
    let found = complete_at((), expr, pos)?;
    extract.extract(&found)
}

pub fn find<T>(env: &T, expr: &SpannedExpr<Symbol>, pos: BytePos) -> Result<ArcType, ()>
where
    T: TypeEnv,
{
    let extract = TypeAt { env };
    completion(extract, expr, pos)
}

pub fn find_all_symbols(
    expr: &SpannedExpr<Symbol>,
    pos: BytePos,
) -> Result<(String, Vec<Span<BytePos>>), ()> {
    let extract = IdentAt;
    completion(extract, expr, pos).map(|symbol| {
        struct ExtractIdents {
            result: Vec<Span<BytePos>>,
            symbol: Symbol,
        }
        impl<'a> Visitor<'a> for ExtractIdents {
            type Ident = Symbol;

            fn visit_expr(&mut self, e: &'a SpannedExpr<Self::Ident>) {
                match e.value {
                    Expr::Ident(ref id) if id.name == self.symbol => {
                        self.result.push(e.span);
                    }
                    _ => walk_expr(self, e),
                }
            }

            fn visit_pattern(&mut self, p: &'a SpannedPattern<Self::Ident>) {
                match p.value {
                    Pattern::As(ref id, ref pat) if id == &self.symbol => {
                        self.result.push(p.span);
                        walk_pattern(self, &pat.value);
                    }
                    Pattern::Ident(ref id) if id.name == self.symbol => {
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

#[derive(Debug, PartialEq)]
pub enum CompletionSymbol<'a> {
    Value {
        name: &'a Symbol,
        typ: &'a ArcType,
        expr: &'a SpannedExpr<Symbol>,
    },
    Type {
        name: &'a Symbol,
        alias: &'a AliasData<Symbol, AstType<Symbol>>,
    },
}

pub fn all_symbols(expr: &SpannedExpr<Symbol>) -> Vec<Spanned<CompletionSymbol, BytePos>> {
    struct AllIdents<'a> {
        result: Vec<Spanned<CompletionSymbol<'a>, BytePos>>,
    }
    impl<'a> Visitor<'a> for AllIdents<'a> {
        type Ident = Symbol;

        fn visit_expr(&mut self, e: &'a SpannedExpr<Self::Ident>) {
            match e.value {
                Expr::TypeBindings(ref binds, _) => {
                    self.result.extend(binds.iter().map(|bind| {
                        pos::spanned(
                            bind.name.span,
                            CompletionSymbol::Type {
                                name: &bind.name.value,
                                alias: &bind.alias.value,
                            },
                        )
                    }));
                }
                Expr::LetBindings(ref binds, _) => self.result.extend(
                    binds.iter().flat_map(|bind| match bind.name.value {
                        Pattern::Ident(ref id) => Some(pos::spanned(
                            bind.name.span,
                            CompletionSymbol::Value {
                                name: &id.name,
                                typ: &id.typ,
                                expr: &bind.expr,
                            },
                        )),
                        _ => None,
                    }),
                ),
                _ => (),
            }
            walk_expr(self, e)
        }
    }
    let mut visitor = AllIdents { result: Vec::new() };
    visitor.visit_expr(expr);
    visitor.result
}

pub fn suggest<T>(env: &T, expr: &SpannedExpr<Symbol>, pos: BytePos) -> Vec<Suggestion>
where
    T: TypeEnv,
{
    let mut suggest = Suggest::new(env);

    let found = match complete_at(&mut suggest, expr, pos) {
        Ok(x) => x,
        Err(()) => return vec![],
    };
    let mut result = vec![];
    match found.match_ {
        Some(match_) => match match_ {
            Match::Expr(expr) => {
                result.extend(expr_iter(&suggest.stack, expr).map(|(k, typ)| {
                    Suggestion {
                        name: k.declared_name().into(),
                        typ: Either::Right(typ.clone()),
                    }
                }));
            }

            Match::Pattern(pattern) => {
                let prefix = match pattern.value {
                    Pattern::Constructor(ref id, _) | Pattern::Ident(ref id) => id.as_ref(),
                    _ => "",
                };
                result.extend(
                    suggest
                        .patterns
                        .iter()
                        .filter(|&(ref name, _)| name.declared_name().starts_with(prefix))
                        .map(|(name, typ)| {
                            Suggestion {
                                name: name.declared_name().into(),
                                typ: Either::Right(typ.clone()),
                            }
                        }),
                );
            }
            Match::Ident(_, ident, _) => if let Match::Expr(context) = found.enclosing_match {
                let iter = suggest.ident_iter(context, ident);
                result.extend(iter.into_iter().map(|(name, typ)| {
                    Suggestion {
                        name: name.declared_name().into(),
                        typ: Either::Right(typ),
                    }
                }));
            },

            Match::Type(_, ident, _) => {
                result.extend(
                    suggest
                        .type_stack
                        .iter()
                        .filter(|&(k, _)| {
                            k.declared_name().starts_with(ident.declared_name())
                        })
                        .map(|(name, kind)| {
                            Suggestion {
                                name: name.declared_name().into(),
                                typ: Either::Left(kind.clone()),
                            }
                        }),
                );
            }
        },

        None => match found.enclosing_match {
            Match::Expr(..) | Match::Ident(..) => {
                result.extend(suggest.stack.iter().map(|(name, typ)| {
                    Suggestion {
                        name: name.declared_name().into(),
                        typ: Either::Right(typ.clone()),
                    }
                }));
            }

            Match::Type(_, ident, _) => {
                result.extend(
                    suggest
                        .type_stack
                        .iter()
                        .filter(|&(k, _)| {
                            k.declared_name().starts_with(ident.declared_name())
                        })
                        .map(|(name, kind)| {
                            Suggestion {
                                name: name.declared_name().into(),
                                typ: Either::Left(kind.clone()),
                            }
                        }),
                );
            }

            Match::Pattern(..) => result.extend(suggest.patterns.iter().map(|(name, typ)| {
                Suggestion {
                    name: name.declared_name().into(),
                    typ: Either::Right(typ.clone()),
                }
            })),
        },
    }
    result
}

pub fn get_metadata<'a>(
    env: &'a FnvMap<Symbol, Metadata>,
    expr: &SpannedExpr<Symbol>,
    pos: BytePos,
) -> Option<&'a Metadata> {
    complete_at((), expr, pos)
        .ok()
        .and_then(|found| {
            let e = found.enclosing_match;
            found.match_.map(|m| (m, e))
        })
        .and_then(|(match_, enclosing_match)| match match_ {
            Match::Expr(expr) => if let Expr::Ident(ref id) = expr.value {
                env.get(&id.name)
            } else {
                None
            },
            Match::Ident(_, id, _typ) => match enclosing_match {
                Match::Expr(&Spanned {
                    value: Expr::Projection(ref expr, _, _),
                    ..
                }) => if let Expr::Ident(ref expr_id) = expr.value {
                    env.get(&expr_id.name)
                        .and_then(|metadata| metadata.module.get(id.as_ref()))
                } else {
                    None
                },
                Match::Expr(&Spanned {
                    value: Expr::Infix(..),
                    ..
                }) => env.get(id),
                _ => None,
            },
            _ => None,
        })
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
    let mut suggest = Suggest::new(type_env);
    complete_at(&mut suggest, expr, pos)
        .ok()
        .and_then(|found| match found.match_ {
            Some(match_) => match match_ {
                Match::Expr(expr) => {
                    let suggestion = expr_iter(&suggest.stack, expr)
                        .find(|&(stack_name, _)| stack_name.declared_name() == name);
                    if let Some((name, _)) = suggestion {
                        env.get(name)
                    } else {
                        None
                    }
                }

                Match::Ident(_, _, _) => match found.enclosing_match {
                    Match::Expr(&Spanned {
                        value: Expr::Projection(ref expr, _, _),
                        ..
                    }) => if let Expr::Ident(ref expr_ident) = expr.value {
                        env.get(&expr_ident.name)
                            .and_then(|metadata| metadata.module.get(name))
                    } else {
                        None
                    },
                    _ => None,
                },
                _ => None,
            },

            None => match found.enclosing_match {
                Match::Expr(..) | Match::Ident(..) => suggest
                    .stack
                    .iter()
                    .find(|&(ref stack_name, _)| stack_name.declared_name() == name)
                    .and_then(|t| env.get(t.0)),

                _ => None,
            },
        })
}
