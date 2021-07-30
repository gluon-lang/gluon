//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.
#![doc(html_root_url = "https://docs.rs/gluon_parser/0.17.2")] // # GLUON

extern crate gluon_base as base;
#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

use std::{fmt, hash::Hash, marker::PhantomData, sync::Arc};

use itertools::Either;

use crate::base::{
    ast::{
        self, AstType, Do, Expr, IdentEnv, PatternField, RootExpr, Sp, SpannedExpr, SpannedPattern,
        TypedIdent, ValueBinding,
    },
    error::{AsDiagnostic, Errors},
    fnv::FnvMap,
    metadata::{BaseMetadata, Metadata},
    mk_ast_arena,
    pos::{self, ByteOffset, BytePos, Span, Spanned},
    source,
    symbol::Symbol,
    types::{Alias, ArcType, Field, Generic, TypeCache},
};

use crate::{
    infix::{Fixity, OpMeta, OpTable, Reparser},
    layout::Layout,
    token::{BorrowedToken, Tokenizer},
};

pub use crate::{
    infix::Error as InfixError, layout::Error as LayoutError, token::Error as TokenizeError,
    token::Token,
};

lalrpop_mod!(
    #[cfg_attr(rustfmt, rustfmt_skip)]
    #[allow(unused_parens)]
    grammar
);

pub mod infix;
mod layout;
mod str_suffix;
mod token;

fn new_ident<Id>(type_cache: &TypeCache<Id, ArcType<Id>>, name: Id) -> TypedIdent<Id> {
    TypedIdent {
        name: name,
        typ: type_cache.hole(),
    }
}

type LalrpopError<'input> =
    lalrpop_util::ParseError<BytePos, BorrowedToken<'input>, Spanned<Error, BytePos>>;

/// Shrink hidden spans to fit the visible expressions and flatten singleton blocks.
fn shrink_hidden_spans<Id: std::fmt::Debug>(mut expr: SpannedExpr<Id>) -> SpannedExpr<Id> {
    match expr.value {
        Expr::Infix { rhs: ref last, .. }
        | Expr::IfElse(_, _, ref last)
        | Expr::TypeBindings(_, ref last)
        | Expr::Do(Do { body: ref last, .. }) => {
            expr.span = Span::new(expr.span.start(), last.span.end())
        }
        Expr::LetBindings(_, ref last) => expr.span = Span::new(expr.span.start(), last.span.end()),
        Expr::Lambda(ref lambda) => {
            expr.span = Span::new(expr.span.start(), lambda.body.span.end())
        }
        Expr::Block(ref mut exprs) => match exprs {
            [] => (),
            [e] => {
                return std::mem::take(e);
            }
            _ => expr.span = Span::new(expr.span.start(), exprs.last().unwrap().span.end()),
        },
        Expr::Match(_, ref alts) => {
            if let Some(last_alt) = alts.last() {
                let end = last_alt.expr.span.end();
                expr.span = Span::new(expr.span.start(), end);
            }
        }
        Expr::Annotated(..)
        | Expr::App { .. }
        | Expr::Ident(_)
        | Expr::Literal(_)
        | Expr::Projection(_, _, _)
        | Expr::Array(_)
        | Expr::Record { .. }
        | Expr::Tuple { .. }
        | Expr::MacroExpansion { .. }
        | Expr::Error(..) => (),
    }
    expr
}

fn transform_errors<'a, Iter>(
    source_span: Span<BytePos>,
    errors: Iter,
) -> Errors<Spanned<Error, BytePos>>
where
    Iter: IntoIterator<Item = LalrpopError<'a>>,
{
    errors
        .into_iter()
        .map(|err| Error::from_lalrpop(source_span, err))
        .collect()
}

struct Expected<'a>(&'a [String]);

impl<'a> fmt::Display for Expected<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0.len() {
            0 => (),
            1 => write!(f, "\nExpected ")?,
            _ => write!(f, "\nExpected one of ")?,
        }
        for (i, token) in self.0.iter().enumerate() {
            let sep = match i {
                0 => "",
                i if i + 1 < self.0.len() => ",",
                _ => " or",
            };
            write!(f, "{} {}", sep, token)?;
        }
        Ok(())
    }
}

quick_error! {
    #[derive(Debug, Eq, PartialEq, Hash, Clone)]
    pub enum Error {
        Token(err: TokenizeError) {
            display("{}", err)
            from()
        }
        Layout(err: LayoutError) {
            display("{}", err)
            from()
        }
        InvalidToken {
            display("Invalid token")
        }
        UnexpectedToken(token: Token<String>, expected: Vec<String>) {
            display("Unexpected token: {}{}", token, Expected(&expected))
        }
        UnexpectedEof(expected: Vec<String>) {
            display("Unexpected end of file{}", Expected(&expected))
        }
        ExtraToken(token: Token<String>) {
            display("Extra token: {}", token)
        }
        Infix(err: InfixError) {
            display("{}", err)
            from()
        }
        Message(msg: String) {
            display("{}", msg)
            from()
        }
    }
}

impl AsDiagnostic for Error {
    fn as_diagnostic(
        &self,
        _map: &base::source::CodeMap,
    ) -> codespan_reporting::diagnostic::Diagnostic<source::FileId> {
        codespan_reporting::diagnostic::Diagnostic::error().with_message(self.to_string())
    }
}

/// LALRPOP currently has an unnecessary set of `"` around each expected token
fn remove_extra_quotes(tokens: &mut [String]) {
    for token in tokens {
        if token.starts_with('"') && token.ends_with('"') {
            token.remove(0);
            token.pop();
        }
    }
}

impl Error {
    fn from_lalrpop(source_span: Span<BytePos>, err: LalrpopError) -> Spanned<Error, BytePos> {
        use lalrpop_util::ParseError::*;

        match err {
            InvalidToken { location } => pos::spanned2(location, location, Error::InvalidToken),
            UnrecognizedToken {
                token: (lpos, token, rpos),
                mut expected,
            } => {
                remove_extra_quotes(&mut expected);
                pos::spanned2(
                    lpos,
                    rpos,
                    Error::UnexpectedToken(token.map(|s| s.into()), expected),
                )
            }
            UnrecognizedEOF {
                location,
                mut expected,
            } => {
                // LALRPOP will use `Default::default()` as the location if it is unable to find
                // one. This is not correct for codespan as that represents "nil" so we must grab
                // the end from the current source instead
                let location = if location == BytePos::default() {
                    source_span.end()
                } else {
                    location
                };
                remove_extra_quotes(&mut expected);
                pos::spanned2(location, location, Error::UnexpectedEof(expected))
            }
            ExtraToken {
                token: (lpos, token, rpos),
            } => pos::spanned2(lpos, rpos, Error::ExtraToken(token.map(|s| s.into()))),
            User { error } => error,
        }
    }
}

#[derive(Debug)]
pub enum FieldExpr<'ast, Id> {
    Type(
        BaseMetadata<'ast>,
        Spanned<Id, BytePos>,
        Option<ArcType<Id>>,
    ),
    Value(
        BaseMetadata<'ast>,
        Spanned<Id, BytePos>,
        Option<SpannedExpr<'ast, Id>>,
    ),
}

pub enum Variant<'ast, Id> {
    Gadt(Sp<Id>, AstType<'ast, Id>),
    Simple(Sp<Id>, Vec<AstType<'ast, Id>>),
}

// Hack around LALRPOP's limited type syntax
type MutIdentEnv<'env, Id> = &'env mut dyn IdentEnv<Ident = Id>;
type ErrorEnv<'err, 'input> = &'err mut Errors<LalrpopError<'input>>;
type Slice<T> = [T];

trait TempVec<'ast, Id>: Sized {
    fn select<'a>(vecs: &'a mut TempVecs<'ast, Id>) -> &'a mut Vec<Self>;
}

macro_rules! impl_temp_vec {
    ($( $ty: ty => $field: ident),* $(,)?) => {
        #[doc(hidden)]
        pub struct TempVecs<'ast, Id> {
        $(
            $field: Vec<$ty>,
        )*
        }

        #[doc(hidden)]
        #[derive(Debug)]
        pub struct TempVecStart<T>(usize, PhantomData<T>);

        impl<'ast, Id> TempVecs<'ast, Id> {
            fn new() -> Self {
                TempVecs {
                    $(
                        $field: Vec::new(),
                    )*
                }
            }

            fn start<T>(&mut self) -> TempVecStart<T>
            where
                T: TempVec<'ast, Id>,
            {
                TempVecStart(T::select(self).len(), PhantomData)
            }

            fn select<T>(&mut self) -> &mut Vec<T>
            where
                T: TempVec<'ast, Id>,
            {
                T::select(self)
            }

            fn drain<'a, T>(&'a mut self, start: TempVecStart<T>) -> impl DoubleEndedIterator<Item = T> + 'a
            where
                T: TempVec<'ast, Id> + 'a,
            {
                T::select(self).drain(start.0..)
            }

            fn drain_n<'a, T>(&'a mut self, n: usize) -> impl DoubleEndedIterator<Item = T> + 'a
            where
                T: TempVec<'ast, Id> + 'a,
            {
                let vec = T::select(self);
                let start = vec.len() - n;
                vec.drain(start..)
            }
        }

        $(
            impl<'ast, Id> TempVec<'ast, Id> for $ty {
                fn select<'a>(vecs: &'a mut TempVecs<'ast, Id>) -> &'a mut Vec<Self> {
                    &mut vecs.$field
                }
            }
        )*
    };
}
impl_temp_vec! {
    SpannedExpr<'ast, Id> => exprs,
    SpannedPattern<'ast, Id> => patterns,
    ast::PatternField<'ast, Id> => pattern_field,
    ast::ExprField<'ast, Id, ArcType<Id>> => expr_field_types,
    ast::ExprField<'ast, Id, SpannedExpr<'ast, Id>> => expr_field_exprs,
    ast::TypeBinding<'ast, Id> => type_bindings,
    ValueBinding<'ast, Id> => value_bindings,
    ast::Do<'ast, Id> => do_exprs,
    ast::Alternative<'ast, Id> => alts,
    ast::Argument<ast::SpannedIdent<Id>> => args,
    FieldExpr<'ast, Id> => field_expr,
    ast::InnerAstType<'ast, Id> => types,
    AstType<'ast, Id> => type_ptrs,
    Generic<Id> => generics,
    Field<Spanned<Id, BytePos>, AstType<'ast, Id>> => type_fields,
    Field<Spanned<Id, BytePos>, Alias<Id, AstType<'ast, Id>>> => type_type_fields,
    Either<Field<Spanned<Id, BytePos>, Alias<Id, AstType<'ast, Id>>>, Field<Spanned<Id, BytePos>, AstType<'ast, Id>>> => either_type_fields,
}

pub type ParseErrors = Errors<Spanned<Error, BytePos>>;

pub trait ParserSource {
    fn src(&self) -> &str;
    fn start_index(&self) -> BytePos;

    fn span(&self) -> Span<BytePos> {
        let start = self.start_index();
        Span::new(start, start + ByteOffset::from(self.src().len() as i64))
    }
}

impl<'a, S> ParserSource for &'a S
where
    S: ?Sized + ParserSource,
{
    fn src(&self) -> &str {
        (**self).src()
    }
    fn start_index(&self) -> BytePos {
        (**self).start_index()
    }
}

impl ParserSource for str {
    fn src(&self) -> &str {
        self
    }
    fn start_index(&self) -> BytePos {
        BytePos::from(1)
    }
}

impl ParserSource for source::FileMap {
    fn src(&self) -> &str {
        source::FileMap::source(self)
    }
    fn start_index(&self) -> BytePos {
        source::Source::span(self).start()
    }
}

pub fn parse_partial_root_expr<Id, S>(
    symbols: &mut dyn IdentEnv<Ident = Id>,
    type_cache: &TypeCache<Id, ArcType<Id>>,
    input: &S,
) -> Result<RootExpr<Id>, (Option<RootExpr<Id>>, ParseErrors)>
where
    Id: Clone + AsRef<str> + std::fmt::Debug,
    S: ?Sized + ParserSource,
{
    mk_ast_arena!(arena);

    parse_partial_expr((*arena).borrow(), symbols, type_cache, input)
        .map_err(|(expr, err)| {
            (
                expr.map(|expr| RootExpr::new(arena.clone(), arena.alloc(expr))),
                err,
            )
        })
        .map(|expr| RootExpr::new(arena.clone(), arena.alloc(expr)))
}

pub fn parse_partial_expr<'ast, Id, S>(
    arena: ast::ArenaRef<'_, 'ast, Id>,
    symbols: &mut dyn IdentEnv<Ident = Id>,
    type_cache: &TypeCache<Id, ArcType<Id>>,
    input: &S,
) -> Result<SpannedExpr<'ast, Id>, (Option<SpannedExpr<'ast, Id>>, ParseErrors)>
where
    Id: Clone + AsRef<str> + std::fmt::Debug,
    S: ?Sized + ParserSource,
{
    parse_with(input, &mut |parse_errors, layout| {
        grammar::TopExprParser::new().parse(
            &input,
            type_cache,
            arena,
            symbols,
            parse_errors,
            &mut TempVecs::new(),
            layout,
        )
    })
}

pub fn parse_expr<'ast>(
    arena: ast::ArenaRef<'_, 'ast, Symbol>,
    symbols: &mut dyn IdentEnv<Ident = Symbol>,
    type_cache: &TypeCache<Symbol, ArcType>,
    input: &str,
) -> Result<SpannedExpr<'ast, Symbol>, ParseErrors> {
    parse_partial_expr(arena, symbols, type_cache, input).map_err(|t| t.1)
}

#[derive(Debug, PartialEq)]
pub enum ReplLine<'ast, Id> {
    Expr(SpannedExpr<'ast, Id>),
    Let(&'ast mut ValueBinding<'ast, Id>),
}

pub fn parse_partial_repl_line<'ast, Id, S>(
    arena: ast::ArenaRef<'_, 'ast, Id>,
    symbols: &mut dyn IdentEnv<Ident = Id>,
    input: &S,
) -> Result<Option<ReplLine<'ast, Id>>, (Option<ReplLine<'ast, Id>>, ParseErrors)>
where
    Id: Clone + Eq + Hash + AsRef<str> + ::std::fmt::Debug,
    S: ?Sized + ParserSource,
{
    parse_with(input, &mut |parse_errors, layout| {
        let type_cache = TypeCache::default();

        grammar::ReplLineParser::new()
            .parse(
                &input,
                &type_cache,
                arena,
                symbols,
                parse_errors,
                &mut TempVecs::new(),
                layout,
            )
            .map(|o| o.map(|b| *b))
    })
    .map_err(|(opt, err)| (opt.and_then(|opt| opt), err))
}

fn parse_with<'ast, 'input, S, T>(
    input: &'input S,
    parse: &mut dyn FnMut(
        ErrorEnv<'_, 'input>,
        Layout<'input, &mut Tokenizer<'input>>,
    ) -> Result<
        T,
        lalrpop_util::ParseError<BytePos, Token<&'input str>, Spanned<Error, BytePos>>,
    >,
) -> Result<T, (Option<T>, ParseErrors)>
where
    S: ?Sized + ParserSource,
{
    let mut tokenizer = Tokenizer::new(input);
    let layout = Layout::new(&mut tokenizer);

    let mut parse_errors = Errors::new();

    let result = parse(&mut parse_errors, layout);

    let mut all_errors = transform_errors(input.span(), parse_errors);

    all_errors.extend(tokenizer.errors.drain(..).map(|sp_error| {
        pos::spanned2(
            sp_error.span.start().absolute,
            sp_error.span.end().absolute,
            sp_error.value.into(),
        )
    }));

    match result {
        Ok(value) => {
            if all_errors.has_errors() {
                Err((Some(value), all_errors))
            } else {
                Ok(value)
            }
        }
        Err(err) => {
            all_errors.push(Error::from_lalrpop(input.span(), err));
            Err((None, all_errors))
        }
    }
}

pub fn reparse_infix<'ast, Id>(
    arena: ast::ArenaRef<'_, 'ast, Id>,
    metadata: &FnvMap<Id, Arc<Metadata>>,
    symbols: &dyn IdentEnv<Ident = Id>,
    expr: &mut SpannedExpr<'ast, Id>,
) -> Result<(), ParseErrors>
where
    Id: Clone + Eq + Hash + AsRef<str> + ::std::fmt::Debug,
{
    use crate::base::ast::{is_operator_char, walk_pattern, Pattern, Visitor};

    let mut errors = Errors::new();

    struct CheckInfix<'b, Id>
    where
        Id: 'b,
    {
        metadata: &'b FnvMap<Id, Arc<Metadata>>,
        errors: &'b mut Errors<Spanned<Error, BytePos>>,
        op_table: &'b mut OpTable<Id>,
    }

    impl<'b, Id> CheckInfix<'b, Id>
    where
        Id: Clone + Eq + Hash + AsRef<str>,
    {
        fn insert_infix(&mut self, id: &Id, span: Span<BytePos>) {
            match self
                .metadata
                .get(id)
                .and_then(|meta| meta.get_attribute("infix"))
            {
                Some(infix_attribute) => {
                    fn parse_infix(s: &str) -> Result<OpMeta, InfixError> {
                        let mut iter = s.splitn(2, ",");
                        let fixity = match iter.next().ok_or(InfixError::InvalidFixity)?.trim() {
                            "left" => Fixity::Left,
                            "right" => Fixity::Right,
                            _ => {
                                return Err(InfixError::InvalidFixity);
                            }
                        };
                        let precedence = iter
                            .next()
                            .and_then(|s| s.trim().parse().ok())
                            .and_then(|precedence| {
                                if precedence >= 0 {
                                    Some(precedence)
                                } else {
                                    None
                                }
                            })
                            .ok_or(InfixError::InvalidPrecedence)?;
                        Ok(OpMeta { fixity, precedence })
                    }

                    match parse_infix(infix_attribute) {
                        Ok(op_meta) => {
                            self.op_table.operators.insert(id.clone(), op_meta);
                        }
                        Err(err) => {
                            self.errors.push(pos::spanned(span, err.into()));
                        }
                    }
                }

                None => {
                    if id.as_ref().starts_with(is_operator_char) {
                        self.errors.push(pos::spanned(
                            span,
                            InfixError::UndefinedFixity(id.as_ref().into()).into(),
                        ))
                    }
                }
            }
        }
    }
    impl<'a, 'b, 'ast, Id> Visitor<'a, 'ast> for CheckInfix<'b, Id>
    where
        Id: Clone + Eq + Hash + AsRef<str> + 'a + 'ast,
    {
        type Ident = Id;

        fn visit_pattern(&mut self, pattern: &'a SpannedPattern<Id>) {
            match pattern.value {
                Pattern::Ident(ref id) => {
                    self.insert_infix(&id.name, pattern.span);
                }
                Pattern::Record { ref fields, .. } => {
                    for name in fields.iter().filter_map(|field| match field {
                        PatternField::Value { name, value } => {
                            if value.is_none() {
                                Some(name)
                            } else {
                                None
                            }
                        }
                        PatternField::Type { .. } => None,
                    }) {
                        self.insert_infix(&name.value, name.span);
                    }
                }
                _ => (),
            }
            walk_pattern(self, &pattern.value);
        }
    }

    let mut op_table = OpTable::new(None);
    CheckInfix {
        metadata,
        errors: &mut errors,
        op_table: &mut op_table,
    }
    .visit_expr(expr);

    let mut reparser = Reparser::new(arena, op_table, symbols);
    match reparser.reparse(expr) {
        Err(reparse_errors) => {
            errors.extend(reparse_errors.into_iter().map(|err| err.map(Error::from)));
        }
        Ok(_) => {}
    }

    if errors.has_errors() {
        Err(errors)
    } else {
        Ok(())
    }
}
