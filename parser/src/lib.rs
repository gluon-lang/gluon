//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.
#![doc(html_root_url = "https://docs.rs/gluon_parser/0.14.1")] // # GLUON

extern crate codespan;
extern crate codespan_reporting;
extern crate collect_mac;
extern crate gluon_base as base;
extern crate itertools;
#[macro_use]
extern crate lalrpop_util;
#[macro_use]
extern crate log;
extern crate ordered_float;
extern crate pretty;
#[macro_use]
extern crate quick_error;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;

use std::{fmt, hash::Hash, marker::PhantomData, sync::Arc};

use itertools::Either;

use crate::base::{
    ast::{
        self, AstType, Do, Expr, IdentEnv, PatternField, RootExpr, SpannedExpr, SpannedPattern,
        TypedIdent, ValueBinding,
    },
    error::{AsDiagnostic, Errors},
    fnv::FnvMap,
    metadata::{BaseMetadata, Metadata},
    mk_ast_arena,
    pos::{self, ByteOffset, BytePos, Span, Spanned},
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
fn shrink_hidden_spans<Id>(mut expr: SpannedExpr<Id>) -> SpannedExpr<Id> {
    match expr.value {
        Expr::Infix { rhs: ref last, .. }
        | Expr::IfElse(_, _, ref last)
        | Expr::LetBindings(_, ref last)
        | Expr::TypeBindings(_, ref last)
        | Expr::Do(Do { body: ref last, .. }) => {
            expr.span = Span::new(expr.span.start(), last.span.end())
        }
        Expr::Lambda(ref lambda) => {
            expr.span = Span::new(expr.span.start(), lambda.body.span.end())
        }
        Expr::Block(ref mut exprs) => match exprs {
            [] => (),
            [e] => return std::mem::take(e),
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
    fn as_diagnostic(&self) -> codespan_reporting::Diagnostic {
        codespan_reporting::Diagnostic::new_error(self.to_string())
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
    Gadt(Id, AstType<'ast, Id>),
    Simple(Id, Vec<AstType<'ast, Id>>),
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

            fn drain<'a, T>(&'a mut self, start: TempVecStart<T>) -> impl Iterator<Item = T> + 'a
            where
                T: TempVec<'ast, Id> + 'a,
            {
                T::select(self).drain(start.0..)
            }

            fn drain_n<'a, T>(&'a mut self, n: usize) -> impl Iterator<Item = T> + 'a
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
    Field<Id, AstType<'ast, Id>> => type_fields,
    Field<Id, Alias<Id, AstType<'ast, Id>>> => type_type_fields,
    Either<Field<Id, Alias<Id, AstType<'ast, Id>>>, Field<Id, AstType<'ast, Id>>> => either_type_fields,
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

impl ParserSource for codespan::FileMap {
    fn src(&self) -> &str {
        codespan::FileMap::src(self)
    }
    fn start_index(&self) -> BytePos {
        codespan::FileMap::span(self).start()
    }
}

macro_rules! enum_ {
        ($($id: ident ($typ: ty $(,)?),)* $(,)?) => {
            let mut a = [$( ( stringify!($typ), ::std::mem::size_of::<$typ>() ) ),*];
            a.sort_by(|l, r| l.1.cmp(&r.1));
            eprintln!("{:#?}", &a[..]);
            panic!();
        }
    }
pub mod t {
    use std::{mem, str::FromStr};

    use crate::itertools::{Either, Itertools};

    use crate::base::{
        ast::{
            self, Alternative, Argument, Array, AstType, Do, Expr, ExprField, KindedIdent, Lambda,
            Literal, Pattern, PatternField, SpannedExpr, SpannedIdent, SpannedPattern, TypeBinding,
            TypedIdent, ValueBinding, ValueBindings,
        },
        kind::{ArcKind, Kind},
        metadata::{Attribute, BaseMetadata, Comment},
        pos::{self, BytePos, HasSpan, Spanned},
        types::{
            Alias, AliasData, ArcType, ArgType, BuiltinType, Field, Generic, Type, TypeCache,
            TypeContext,
        },
    };

    use crate::ordered_float::NotNan;
    use crate::token::{BorrowedToken, StringLiteral, Token};
    use crate::{new_ident, ReplLine, Variant};

    use crate::{Error, ErrorEnv, FieldExpr, MutIdentEnv, Slice, TempVecStart, TempVecs};

    pub(crate) fn run() {
        enum_! {
            Variant0(BorrowedToken<'_>),
            Variant1(u8),
            Variant2(char),
            Variant3(Comment<&'_ str>),
            Variant4(NotNan<f64>),
            Variant5(&'_ str),
            Variant6(i64),
            Variant7(StringLiteral<&'_ str>),
            Variant8(lalrpop_util::ErrorRecovery<BytePos, BorrowedToken<'_>, Spanned<Error, BytePos>>),
            Variant9(::std::option::Option<BorrowedToken<'_>>),
            Variant10(::std::vec::Vec<Comment<&'_ str>>),
            Variant11(::std::option::Option<&'_ str>),
            Variant12(AstType<'_, String>),
            Variant13(::std::option::Option<AstType<'_, String>>),
            Variant14(Spanned<Type<String, AstType<'_, String>>, BytePos>),
            Variant15(Field<String, AstType<'_, String>>),
            Variant16(FieldExpr<'_, String>),
            Variant17(String),
            Variant18(::std::vec::Vec<String>),
            Variant19(PatternField<'_, String>),
            Variant20(Either<Field<String, Alias<String, AstType<'_, String>>>, Field<String, AstType<'_, String>>>),
            Variant21(Spanned<Pattern<'_, String>, BytePos>),
            Variant22(SpannedExpr<'_, String>),
            Variant23(BytePos),
            Variant24(Alternative<'_, String>),
            Variant25(()),
            Variant26(::std::vec::Vec<()>),
            Variant27(Expr<'_, String>),
            Variant28(Type<String, AstType<'_, String>>),
            Variant29((ArgType, AstType<'_, String>)),
            Variant30(ArcKind),
            Variant31(Pattern<'_, String>),
            Variant32(::std::vec::Vec<AstType<'_, String>>),
            Variant33(Attribute),
            Variant34(::std::vec::Vec<Attribute>),
            Variant35(Option<String>),
            Variant36(&'_ mut Slice<PatternField<'_, String>>),
            Variant37(&'_ mut Slice<Spanned<Pattern<'_, String>, BytePos>>),
            Variant38(&'_ mut Slice<SpannedExpr<'_, String>>),
            Variant39(TempVecStart<FieldExpr<'_, String>>),
            Variant40(TempVecStart<Either<Field<String, Alias<String, AstType<'_, String>>>, Field<String, AstType<'_, String>>>>),
            Variant41(TempVecStart<AstType<'_, String>>),
            Variant42(Box<(SpannedPattern<'_, String>, SpannedExpr<'_, String>)>),
            Variant43(Comment),
            Variant44(::std::option::Option<Field<String, AstType<'_, String>>>),
            Variant45(::std::option::Option<FieldExpr<'_, String>>),
            Variant46(Argument<SpannedIdent<String>>),
            Variant47(Literal),
            Variant48(&'_ mut Slice<Alternative<'_, String>>),
            Variant49(&'_ mut Slice<AstType<'_, String>>),
            Variant50(&'_ mut Slice<Argument<SpannedIdent<String>>>),
            Variant51(&'_ mut Slice<TypeBinding<'_, String>>),
            Variant52(TempVecStart<Field<String, AstType<'_, String>>>),
            Variant53(::std::option::Option<TempVecStart<Field<String, AstType<'_, String>>>>),
            Variant54(::std::option::Option<TempVecStart<FieldExpr<'_, String>>>),
            Variant55(TempVecStart<PatternField<'_, String>>),
            Variant56(::std::option::Option<TempVecStart<PatternField<'_, String>>>),
            Variant57(::std::option::Option<TempVecStart<Either<Field<String, Alias<String, AstType<'_, String>>>, Field<String, AstType<'_, String>>>>>),
            Variant58(TempVecStart<Spanned<Pattern<'_, String>, BytePos>>),
            Variant59(::std::option::Option<TempVecStart<Spanned<Pattern<'_, String>, BytePos>>>),
            Variant60(TempVecStart<SpannedExpr<'_, String>>),
            Variant61(::std::option::Option<TempVecStart<SpannedExpr<'_, String>>>),
            Variant62(::std::option::Option<TempVecStart<AstType<'_, String>>>),
            Variant63(TempVecStart<Alternative<'_, String>>),
            Variant64(TempVecStart<Argument<SpannedIdent<String>>>),
            Variant65(TempVecStart<TypeBinding<'_, String>>),
            Variant66(BaseMetadata),
            Variant67(::std::option::Option<BaseMetadata>),
            Variant68(TypedIdent<String>),
            Variant69(::std::option::Option<PatternField<'_, String>>),
            Variant70(Option<SpannedExpr<'_, String>>),
            Variant71(::std::option::Option<Either<Field<String, Alias<String, AstType<'_, String>>>, Field<String, AstType<'_, String>>>>),
            Variant72(Option<Box<ReplLine<'_, String>>>),
            Variant73(&'_ mut Slice<Field<String, AstType<'_, String>>>),
            Variant74(Spanned<BorrowedToken<'_>, BytePos>),
            Variant75(Spanned<::std::option::Option<BorrowedToken<'_>>, BytePos>),
            Variant76(Spanned<AstType<'_, String>, BytePos>),
            Variant77(Spanned<Expr<'_, String>, BytePos>),
            Variant78(Spanned<String, BytePos>),
            Variant79(Spanned<&'_ str, BytePos>),
            Variant80(Spanned<TypedIdent<String>, BytePos>),
            Variant81(::std::option::Option<Spanned<Pattern<'_, String>, BytePos>>),
            Variant82(Spanned<(), BytePos>),
            Variant83(Spanned<(Vec<String>, Vec<Variant<'_, String>>, Option<AstType<'_, String>>), BytePos>),
            Variant84(::std::option::Option<SpannedExpr<'_, String>>),
            Variant85(SpannedIdent<String>),
            Variant86(TypeBinding<'_, String>),
            Variant87(Generic<String>),
            Variant88(::std::vec::Vec<Generic<String>>),
            Variant89(Either<AstType<'_, String>, Spanned<(Vec<String>, Vec<Variant<'_, String>>, Option<AstType<'_, String>>), BytePos>>),
            Variant90(&'_ mut ValueBinding<'_, String>),
            Variant91(Variant<'_, String>),
            Variant92(::std::vec::Vec<Variant<'_, String>>),
            Variant93((Vec<String>, Vec<Variant<'_, String>>, Option<AstType<'_, String>>)),
        }
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
    let layout = Layout::new(Tokenizer::new(input));

    let mut parse_errors = Errors::new();

    let result = grammar::TopExprParser::new().parse(
        &input,
        type_cache,
        arena,
        symbols,
        &mut parse_errors,
        &mut TempVecs::new(),
        layout,
    );

    match result {
        Ok(expr) => {
            if parse_errors.has_errors() {
                Err((Some(expr), transform_errors(input.span(), parse_errors)))
            } else {
                Ok(expr)
            }
        }
        Err(err) => {
            parse_errors.push(err);
            Err((None, transform_errors(input.span(), parse_errors)))
        }
    }
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
    let layout = Layout::new(Tokenizer::new(input));

    let mut parse_errors = Errors::new();

    let type_cache = TypeCache::default();

    let result = grammar::ReplLineParser::new().parse(
        &input,
        &type_cache,
        arena,
        symbols,
        &mut parse_errors,
        &mut TempVecs::new(),
        layout,
    );

    match result {
        Ok(repl_line) => {
            let repl_line = repl_line.map(|b| *b);
            if parse_errors.has_errors() {
                Err((repl_line, transform_errors(input.span(), parse_errors)))
            } else {
                Ok(repl_line)
            }
        }
        Err(err) => {
            parse_errors.push(err);
            Err((None, transform_errors(input.span(), parse_errors)))
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
