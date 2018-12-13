//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.
#![doc(html_root_url = "https://docs.rs/gluon_parser/0.9.4")] // # GLUON

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

use std::cell::RefCell;
use std::fmt;
use std::hash::Hash;

use base::ast::{Do, Expr, IdentEnv, SpannedExpr, SpannedPattern, TypedIdent, ValueBinding};
use base::error::{AsDiagnostic, Errors};
use base::fnv::FnvMap;
use base::metadata::Metadata;
use base::pos::{self, ByteOffset, BytePos, Span, Spanned};
use base::symbol::Symbol;
use base::types::{ArcType, TypeCache};

use infix::{Fixity, OpMeta, OpTable, Reparser};
use layout::Layout;
use token::{Token, Tokenizer};

pub use infix::Error as InfixError;
pub use layout::Error as LayoutError;
pub use token::Error as TokenizeError;

lalrpop_mod!(
    #[cfg_attr(rustfmt, rustfmt_skip)]
    grammar
);

pub mod infix;
mod layout;
mod token;

fn new_ident<Id>(type_cache: &TypeCache<Id, ArcType<Id>>, name: Id) -> TypedIdent<Id> {
    TypedIdent {
        name: name,
        typ: type_cache.hole(),
    }
}

type LalrpopError<'input> =
    lalrpop_util::ParseError<BytePos, Token<'input>, Spanned<Error, BytePos>>;

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
        Expr::Block(ref mut exprs) => match exprs.len() {
            0 => (),
            1 => return exprs.pop().unwrap(),
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
    #[derive(Debug, PartialEq)]
    pub enum Error {
        Token(err: TokenizeError) {
            description(err.description())
            display("{}", err)
            from()
        }
        Layout(err: LayoutError) {
            description(err.description())
            display("{}", err)
            from()
        }
        InvalidToken {
            description("invalid token")
            display("Invalid token")
        }
        UnexpectedToken(token: String, expected: Vec<String>) {
            description("unexpected token")
            display("Unexpected token: {}{}", token, Expected(&expected))
        }
        UnexpectedEof(expected: Vec<String>) {
            description("unexpected end of file")
            display("Unexpected end of file{}", Expected(&expected))
        }
        ExtraToken(token: String) {
            description("extra token")
            display("Extra token: {}", token)
        }
        Infix(err: InfixError) {
            description(err.description())
            display("{}", err)
            from()
        }
        Message(msg: String) {
            description(msg)
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
                token: Some((lpos, token, rpos)),
                mut expected,
            } => {
                remove_extra_quotes(&mut expected);
                pos::spanned2(
                    lpos,
                    rpos,
                    Error::UnexpectedToken(token.to_string(), expected),
                )
            }
            UnrecognizedToken {
                token: None,
                mut expected,
            } => {
                remove_extra_quotes(&mut expected);
                pos::spanned2(
                    source_span.end(),
                    source_span.end(),
                    Error::UnexpectedEof(expected),
                )
            }
            ExtraToken {
                token: (lpos, token, rpos),
            } => pos::spanned2(lpos, rpos, Error::ExtraToken(token.to_string())),
            User { error } => error,
        }
    }
}

/// An iterator which forwards only the `Ok` values. If an `Err` is found the iterator returns
/// `None` and the error can be retrieved using the `result` method.
struct ResultOkIter<I, E> {
    iter: I,
    error: Option<E>,
}

impl<I, E> ResultOkIter<I, E> {
    fn new(iter: I) -> ResultOkIter<I, E> {
        ResultOkIter {
            iter: iter,
            error: None,
        }
    }

    fn result<T>(&mut self, value: T) -> Result<T, E> {
        match self.error.take() {
            Some(err) => Err(err),
            None => Ok(value),
        }
    }
}

impl<I, T, E> Iterator for ResultOkIter<I, E>
where
    I: Iterator<Item = Result<T, E>>,
    E: ::std::fmt::Debug,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        match self.iter.next() {
            Some(Ok(t)) => Some(t),
            Some(Err(err)) => {
                self.error = Some(err);
                None
            }
            None => None,
        }
    }
}

/// An iterator which can be shared
struct SharedIter<'a, I: 'a> {
    iter: &'a RefCell<I>,
}

impl<'a, I> Clone for SharedIter<'a, I> {
    fn clone(&self) -> SharedIter<'a, I> {
        SharedIter { iter: self.iter }
    }
}

impl<'a, I> SharedIter<'a, I> {
    fn new(iter: &'a RefCell<I>) -> SharedIter<'a, I> {
        SharedIter { iter }
    }
}

impl<'a, I> Iterator for SharedIter<'a, I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        self.iter.borrow_mut().next()
    }
}

pub enum FieldPattern<Id> {
    Type(Spanned<Id, BytePos>, Option<Id>),
    Value(Spanned<Id, BytePos>, Option<SpannedPattern<Id>>),
}

pub enum FieldExpr<Id> {
    Type(Metadata, Spanned<Id, BytePos>, Option<ArcType<Id>>),
    Value(Metadata, Spanned<Id, BytePos>, Option<SpannedExpr<Id>>),
}

// Hack around LALRPOP's limited type syntax
type MutIdentEnv<'env, Id> = &'env mut IdentEnv<Ident = Id>;
type ErrorEnv<'err, 'input> = &'err mut Errors<LalrpopError<'input>>;

pub type ParseErrors = Errors<Spanned<Error, BytePos>>;
macro_rules! layout {
    ($result_ok_iter:ident, $input:expr) => {{
        let tokenizer = Tokenizer::new($input);
        $result_ok_iter = RefCell::new(ResultOkIter::new(tokenizer));

        Layout::new(SharedIter::new(&$result_ok_iter)).map(|token| {
            // Return the tokenizer error if one exists
            $result_ok_iter.borrow_mut().result(()).map_err(|err| {
                pos::spanned2(
                    err.span.start().absolute,
                    err.span.end().absolute,
                    err.value.into(),
                )
            })?;
            let token = token.map_err(|err| pos::spanned(err.span, err.value.into()))?;
            debug!("Lex {:?}", token.value);
            Ok((
                token.span.start().absolute,
                token.value,
                token.span.end().absolute,
            ))
        })
    }};
}

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

pub fn parse_partial_expr<Id, S>(
    symbols: &mut IdentEnv<Ident = Id>,
    type_cache: &TypeCache<Id, ArcType<Id>>,
    input: &S,
) -> Result<SpannedExpr<Id>, (Option<SpannedExpr<Id>>, ParseErrors)>
where
    Id: Clone,
    S: ?Sized + ParserSource,
{
    let result_ok_iter;
    let layout = layout!(result_ok_iter, input);

    let mut parse_errors = Errors::new();

    let result =
        grammar::TopExprParser::new().parse(&input, type_cache, symbols, &mut parse_errors, layout);

    // If there is a tokenizer error it may still exist in the result iterator wrapper.
    // If that is the case we return that error instead of the unexpected EOF error that lalrpop
    // emitted
    if let Err(err) = result_ok_iter.borrow_mut().result(()) {
        parse_errors.pop(); // Remove the EOF error
        parse_errors.push(lalrpop_util::ParseError::User {
            error: pos::spanned2(
                err.span.start().absolute,
                err.span.end().absolute,
                err.value.into(),
            ),
        });
    }

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

pub fn parse_expr(
    symbols: &mut IdentEnv<Ident = Symbol>,
    type_cache: &TypeCache<Symbol, ArcType>,
    input: &str,
) -> Result<SpannedExpr<Symbol>, ParseErrors> {
    parse_partial_expr(symbols, type_cache, input).map_err(|t| t.1)
}

#[derive(Debug, PartialEq)]
pub enum ReplLine<Id> {
    Expr(SpannedExpr<Id>),
    Let(ValueBinding<Id>),
}

pub fn parse_partial_repl_line<Id, S>(
    symbols: &mut IdentEnv<Ident = Id>,
    input: &S,
) -> Result<Option<ReplLine<Id>>, (Option<ReplLine<Id>>, ParseErrors)>
where
    Id: Clone + Eq + Hash + AsRef<str> + ::std::fmt::Debug,
    S: ?Sized + ParserSource,
{
    let result_ok_iter;
    let layout = layout!(result_ok_iter, input);

    let mut parse_errors = Errors::new();

    let type_cache = TypeCache::default();

    let result = grammar::ReplLineParser::new().parse(
        &input,
        &type_cache,
        symbols,
        &mut parse_errors,
        layout,
    );

    // If there is a tokenizer error it may still exist in the result iterator wrapper.
    // If that is the case we return that error instead of the unexpected EOF error that lalrpop
    // emitted
    if let Err(err) = result_ok_iter.borrow_mut().result(()) {
        parse_errors.pop(); // Remove the EOF error
        parse_errors.push(lalrpop_util::ParseError::User {
            error: pos::spanned2(
                err.span.start().absolute,
                err.span.end().absolute,
                err.value.into(),
            ),
        });
    }

    match result {
        Ok(repl_line) => {
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

pub fn reparse_infix<Id>(
    metadata: &FnvMap<Id, Metadata>,
    symbols: &IdentEnv<Ident = Id>,
    expr: &mut SpannedExpr<Id>,
) -> Result<(), ParseErrors>
where
    Id: Clone + Eq + Hash + AsRef<str> + ::std::fmt::Debug,
{
    use base::ast::{is_operator_char, walk_pattern, Pattern, Visitor};

    let mut errors = Errors::new();

    struct CheckInfix<'b, Id>
    where
        Id: 'b,
    {
        metadata: &'b FnvMap<Id, Metadata>,
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
    impl<'a, 'b, Id> Visitor<'a> for CheckInfix<'b, Id>
    where
        Id: Clone + Eq + Hash + AsRef<str> + 'a,
    {
        type Ident = Id;

        fn visit_pattern(&mut self, pattern: &'a SpannedPattern<Id>) {
            match pattern.value {
                Pattern::Ident(ref id) => {
                    self.insert_infix(&id.name, pattern.span);
                }
                Pattern::Record { ref fields, .. } => {
                    for field in fields.iter().filter(|field| field.value.is_none()) {
                        self.insert_infix(&field.name.value, field.name.span);
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

    let mut reparser = Reparser::new(op_table, symbols);
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
