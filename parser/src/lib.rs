//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.
#[macro_use]
extern crate log;
extern crate gluon_base as base;
extern crate combine;
extern crate combine_language;

pub mod lexer;

use std::cell::RefCell;
use std::fmt;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::rc::Rc;

use base::ast;
use base::ast::*;
use base::error::Errors;
use base::pos::{self, BytePos, Span};
use base::types::{Type, Generic, Alias, Field, Kind};
use base::symbol::{Name, Symbol, SymbolModule};

use combine::primitives::{Consumed, Stream, StreamOnce, Error as CombineError, Info,
                          BufferedStream};
use combine::combinator::EnvParser;
use combine::{between, choice, env_parser, many, many1, optional, parser, satisfy, sep_by1,
              sep_end_by, token, try, value, ParseError, ParseResult, Parser, ParserExt};
use combine_language::{Assoc, Fixity, expression_parser};

use lexer::{Lexer, Delimiter, Token, IdentType};

pub type Error = ParseError<StreamType>;

// Dummy type for ParseError which has the correct associated types
#[derive(Clone)]
pub struct StreamType(());

impl StreamOnce for StreamType {
    type Item = Token<String>;
    type Range = Token<String>;
    type Position = BytePos;

    fn uncons(&mut self) -> Result<Token<String>, ::lexer::Error<String>> {
        unimplemented!()
    }

    fn position(&self) -> Self::Position {
        unimplemented!()
    }
}


/// Parser passes the environment to each parser function
type LanguageParser<'parser, I: 'parser, F: 'parser, T> = EnvParser<&'parser ParserEnv<I, F>, I, T>;

/// `ParserEnv` is passed around to all individual parsers so that identifiers can always be
/// constructed through calling `make_ident`.
struct ParserEnv<I, F>
    where F: IdentEnv,
          I: Stream
{
    empty_id: F::Ident,
    make_ident: Rc<RefCell<F>>,
    errors: RefCell<Errors<Error>>,
    env: PhantomData<I>,
}

// Wrapper type to reduce typechecking times
#[derive(Clone)]
pub struct Wrapper<'input: 'lexer, 'lexer> {
    stream: BufferedStream<'lexer, Lexer<'input, &'input str>>,
}

impl<'input, 'lexer> StreamOnce for Wrapper<'input, 'lexer> {
    type Item = Token<&'input str>;
    type Range = Token<&'input str>;
    type Position = Span<BytePos>;

    fn uncons(&mut self) -> Result<Token<&'input str>, lexer::Error<&'input str>> {
        self.stream.uncons()
    }

    fn position(&self) -> Self::Position {
        let span = self.stream.position();

        Span {
            start: span.start.absolute,
            end: span.end.absolute,
        }
    }
}

enum LetOrType<Id: AstId> {
    Let(Vec<Binding<Id>>),
    Type(Vec<TypeBinding<Id::Untyped>>),
}

macro_rules! match_parser {
    ($function: ident, $variant: ident -> $typ: ty) => {
        fn $function<'a>(&'a self) -> LanguageParser<'a, I, F, $typ> {
            fn inner<'input, I, Id, F>(_: &ParserEnv<I, F>, input: I) -> ParseResult<$typ, I>
                where I: Stream<Item = Token<&'input str>>,
                      F: IdentEnv<Ident = Id>,
                      Id: AstId + Clone + PartialEq + fmt::Debug,
                      I::Range: fmt::Debug
            {
                satisfy(|t: Token<&'input str>| {
                    match t {
                        Token::$variant(_) => true,
                        _ => false,
                    }
                })
                    .map(|t| {
                        match t {
                            Token::$variant(s) => s,
                            _ => unreachable!(),
                        }
                    })
                    .parse_state(input)
            }

            self.parser(inner)
        }
    }
}

fn as_trait<P: Parser>(p: &mut P) -> &mut Parser<Input = P::Input, Output = P::Output> {
    p
}

impl<'input, I, Id, F> ParserEnv<I, F>
    where I: Stream<Item = Token<&'input str>, Range = Token<&'input str>, Position = Span<BytePos>>,
          F: IdentEnv<Ident = Id>,
          Id: AstId + Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug
{
    fn intern(&self, s: &str) -> Id {
        self.make_ident.borrow_mut().from_str(s)
    }

    fn parser<'a, T>(&'a self,
                     parser: fn(&ParserEnv<I, F>, I) -> ParseResult<T, I>)
                     -> LanguageParser<'a, I, F, T> {
        env_parser(self, parser)
    }

    fn precedence(&self, s: &str) -> i32 {
        match s {
            "*" | "/" | "%" => 7,
            "+" | "-" => 6,
            ":" | "++" => 5,
            "&&" => 3,
            "||" => 2,
            "$" => 0,
            "==" | "/=" | "<" | ">" | "<=" | ">=" => 4,
            // Primitive operators starts with # and has the op at the end
            _ if s.starts_with("#") => {
                let op = s[1..].trim_left_matches(|c: char| c.is_alphanumeric());
                self.precedence(op)
            }
            // Hack for some library operators
            "<<" | ">>" => 9,
            "<|" | "|>" => 0,
            // User-defined operators
            _ => 9,
        }
    }

    fn fixity(&self, i: &str) -> Fixity {
        match i {
            "*" | "/" | "%" | "+" | "-" | "==" | "/=" | "<" | ">" | "<=" | ">=" => Fixity::Left,
            ":" | "++" | "&&" | "||" | "$" => Fixity::Right,
            // Hack for some library operators
            ">>" | "|>" => Fixity::Left,
            "<<" | "<|" => Fixity::Right,
            // User-defined operators
            _ => Fixity::Left,
        }
    }

    fn ident<'a>(&'a self) -> LanguageParser<'a, I, F, Id> {
        self.parser(ParserEnv::<I, F>::parse_ident)
    }

    fn parse_ident(&self, input: I) -> ParseResult<Id, I> {
        self.parser(ParserEnv::<I, F>::parse_ident2)
            .map(|x| x.0)
            .parse_state(input)
    }

    /// Identifier parser which returns the identifier as well as the type of the identifier
    fn parse_ident2(&self, input: I) -> ParseResult<(Id, IdentType), I> {
        satisfy(|t: Token<&'input str>| {
                match t {
                    Token::Identifier(..) => true,
                    _ => false,
                }
            })
            .map(|t| {
                match t {
                    Token::Identifier(id, typ) => (self.intern(id), typ),
                    _ => unreachable!(),
                }
            })
            .parse_state(input)
    }

    fn ident_u<'a>(&'a self) -> LanguageParser<'a, I, F, Id::Untyped> {
        self.parser(ParserEnv::<I, F>::parse_untyped_ident)
    }

    fn parse_untyped_ident(&self, input: I) -> ParseResult<Id::Untyped, I> {
        self.ident()
            .map(AstId::to_id)
            .parse_state(input)
    }

    fn ident_type<'a>(&'a self) -> LanguageParser<'a, I, F, AstType<Id::Untyped>> {
        self.parser(ParserEnv::<I, F>::parse_ident_type)
    }

    fn parse_ident_type(&self, input: I) -> ParseResult<AstType<Id::Untyped>, I> {
        try(self.parser(ParserEnv::<I, F>::parse_ident2))
            .map(|(s, typ)| {
                debug!("Id: {:?}", s);
                if typ == IdentType::Variable {
                    Type::generic(Generic {
                        kind: Kind::variable(0),
                        id: s.to_id(),
                    })
                } else {
                    let ident_env = self.make_ident.borrow();
                    match ident_env.string(&s).parse() {
                        Ok(prim) => Type::builtin(prim),
                        Err(()) => Type::id(s.to_id()),
                    }
                }
            })
            .parse_state(input)
    }

    match_parser! { string_literal, String -> String }

    match_parser! { char_literal, Char -> char }

    match_parser! { float, Float -> f64 }

    match_parser! { integer, Integer -> i64 }

    match_parser! { byte, Byte -> u8 }

    match_parser! { doc_comment, DocComment -> String }

    fn typ<'a>(&'a self) -> LanguageParser<'a, I, F, AstType<Id::Untyped>> {
        self.parser(ParserEnv::<I, F>::parse_type)
    }

    fn parse_adt(&self,
                 return_type: &AstType<Id::Untyped>,
                 input: I)
                 -> ParseResult<AstType<Id::Untyped>, I> {
        let variant = (token(Token::Pipe),
                       self.ident_u(),
                       many(self.parser(ParserEnv::<I, F>::type_arg)))
            .map(|(_, id, args): (_, _, Vec<_>)| (id, Type::function(args, return_type.clone())));
        many1(variant)
            .map(Type::variants)
            .parse_state(input)
    }

    fn parse_type(&self, input: I) -> ParseResult<AstType<Id::Untyped>, I> {
        (many1(self.parser(ParserEnv::<I, F>::type_arg)),
         optional(token(Token::RightArrow).with(self.typ())))
            .map(|(mut arg, ret): (Vec<_>, _)| {
                let arg = if arg.len() == 1 {
                    arg.pop().unwrap()
                } else {
                    let x = arg.remove(0);
                    Type::app(x, arg)
                };
                debug!("Parse: {:?} -> {:?}", arg, ret);
                match ret {
                    Some(ret) => Type::function(vec![arg], ret),
                    None => arg,
                }
            })
            .parse_state(input)
    }

    fn record_type(&self, input: I) -> ParseResult<AstType<Id::Untyped>, I> {
        let field = self.parser(ParserEnv::<I, F>::parse_ident2)
            .then(|(id, typ)| {
                parser(move |input| {
                    if typ == IdentType::Constructor {
                        value((id.clone(), None)).parse_state(input)
                    } else {
                        token(Token::Colon)
                            .with(self.typ())
                            .map(|typ| (id.clone(), Some(typ)))
                            .parse_state(input)
                    }
                })
            });
        between(token(Token::Open(Delimiter::Brace)),
                token(Token::Close(Delimiter::Brace)),
                sep_end_by(field, token(Token::Comma)))
            .map(|fields: Vec<(Id, _)>| {
                let mut associated = Vec::new();
                let mut types = Vec::new();
                let mut ids = self.make_ident.borrow_mut();
                for (id, field) in fields {
                    let untyped_id = id.clone().to_id();
                    match field {
                        Some(typ) => {
                            types.push(Field {
                                name: untyped_id,
                                typ: typ,
                            })
                        }
                        None => {
                            let typ = Type::id(untyped_id.clone());
                            let short_name = String::from(Name::new(ids.string(&id))
                                .name()
                                .as_str());
                            associated.push(Field {
                                name: ids.from_str(&short_name).to_id(),
                                typ: Alias::new(untyped_id, vec![], typ),
                            });
                        }
                    }
                }
                Type::record(associated, types)
            })
            .parse_state(input)
    }

    fn type_arg(&self, input: I) -> ParseResult<AstType<Id::Untyped>, I> {
        choice::<[&mut Parser<Input = I, Output = AstType<Id::Untyped>>; 3],
                 _>([&mut self.parser(ParserEnv::<I, F>::record_type),
                     &mut between(token(Token::Open(Delimiter::Paren)),
                                  token(Token::Close(Delimiter::Paren)),
                                  optional(self.typ()))
                         .map(|typ| {
                             match typ {
                                 Some(typ) => typ,
                                 None => Type::unit(),
                             }
                         }),
                     &mut self.ident_type()])
            .parse_state(input)
    }

    fn type_decl(&self, input: I) -> ParseResult<LetOrType<Id>, I> {
        debug!("type_decl");
        let type_binding = |t| {
            (try(optional(self.doc_comment()).skip(token(t))),
             self.parser(ParserEnv::<I, F>::type_binding))
                .map(|(comment, mut bind)| {
                    bind.comment = comment;
                    bind
                })
        };
        (as_trait(&mut type_binding(Token::Type)),
         many(as_trait(&mut type_binding(Token::And))),
         token(Token::In).expected("`in` or an expression in the same column as the `let`"))
            .map(|(first, mut bindings, _): (_, Vec<_>, _)| {
                bindings.insert(0, first);
                LetOrType::Type(bindings)
            })
            .parse_state(input)
    }

    fn type_binding(&self, input: I) -> ParseResult<TypeBinding<Id::Untyped>, I> {
        (self.ident_u(), many(self.ident_u()))
            .then(|(name, args): (Id::Untyped, Vec<Id::Untyped>)| {
                let arg_types = args.iter()
                    .map(|id| {
                        Type::generic(Generic {
                            kind: Kind::variable(0),
                            id: id.clone(),
                        })
                    })
                    .collect();
                let return_type = if args.is_empty() {
                    Type::id(name.clone())
                } else {
                    Type::app(Type::id(name.clone()), arg_types)
                };
                token(Token::Equal)
                    .with(self.typ()
                        .or(parser(move |input| self.parse_adt(&return_type, input))))
                    .map(move |rhs_type| {
                        TypeBinding {
                            comment: None,
                            name: name.clone(),
                            alias: Alias::new(name.clone(),
                                              args.iter()
                                                  .map(|id| {
                                                      Generic {
                                                          kind: Kind::variable(0),
                                                          id: id.clone(),
                                                      }
                                                  })
                                                  .collect(),
                                              rhs_type),
                        }
                    })
            })
            .parse_state(input)
    }

    fn expr<'a>(&'a self) -> LanguageParser<'a, I, F, SpannedExpr<Id>> {
        self.parser(ParserEnv::<I, F>::top_expr)
    }

    fn parse_expr(&self, input: I) -> ParseResult<SpannedExpr<Id>, I> {
        let arg_expr1 = self.parser(ParserEnv::<I, F>::parse_arg);
        let arg_expr2 = self.parser(ParserEnv::<I, F>::parse_arg);
        (arg_expr1, many(arg_expr2))
            .map(|(f, args): (SpannedExpr<Id>, Vec<SpannedExpr<_>>)| {
                if let Some(end) = args.last().map(|last| last.span.end) {
                    pos::spanned2(f.span.start, end, Expr::Call(Box::new(f), args))
                } else {
                    f
                }
            })
            .parse_state(input)
    }

    /// Parses an expression which could be an argument to a function
    fn parse_arg(&self, input: I) -> ParseResult<SpannedExpr<Id>, I> {
        debug!("Expr start: {:?}", input.clone().uncons());
        let span = input.position();
        let loc = |expr| pos::spanned(span, expr);

        // To prevent stack overflows we push all binding groups (which are commonly deeply nested)
        // to a stack and construct the expressions afterwards
        let mut let_bindings = Vec::new();
        let mut resulting_expr;
        let mut input = input;
        let mut declaration_parser = self.parser(ParserEnv::<I, F>::type_decl)
            .or(self.parser(ParserEnv::<I, F>::let_in))
            .map(loc);
        loop {
            match declaration_parser.parse_lazy(input.clone()) {
                Ok((bindings, new_input)) => {
                    let_bindings.push(bindings);
                    input = new_input.into_inner();
                }
                Err(err @ Consumed::Consumed(_)) => return Err(err),
                Err(Consumed::Empty(err)) => {
                    // If a let or type binding has been parsed then any kind of expression can
                    // follow
                    let mut expr_parser = if let_bindings.is_empty() {
                        self.parser(ParserEnv::<I, F>::rest_expr)
                    } else {
                        self.expr()
                    };
                    let (expr, new_input) = try!(expr_parser.parse_state(input)
                        .map_err(|err2| err2.map(|err2| err.merge(err2))));
                    resulting_expr = expr;
                    input = new_input.into_inner();
                    break;
                }
            }
        }
        for binding in let_bindings.into_iter().rev() {
            resulting_expr = pos::spanned(binding.span,
                                          match binding.value {
                                              LetOrType::Let(bindings) => {
                                                  Expr::Let(bindings, Box::new(resulting_expr))
                                              }
                                              LetOrType::Type(bindings) => {
                                                  Expr::Type(bindings, Box::new(resulting_expr))
                                              }
                                          });
        }
        Ok((resulting_expr, Consumed::Consumed(input)))
    }

    fn rest_expr(&self, input: I) -> ParseResult<SpannedExpr<Id>, I> {
        let span = input.position();
        let loc = |expr| pos::spanned(span, expr);

        choice::<[&mut Parser<Input = I, Output = SpannedExpr<Id>>; 12],
                 _>([&mut parser(|input| self.if_else(input)),
                     &mut self.parser(ParserEnv::<I, F>::case_of),
                     &mut self.parser(ParserEnv::<I, F>::lambda),
                     &mut self.integer()
                         .map(|i| loc(Expr::Literal(LiteralEnum::Integer(i)))),
                     &mut self.byte()
                         .map(|i| loc(Expr::Literal(LiteralEnum::Byte(i)))),
                     &mut self.float()
                         .map(|f| loc(Expr::Literal(LiteralEnum::Float(f)))),
                     &mut self.ident()
                         .map(Expr::Identifier)
                         .map(&loc),
                     &mut self.parser(ParserEnv::<I, F>::record).map(&loc),
                     &mut between(token(Token::Open(Delimiter::Paren)),
                                  token(Token::Close(Delimiter::Paren)),
                                  optional(self.expr()).map(|expr| {
                                      match expr {
                                          Some(expr) => expr,
                                          None => loc(Expr::Tuple(vec![])),
                                      }
                                  })),
                     &mut self.string_literal()
                         .map(|s| loc(Expr::Literal(LiteralEnum::String(s)))),
                     &mut self.char_literal()
                         .map(|s| loc(Expr::Literal(LiteralEnum::Char(s)))),
                     &mut between(token(Token::Open(Delimiter::Bracket)),
                                  token(Token::Close(Delimiter::Bracket)),
                                  sep_end_by(self.expr(), token(Token::Comma)))
                         .map(|exprs| {
                             loc(Expr::Array(Array {
                                 id: self.empty_id.clone(),
                                 expressions: exprs,
                             }))
                         })])
            .and(self.parser(Self::fields))
            .map(|(expr, fields): (_, Vec<_>)| {
                debug!("Parsed expr {:?}", expr);
                fields.into_iter().fold(expr, |expr, (id, end)| {
                    pos::spanned2(span.start, end, Expr::FieldAccess(Box::new(expr), id))
                })
            })
            .parse_state(input)

    }

    // The BytePos is the end of the field
    fn fields(&self, input: I) -> ParseResult<Vec<(Id, BytePos)>, I> {
        let mut fields = Vec::new();
        let mut input = Consumed::Empty(input);
        loop {
            input = match input.clone().combine(|input| token(Token::Dot).parse_lazy(input)) {
                Ok((_, input)) => input,
                Err(_) => return Ok((fields, input)),
            };
            let end = input.clone().into_inner().position().end;
            input = match input.clone().combine(|input| self.ident().parse_lazy(input)) {
                Ok((field, input)) => {
                    fields.push((field, end));
                    input
                }
                Err(err) => {
                    // If not field where found after the '.' add an empty field so that running
                    // completion can be done for the attempt to access the field
                    self.errors
                        .borrow_mut()
                        .error(static_error(err.into_inner()));
                    fields.push((self.empty_id.clone(), end));
                    return Ok((fields, input));
                }
            };
        }
    }

    fn op<'a>(&'a self) -> LanguageParser<'a, I, F, &'input str> {
        fn inner<'input, I, Id, F>(_: &ParserEnv<I, F>, input: I) -> ParseResult<&'input str, I>
            where I: Stream<Item = Token<&'input str>, Range = Token<&'input str>, Position = Span<BytePos>>,
                  F: IdentEnv<Ident = Id>,
                  Id: AstId + Clone + PartialEq + fmt::Debug,
                  I::Range: fmt::Debug
        {
            satisfy(|t: Token<&'input str>| {
                    match t {
                        Token::Operator(_) => true,
                        _ => false,
                    }
                })
                .map(|t| {
                    match t {
                        Token::Operator(s) => s,
                        _ => unreachable!(),
                    }
                })
                .parse_state(input)
        }
        self.parser(inner)
    }

    /// Parses any sort of expression
    fn top_expr(&self, input: I) -> ParseResult<SpannedExpr<Id>, I> {
        let term = self.parser(ParserEnv::<I, F>::parse_expr);
        let op = self.op()
            .map(|op| {
                let assoc = Assoc {
                    precedence: self.precedence(&op),
                    fixity: self.fixity(&op),
                };
                (op, assoc)
            });
        between(token(Token::OpenBlock),
                token(Token::CloseBlock),
                self.expr())
            .or(sep_by1(expression_parser(term, op, |l, op, r| {
                            pos::spanned2(l.span.start,
                                          r.span.end,
                                          Expr::BinOp(Box::new(l), self.intern(&op), Box::new(r)))
                        }),
                        token(Token::Semi))
                .map(|mut exprs: Vec<SpannedExpr<Id>>| {
                    if exprs.len() == 1 {
                        exprs.pop().unwrap()
                    } else {
                        pos::spanned(exprs.first().expect("Expr in block").span,
                                     Expr::Block(exprs))
                    }
                }))
            .parse_state(input)
    }

    fn lambda(&self, input: I) -> ParseResult<SpannedExpr<Id>, I> {
        let start = input.position().start;
        (token(Token::Lambda), many(self.ident()), token(Token::RightArrow), self.expr())
            .map(|(_, args, _, expr)| {
                pos::spanned2(start,
                              expr.span.end,
                              Expr::Lambda(Lambda {
                                  id: self.empty_id.clone(),
                                  arguments: args,
                                  body: Box::new(expr),
                              }))
            })
            .parse_state(input)
    }

    fn case_of(&self, input: I) -> ParseResult<SpannedExpr<Id>, I> {
        let alt = (token(Token::Pipe), self.pattern(), token(Token::RightArrow), self.expr())
            .map(|(_, p, _, e)| {
                Alternative {
                    pattern: p,
                    expression: e,
                }
            });
        let start = input.position().start;
        (token(Token::Match), self.expr(), token(Token::With), many1::<Vec<_>, _>(alt))
            .map(|(_, e, _, alts)| {
                pos::spanned2(start,
                              alts.last().expect("No alternatives").expression.span.end,
                              Expr::Match(Box::new(e), alts))
            })
            .parse_state(input)
    }

    fn pattern<'a>(&'a self) -> LanguageParser<'a, I, F, SpannedPattern<Id>> {
        self.parser(ParserEnv::<I, F>::parse_pattern)
    }

    fn parse_pattern(&self, input: I) -> ParseResult<SpannedPattern<Id>, I> {
        self.record_parser(self.ident_u(), self.ident_u(), |record| {
            let span = input.position();

            self.parser(ParserEnv::<I, F>::parse_ident2)
                .then(|(id, typ)| {
                    parser(move |input| {
                        if typ == IdentType::Constructor {
                            many(self.ident())
                                .parse_state(input)
                                .map(|(args, input)| {
                                    (Pattern::Constructor(id.clone(), args), input)
                                })
                        } else {
                            Ok((Pattern::Identifier(id.clone()), Consumed::Empty(input)))
                        }
                    })
                })
                .or(record.map(|fields: Vec<_>| {
                    let mut types = Vec::new();
                    let mut patterns = Vec::new();
                    for (id, field) in fields {
                        match field {
                            Ok(name) => types.push((id, name)),
                            Err(pattern) => patterns.push((id, pattern)),
                        }
                    }
                    Pattern::Record {
                        id: self.empty_id.clone(),
                        types: types,
                        fields: patterns,
                    }
                }))
                .map(|p| pos::spanned(span, p))
                .or(between(token(Token::Open(Delimiter::Paren)),
                            token(Token::Close(Delimiter::Paren)),
                            self.pattern()))
                .parse_state(input)
        })
    }

    fn if_else(&self, input: I) -> ParseResult<SpannedExpr<Id>, I> {
        let start = input.position().start;
        (token(Token::If),
         self.expr(),
         token(Token::Then),
         self.expr(),
         token(Token::Else),
         self.expr())
            .map(|(_, b, _, t, _, f)| {
                pos::spanned(Span {
                                 start: start,
                                 end: f.span.end,
                             },
                             Expr::IfElse(Box::new(b), Box::new(t), Some(Box::new(f))))
            })
            .parse_state(input)
    }

    fn let_in(&self, input: I) -> ParseResult<LetOrType<Id>, I> {
        let binding = |t| {
            (try(optional(self.doc_comment()).skip(token(t))),
             self.parser(ParserEnv::<I, F>::binding))
                .map(|(comment, mut bind)| {
                    bind.comment = comment;
                    bind
                })
        };
        (as_trait(&mut binding(Token::Let)),
         many(as_trait(&mut binding(Token::And))),
         token(Token::In).expected("`in` or an expression in the same column as the `let`"))
            .map(|(b, bindings, _)| {
                let mut bindings: Vec<_> = bindings;
                bindings.insert(0, b);
                LetOrType::Let(bindings)
            })
            .parse_state(input)
    }

    fn binding(&self, input: I) -> ParseResult<Binding<Id>, I> {
        let (name, input) = try!(self.pattern().parse_state(input));
        let (arguments, input) = match name.value {
            Pattern::Identifier(_) => {
                try!(input.combine(|input| many(self.ident()).parse_state(input)))
            }
            _ => (Vec::new(), input),
        };
        let type_sig = token(Token::Colon).with(self.typ());
        let ((typ, _, e), input) = try!(input.combine(|input| {
            (optional(type_sig), token(Token::Equal), self.expr()).parse_state(input)
        }));
        Ok((Binding {
            comment: None,
            name: name,
            typ: typ,
            arguments: arguments,
            expression: e,
        },
            input))
    }

    fn record(&self, input: I) -> ParseResult<Expr<Id>, I> {
        self.record_parser(self.typ(), self.expr(), |record| {
            record.map(|fields: Vec<_>| {
                    let mut types = Vec::new();
                    let mut exprs = Vec::new();
                    for (id, field) in fields {
                        match field {
                            Ok(typ) => types.push((id, typ)),
                            Err(expr) => exprs.push((id, expr)),
                        }
                    }
                    Expr::Record {
                        typ: self.empty_id.clone(),
                        types: types,
                        exprs: exprs,
                    }
                })
                .parse_state(input)
        })
    }

    fn record_parser<'a, P1, P2, O, G, R>(&'a self, ref p1: P1, ref p2: P2, f: G) -> R
        where P1: Parser<Input = I> + Clone,
              P2: Parser<Input = I> + Clone,
              O: FromIterator<(Id::Untyped, Result<Option<P1::Output>, Option<P2::Output>>)>,
              G: FnOnce(&mut Parser<Input = I, Output = O>) -> R
    {
        let mut field = self.parser(ParserEnv::<I, F>::parse_ident2)
            .then(move |(id, typ)| {
                parser(move |input| {
                    let result = if typ == IdentType::Constructor {
                        optional(token(Token::Equal).with(p1.clone()))
                            .map(Ok)
                            .parse_state(input)

                    } else {
                        optional(token(Token::Equal).with(p2.clone()))
                            .map(Err)
                            .parse_state(input)
                    };
                    result.map(|(x, input)| ((id.clone().to_id(), x), input))
                })
            });
        let mut parser = between(token(Token::Open(Delimiter::Brace)),
                                 token(Token::Close(Delimiter::Brace)),
                                 sep_end_by(&mut field, token(Token::Comma)));
        f(&mut parser)
    }
}

/// Parses a string to an AST which contains has identifiers which also contains a field for storing
/// type information. The type will just be a dummy value until the AST has passed typechecking
pub fn parse_tc
    (symbols: &mut SymbolModule,
     input: &str)
     -> Result<SpannedExpr<TcIdent<Symbol>>, (Option<SpannedExpr<TcIdent<Symbol>>>, Errors<Error>)> {
    let mut env = ast::TcIdentEnv {
        typ: Type::hole(),
        env: symbols,
    };
    parse_expr(&mut env, input)
}

#[cfg(feature = "test")]
pub fn parse_string<'env, 'input>
    (make_ident: &'env mut IdentEnv<Ident = String>,
     input: &'input str)
     -> Result<SpannedExpr<String>, (Option<SpannedExpr<String>>, Errors<Error>)> {
    parse_expr(make_ident, input)
}

/// Parses a gluon expression
pub fn parse_expr<'env, 'input, Id>
    (make_ident: &'env mut IdentEnv<Ident = Id>,
     input: &'input str)
     -> Result<SpannedExpr<Id>, (Option<SpannedExpr<Id>>, Errors<Error>)>
    where Id: AstId + Clone + PartialEq + fmt::Debug
{
    let make_ident = Rc::new(RefCell::new(make_ident));
    let lexer = Lexer::new(input);
    let env = ParserEnv {
        empty_id: make_ident.borrow_mut().from_str(""),
        make_ident: make_ident.clone(),
        errors: RefCell::new(Errors::new()),
        env: PhantomData,
    };
    let buffer = BufferedStream::new(lexer, 10);
    let stream = Wrapper { stream: buffer.as_stream() };

    let result = env.expr()
        .parse(stream)
        .map(|t| t.0);

    let mut errors = env.errors.into_inner();
    match result {
        Ok(x) => {
            if !errors.has_errors() {
                Ok(x)
            } else {
                Err((Some(x), errors))
            }
        }
        Err(err) => {
            errors.errors.push(static_error(err));
            Err((None, errors))
        }
    }
}

fn static_error<'input, I>(error: ParseError<I>) -> Error
    where I: Stream<Item = Token<&'input str>, Range = Token<&'input str>, Position = Span<BytePos>>
{
    let errors = error.errors
        .into_iter()
        .map(static_error_)
        .collect();
    ParseError {
        position: error.position.start,
        errors: errors,
    }
}

// Converts an error into a static error by transforming any range arguments into strings
fn static_error_<'input>(e: CombineError<Token<&'input str>, Token<&'input str>>)
                         -> CombineError<Token<String>, Token<String>> {
    let static_info = |i: Info<Token<&'input str>, Token<&'input str>>| {
        match i {
            Info::Token(t) => Info::Token(t.map(|id| String::from(*id))),
            Info::Range(t) => Info::Token(t.map(|id| String::from(*id))),
            Info::Borrowed(t) => Info::Borrowed(t),
            Info::Owned(t) => Info::Owned(t),
        }
    };
    match e {
        CombineError::Unexpected(t) => CombineError::Unexpected(static_info(t)),
        CombineError::Expected(t) => CombineError::Expected(static_info(t)),
        CombineError::Message(t) => CombineError::Message(static_info(t)),
        CombineError::Other(t) => CombineError::Other(t),
    }
}
