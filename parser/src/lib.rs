//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.
#[macro_use]
extern crate log;
extern crate base;
extern crate combine;
extern crate combine_language;

pub mod lexer;

use std::cell::RefCell;
use std::fmt;
use std::iter::FromIterator;
use std::rc::Rc;

use base::ast;
use base::ast::*;
use base::types::{Type, Generic, Alias, Field, Kind, TypeVariable};
use base::symbol::{Name, Symbol, SymbolModule};

use combine::primitives::{Consumed, Stream, StreamOnce, Error as CombineError, Info,
                          BufferedStream, SourcePosition};
use combine::combinator::EnvParser;
use combine::{between, choice, env_parser, many, many1, optional, parser, satisfy, sep_by,
              sep_by1, token, try, value, ParseError, ParseResult, Parser, ParserExt};
use combine_language::{Assoc, Fixity, expression_parser};

use lexer::{Lexer, Delimiter, Token};

pub type Error = ParseError<BufferedStream<'static,
                                           Lexer<'static,
                                                 &'static str,
                                                 &'static mut IdentEnv<Ident = String>>>>;

/// Parser passes the environment to each parser function
type LanguageParser<'b, I: 'b, F: 'b, T> = EnvParser<&'b ParserEnv<I, F>, I, T>;

/// `ParserEnv` is passed around to all individual parsers so that identifiers can always be
/// constructed through calling `make_ident`.
struct ParserEnv<I, F>
    where F: IdentEnv
{
    empty_id: F::Ident,
    make_ident: Rc<RefCell<F>>,
    env: ::std::marker::PhantomData<I>,
}

// Wrapper type to reduce typechecking times
#[derive(Clone)]
struct Wrapper<'a: 'l, 's: 'l, 'l, Id: Clone + PartialEq + fmt::Debug + 'a> {
    stream: BufferedStream<'l, Lexer<'s, &'s str, &'a mut IdentEnv<Ident = Id>>>,
}

impl<'a, 's, 'l, Id> StreamOnce for Wrapper<'a, 's, 'l, Id>
    where Id: Clone + PartialEq + fmt::Debug
{
    type Item = Token<Id>;
    type Range = Token<Id>;
    type Position = SourcePosition;

    fn uncons(&mut self) -> Result<Token<Id>, ::lexer::Error<Id>> {
        self.stream.uncons()
    }

    fn position(&self) -> Self::Position {
        self.stream.position()
    }
}

enum LetOrType<Id: AstId> {
    Let(Vec<Binding<Id>>),
    Type(Vec<TypeBinding<Id::Untyped>>),
}

macro_rules! match_parser {
    ($function: ident, $variant: ident -> $typ: ty) => {
        fn $function(&'s self) -> LanguageParser<'s, I, F, $typ> {
            fn inner<I, Id, F>(_: &ParserEnv<I, F>, input: I) -> ParseResult<$typ, I>
                where I: Stream<Item = Token<Id>>,
                      F: IdentEnv<Ident = Id>,
                      Id: AstId + Clone + PartialEq + fmt::Debug,
                      I::Range: fmt::Debug
            {
                satisfy(|t: Token<Id>| {
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

impl<'s, I, Id, F> ParserEnv<I, F>
    where I: Stream<Item = Token<Id>, Position = SourcePosition>,
          F: IdentEnv<Ident = Id>,
          Id: AstId + Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug + 's
{
    fn parser<T>(&'s self,
                 parser: fn(&ParserEnv<I, F>, I) -> ParseResult<T, I>)
                 -> LanguageParser<'s, I, F, T> {
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
            _ => 9,
        }
    }

    fn fixity(&self, i: &str) -> Fixity {
        match i {
            "*" | "/" | "%" | "+" | "-" | "==" | "/=" | "<" | ">" | "<=" | ">=" => Fixity::Left,
            ":" | "++" | "&&" | "||" | "$" => Fixity::Right,
            _ => Fixity::Left,
        }
    }

    fn ident(&'s self) -> LanguageParser<'s, I, F, Id> {
        self.parser(ParserEnv::<I, F>::parse_ident)
    }
    fn parse_ident(&self, input: I) -> ParseResult<Id, I> {
        self.parser(ParserEnv::<I, F>::parse_ident2)
            .map(|x| x.0)
            .parse_state(input)
    }

    /// Identifier parser which returns `(id, true)` if the identifier is a constructor
    /// (Starts with an uppercase letter
    fn parse_ident2(&self, input: I) -> ParseResult<(Id, bool), I> {
        satisfy(|t: Token<Id>| {
            match t {
                Token::Identifier(..) => true,
                _ => false,
            }
        })
            .map(|t| {
                match t {
                    Token::Identifier(id, is_ctor) => (id, is_ctor),
                    _ => unreachable!(),
                }
            })
            .parse_state(input)
    }
    fn ident_u(&'s self) -> LanguageParser<'s, I, F, Id::Untyped> {
        self.parser(ParserEnv::<I, F>::parse_untyped_ident)
    }
    fn parse_untyped_ident(&self, input: I) -> ParseResult<Id::Untyped, I> {
        self.ident()
            .map(AstId::to_id)
            .parse_state(input)
    }

    fn ident_type(&'s self) -> LanguageParser<'s, I, F, ASTType<Id::Untyped>> {
        self.parser(ParserEnv::<I, F>::parse_ident_type)
    }
    fn parse_ident_type(&self, input: I) -> ParseResult<ASTType<Id::Untyped>, I> {
        try(self.parser(ParserEnv::<I, F>::parse_ident2))
            .map(|(s, is_ctor)| {
                debug!("Id: {:?}", s);
                if !is_ctor {
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

    match_parser! { doc_comment, DocComment -> String }

    fn typ(&'s self) -> LanguageParser<'s, I, F, ASTType<Id::Untyped>> {
        self.parser(ParserEnv::<I, F>::parse_type)
    }

    fn parse_adt(&self,
                 return_type: &ASTType<Id::Untyped>,
                 input: I)
                 -> ParseResult<ASTType<Id::Untyped>, I> {
        let variant = (token(Token::Pipe),
                       self.ident_u(),
                       many(self.parser(ParserEnv::<I, F>::type_arg)))
                          .map(|(_, id, args): (_, _, Vec<_>)| {
                              (id, Type::function(args, return_type.clone()))
                          });
        many1(variant)
            .map(Type::variants)
            .parse_state(input)
    }

    fn parse_type(&self, input: I) -> ParseResult<ASTType<Id::Untyped>, I> {
        (many1(self.parser(ParserEnv::<I, F>::type_arg)),
         optional(token(Token::RightArrow).with(self.typ())))
            .map(|(mut arg, ret): (Vec<_>, _)| {
                let arg = if arg.len() == 1 {
                    arg.pop().unwrap()
                } else {
                    let x = arg.remove(0);
                    Type::data(x, arg)
                };
                debug!("Parse: {:?} -> {:?}", arg, ret);
                match ret {
                    Some(ret) => Type::function(vec![arg], ret),
                    None => arg,
                }
            })
            .parse_state(input)
    }

    fn record_type(&self, input: I) -> ParseResult<ASTType<Id::Untyped>, I> {
        let field = self.parser(ParserEnv::<I, F>::parse_ident2)
                        .then(|(id, is_ctor)| {
                            parser(move |input| {
                                if is_ctor {
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
                sep_by(field, token(Token::Comma)))
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
                                typ: Alias {
                                    name: untyped_id,
                                    args: vec![],
                                    typ: Some(typ),
                                },
                            });
                        }
                    }
                }
                Type::record(associated, types)
            })
            .parse_state(input)
    }

    fn type_arg(&self, input: I) -> ParseResult<ASTType<Id::Untyped>, I> {
        choice::<[&mut Parser<Input = I, Output = ASTType<Id::Untyped>>; 4],
                 _>([&mut between(token(Token::Open(Delimiter::Bracket)),
                                  token(Token::Close(Delimiter::Bracket)),
                                  self.typ())
                              .map(Type::array),
                     &mut self.parser(ParserEnv::<I, F>::record_type),
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
                    Type::data(Type::id(name.clone()), arg_types)
                };
                token(Token::Equal)
                    .with(self.typ()
                              .or(parser(move |input| self.parse_adt(&return_type, input))))
                    .map(move |rhs_type| {
                        TypeBinding {
                            comment: None,
                            name: name.clone(),
                            alias: Alias {
                                name: name.clone(),
                                args: args.iter()
                                          .map(|id| {
                                              Generic {
                                                  kind: Kind::variable(0),
                                                  id: id.clone(),
                                              }
                                          })
                                          .collect(),
                                typ: Some(rhs_type),
                            },
                        }
                    })
            })
            .parse_state(input)
    }

    fn expr(&'s self) -> LanguageParser<'s, I, F, LExpr<Id>> {
        self.parser(ParserEnv::<I, F>::top_expr)
    }

    fn parse_expr(&self, input: I) -> ParseResult<LExpr<Id>, I> {
        let arg_expr1 = self.parser(ParserEnv::<I, F>::parse_arg);
        let arg_expr2 = self.parser(ParserEnv::<I, F>::parse_arg);
        (arg_expr1, many(arg_expr2))
            .map(|(f, args): (LExpr<Id>, Vec<_>)| {
                if args.len() > 0 {
                    located(f.location, Expr::Call(Box::new(f), args))
                } else {
                    f
                }
            })
            .parse_state(input)
    }

    /// Parses an expression which could be an argument to a function
    fn parse_arg(&self, input: I) -> ParseResult<LExpr<Id>, I> {
        debug!("Expr start: {:?}", input.clone().uncons());
        let position = input.position();
        let loc = |expr| {
            located(Location {
                        column: position.column,
                        row: position.line,
                        absolute: 0,
                    },
                    expr)
        };

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
                                                            .map_err(|err2| {
                                                                err2.map(|err2| err.merge(err2))
                                                            }));
                    resulting_expr = expr;
                    input = new_input.into_inner();
                    break;
                }
            }
        }
        for Located { location, value } in let_bindings.into_iter().rev() {
            resulting_expr = located(location,
                                     match value {
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

    fn rest_expr(&self, input: I) -> ParseResult<LExpr<Id>, I> {
        let position = input.position();
        let loc = |expr| {
            located(Location {
                        column: position.column,
                        row: position.line,
                        absolute: 0,
                    },
                    expr)
        };
        choice::<[&mut Parser<Input = I, Output = LExpr<Id>>; 11],
                 _>([&mut parser(|input| self.if_else(input)).map(&loc),
                     &mut self.parser(ParserEnv::<I, F>::case_of).map(&loc),
                     &mut self.parser(ParserEnv::<I, F>::lambda).map(&loc),
                     &mut self.integer()
                              .map(|i| loc(Expr::Literal(LiteralEnum::Integer(i)))),
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
                                  sep_by(self.expr(), token(Token::Comma)))
                              .map(|exprs| {
                                  loc(Expr::Array(Array {
                                      id: self.empty_id.clone(),
                                      expressions: exprs,
                                  }))
                              })])
            .and(many(token(Token::Dot).with(self.ident())))
            .map(|(expr, fields): (_, Vec<_>)| {
                debug!("Parsed expr {:?}", expr);
                fields.into_iter().fold(expr,
                                        |expr, field| loc(Expr::FieldAccess(Box::new(expr), field)))
            })
            .parse_state(input)

    }

    match_parser! { op, Operator -> Id }

    /// Parses any sort of expression
    fn top_expr(&self, input: I) -> ParseResult<LExpr<Id>, I> {
        let term = self.parser(ParserEnv::<I, F>::parse_expr);
        let op = self.op()
                     .map(|op| {
                         let assoc = {
                             let ids = self.make_ident.borrow();
                             let op_str = ids.string(&op);
                             Assoc {
                                 precedence: self.precedence(op_str),
                                 fixity: self.fixity(op_str),
                             }
                         };
                         (op, assoc)
                     });
        between(token(Token::OpenBlock),
                token(Token::CloseBlock),
                self.expr())
            .or(sep_by1(expression_parser(term, op, |l, op, r| {
                            let loc = l.location.clone();
                            located(loc, Expr::BinOp(Box::new(l), op.clone(), Box::new(r)))
                        }),
                        token(Token::Semi))
                    .map(|mut exprs: Vec<LExpr<Id>>| {
                        if exprs.len() == 1 {
                            exprs.pop().unwrap()
                        } else {
                            located(exprs.first().expect("Expr in block").location,
                                    Expr::Block(exprs))
                        }
                    }))
            .parse_state(input)
    }

    fn lambda(&self, input: I) -> ParseResult<Expr<Id>, I> {
        (token(Token::Lambda), many(self.ident()), token(Token::RightArrow), self.expr())
            .map(|(_, args, _, expr)| {
                Expr::Lambda(Lambda {
                    id: self.empty_id.clone(),
                    arguments: args,
                    body: Box::new(expr),
                })
            })
            .parse_state(input)
    }

    fn case_of(&self, input: I) -> ParseResult<Expr<Id>, I> {
        let alt = (token(Token::Pipe), self.pattern(), token(Token::RightArrow), self.expr())
                      .map(|(_, p, _, e)| {
                          Alternative {
                              pattern: p,
                              expression: e,
                          }
                      });
        (token(Token::Match), self.expr(), token(Token::With), many1(alt))
            .map(|(_, e, _, alts)| Expr::Match(Box::new(e), alts))
            .parse_state(input)
    }

    fn pattern(&'s self) -> LanguageParser<'s, I, F, LPattern<Id>> {
        self.parser(ParserEnv::<I, F>::parse_pattern)
    }

    fn parse_pattern(&self, input: I) -> ParseResult<LPattern<Id>, I> {
        self.record_parser(self.ident_u(), self.ident_u(), |record| {
            let position = input.position();
            let location = Location {
                column: position.column,
                row: position.line,
                absolute: 0,
            };
            self.parser(ParserEnv::<I, F>::parse_ident2)
                .then(|(id, is_ctor)| {
                    parser(move |input| {
                        if is_ctor {
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
                .map(|p| located(location, p))
                .or(between(token(Token::Open(Delimiter::Paren)),
                            token(Token::Close(Delimiter::Paren)),
                            self.pattern()))
                .parse_state(input)
        })
    }

    fn if_else(&self, input: I) -> ParseResult<Expr<Id>, I> {
        (token(Token::If),
         self.expr(),
         token(Token::Then),
         self.expr(),
         token(Token::Else),
         self.expr())
            .map(|(_, b, _, t, _, f)| Expr::IfElse(Box::new(b), Box::new(t), Some(Box::new(f))))
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

    fn record_parser<P1, P2, O, G, R>(&'s self, ref p1: P1, ref p2: P2, f: G) -> R
        where P1: Parser<Input = I> + Clone,
              P2: Parser<Input = I> + Clone,
              O: FromIterator<(Id::Untyped, Result<Option<P1::Output>, Option<P2::Output>>)>,
              G: FnOnce(&mut Parser<Input = I, Output = O>) -> R
    {
        let mut field = self.parser(ParserEnv::<I, F>::parse_ident2)
                            .then(move |(id, is_ctor)| {
                                parser(move |input| {
                                    let result = if is_ctor {
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
                                 sep_by(&mut field, token(Token::Comma)));
        f(&mut parser)
    }
}

use lexer::PToken;

///Parses a string to an AST which contains has identifiers which also contains a field for storing
///type information. The type will just be a dummy value until the AST has passed typechecking
pub fn parse_tc(symbols: &mut SymbolModule, input: &str) -> Result<LExpr<TcIdent<Symbol>>, Error> {
    let mut env = ast::TcIdentEnv {
        typ: Type::variable(TypeVariable {
            id: 0,
            kind: Kind::star(),
        }),
        env: symbols,
    };
    parse_module(None, &mut env, input)
}

#[cfg(feature = "test")]
pub fn parse_string<'a, 's>(layout: Option<fn(&mut Lexer<'s,
                                                         &'s str,
                                                         &'a mut IdentEnv<Ident = String>>,
                                              PToken<String>)
                                              -> Result<Token<String>, ::lexer::Error<String>>>,
                            make_ident: &'a mut IdentEnv<Ident = String>,
                            input: &'s str)
                            -> Result<LExpr<String>, Error> {
    parse_module(layout, make_ident, input)
}

pub fn parse_module<'a, 's, Id>(layout: Option<fn(&mut Lexer<'s,
                                                             &'s str,
                                                             &'a mut IdentEnv<Ident = Id>>,
                                                  PToken<Id>)
                                                  -> Result<Token<Id>, ::lexer::Error<Id>>>,
                                make_ident: &'a mut IdentEnv<Ident = Id>,
                                input: &'s str)
                                -> Result<LExpr<Id>, Error>
    where Id: AstId + Clone + PartialEq + fmt::Debug
{
    let make_ident = Rc::new(RefCell::new(make_ident));
    let lexer = Lexer::<&str, &mut IdentEnv<Ident = Id>>::new(layout, input, make_ident.clone());
    let empty_id = make_ident.borrow_mut().from_str("");
    let env = ParserEnv {
        empty_id: empty_id,
        make_ident: make_ident.clone(),
        env: ::std::marker::PhantomData,
    };
    let buffer = BufferedStream::new(lexer, 10);
    let stream = Wrapper { stream: buffer.as_stream() };

    env.expr()
       .parse(stream)
       .map(|t| t.0)
       .map_err(|err| {
           let errors = err.errors
                           .into_iter()
                           .map(|t| static_error(&mut *make_ident.borrow_mut(), t))
                           .collect();
           ParseError {
               position: err.position,
               errors: errors,
           }
       })
}

// Converts an error into a static error by transforming any range arguments into strings
fn static_error<Id>(make_ident: &mut IdentEnv<Ident = Id>,
                    e: CombineError<Token<Id>, Token<Id>>)
                    -> CombineError<Token<String>, Token<String>> {
    let static_info = |i: Info<Token<Id>, Token<Id>>| {
        match i {
            Info::Token(t) => Info::Token(t.map(|id| String::from(make_ident.string(id)))),
            Info::Range(t) => Info::Token(t.map(|id| String::from(make_ident.string(id)))),
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
