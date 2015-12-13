//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.
#[macro_use]
extern crate log;
extern crate env_logger;
extern crate base;
extern crate combine;
extern crate combine_language;

use std::cell::RefCell;
use std::error::Error as StdError;
use std::fmt;
use std::iter::FromIterator;
use std::rc::Rc;

use base::ast;
use base::ast::*;
use base::gc::Gc;
use base::interner::{Interner, InternedStr};

use combine::primitives::{Consumed, Stream, Error, Info};
use combine::combinator::EnvParser;
use combine::*;
use combine_language::{LanguageEnv, LanguageDef, Identifier, Assoc, Fixity, expression_parser};

/// Parser passes the environment to each parser function
type LanguageParser<'a: 'b, 'b, I: 'b, F: 'b, T> = EnvParser<&'b ParserEnv<'a, I, F>, I, T>;

/// `ParserEnv` is passed around to all individual parsers so that identifiers can always be
/// constructed through calling `make_ident`.
struct ParserEnv<'a, I, F>
    where I: Stream<Item = char>
{
    env: LanguageEnv<'a, I>,
    make_ident: RefCell<F>,
}

impl<'a, I, F> ::std::ops::Deref for ParserEnv<'a, I, F> where I: Stream<Item = char>
{
    type Target = LanguageEnv<'a, I>;
    fn deref(&self) -> &LanguageEnv<'a, I> {
        &self.env
    }
}

impl<'a, 's, I, Id, F> ParserEnv<'a, I, F>
    where I: Stream<Item = char> + 'a,
          F: FnMut(&str) -> Id + 'a,
          Id: AstId + AsRef<str> + Clone,
          I::Range: fmt::Debug + 's
{
    fn intern(&self, s: &str) -> Id {
        (&mut *self.make_ident.borrow_mut())(s)
    }

    fn parser<T>(&'s self,
                 parser: fn(&ParserEnv<'a, I, F>, State<I>) -> ParseResult<T, I>)
                 -> LanguageParser<'a, 's, I, F, T> {
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
            "*" |
            "/" |
            "%" |
            "+" |
            "-" |
            "==" |
            "/=" |
            "<" |
            ">" |
            "<=" |
            ">=" => Fixity::Left,
            ":" | "++" | "&&" | "||" | "$" => Fixity::Right,
            _ => Fixity::Left,
        }
    }

    fn ident(&'s self) -> LanguageParser<'a, 's, I, F, Id> {
        self.parser(ParserEnv::parse_ident)
    }
    fn parse_ident(&self, input: State<I>) -> ParseResult<Id, I> {
        self.parser(ParserEnv::parse_ident2)
            .map(|x| x.0)
            .parse_state(input)
    }

    /// Identifier parser which returns `(id, true)` if the identifier is a constructor
    /// (Starts with an uppercase letter
    fn parse_ident2(&self, input: State<I>) -> ParseResult<(Id, bool), I> {
        try(self.env.identifier())
            .or(try(self.parens(self.env.op())))
            .map(|s| {
                debug!("Id: {}", s);
                (self.intern(&s), s.chars().next().unwrap().is_uppercase())
            })
            .parse_state(input)
    }
    fn ident_u(&'s self) -> LanguageParser<'a, 's, I, F, Id::Untyped> {
        self.parser(ParserEnv::parse_untyped_ident)
    }
    fn parse_untyped_ident(&self, input: State<I>) -> ParseResult<Id::Untyped, I> {
        self.ident()
            .map(AstId::to_id)
            .parse_state(input)
    }

    fn ident_type(&'s self) -> LanguageParser<'a, 's, I, F, ASTType<Id::Untyped>> {
        self.parser(ParserEnv::parse_ident_type)
    }
    fn parse_ident_type(&self, input: State<I>) -> ParseResult<ASTType<Id::Untyped>, I> {
        try(self.env.identifier())
            .map(|s| {
                debug!("Id: {}", s);
                if s.chars()
                    .next()
                    .map(|c| c.is_lowercase())
                    .unwrap_or(false) {
                    Type::generic(Generic {
                        kind: Rc::new(Kind::Variable(0)),
                        id: self.intern(&s).to_id(),
                    })
                } else {
                    match str_to_primitive_type(&s) {
                        Some(prim) => Type::builtin(prim),
                        None => {
                            Type::data(TypeConstructor::Data(self.intern(&s).to_id()), Vec::new())
                        }
                    }
                }
            })
            .parse_state(input)
    }

    fn typ(&'s self) -> LanguageParser<'a, 's, I, F, ASTType<Id::Untyped>> {
        self.parser(ParserEnv::parse_type)
    }

    fn parse_adt(&self,
                 return_type: &ASTType<Id::Untyped>,
                 input: State<I>)
                 -> ParseResult<ASTType<Id::Untyped>, I> {
        let variant = (self.lex(char('|')),
                       self.ident_u(),
                       many(self.parser(ParserEnv::type_arg)))
                          .map(|(_, id, args): (_, _, Vec<_>)| {
                              (id, Type::function(args, return_type.clone()))
                          });
        many1(variant)
            .map(Type::variants)
            .parse_state(input)
    }

    fn parse_type(&self, input: State<I>) -> ParseResult<ASTType<Id::Untyped>, I> {
        let f = parser(|input| {
            let f = |l: ASTType<Id::Untyped>, r| {
                match (*l).clone() {
                    Type::Data(ctor, mut args) => {
                        args.push(r);
                        Type::data(ctor, args)
                    }
                    _ => Type::app(l, r),
                }
            };
            Ok((f, Consumed::Empty(input)))
        });
        (chainl1(self.parser(ParserEnv::type_arg), f),
         optional(self.reserved_op("->").with(self.typ())))
            .map(|(arg, ret)| {
                debug!("Parse: {:?} -> {:?}", arg, ret);
                match ret {
                    Some(ret) => Type::function(vec![arg], ret),
                    None => arg,
                }
            })
            .parse_state(input)
    }

    fn record_type(&self, input: State<I>) -> ParseResult<ASTType<Id::Untyped>, I> {
        let field = self.parser(ParserEnv::parse_ident2)
                        .then(|(id, is_ctor)| {
                            parser(move |input| {
                                if is_ctor {
                                    value((id.clone().to_id(), None)).parse_state(input)
                                } else {
                                    self.reserved_op(":")
                                        .with(self.typ())
                                        .map(|typ| (id.clone().to_id(), Some(typ)))
                                        .parse_state(input)
                                }
                            })
                        });
        self.braces(sep_by(field, self.lex(char(','))))
            .map(|fields: Vec<_>| {
                let mut associated = Vec::new();
                let mut types = Vec::new();
                for (id, field) in fields {
                    match field {
                        Some(typ) => {
                            types.push(Field {
                                name: id,
                                typ: typ,
                            })
                        }
                        None => {
                            let typ = Type::data(TypeConstructor::Data(id), Vec::new());
                            associated.push(Field {
                                name: typ.clone(),
                                typ: typ,
                            });
                        }
                    }
                }
                Type::record(associated, types)
            })
            .parse_state(input)
    }

    fn type_arg(&self, input: State<I>) -> ParseResult<ASTType<Id::Untyped>, I> {
        let array_type = self.brackets(self.typ())
                             .map(Type::array);
        array_type.or(self.parser(ParserEnv::record_type))
                  .or(self.parens(optional(self.typ()))
                          .map(|typ| {
                              match typ {
                                  Some(typ) => typ,
                                  None => Type::builtin(BuiltinType::UnitType),
                              }
                          }))
                  .or(self.ident_type())
                  .parse_state(input)
    }

    fn type_decl(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        debug!("type_decl");
        (self.reserved("type"),
         self.parser(ParserEnv::type_binding),
         many(self.reserved("and").with(self.parser(ParserEnv::type_binding))),
         self.reserved("in"),
         self.expr())
            .map(|(_, first, rest, _, expr): (_, _, Vec<_>, _, _)| {
                let binds = Some(first)
                                .into_iter()
                                .chain(rest)
                                .map(|(name, typ)| {
                                    ast::TypeBinding {
                                        name: name,
                                        typ: typ,
                                    }
                                })
                                .collect();
                Expr::Type(binds, Box::new(expr))
            })
            .parse_state(input)
    }

    fn type_binding(&self,
                    input: State<I>)
                    -> ParseResult<(ASTType<Id::Untyped>, ASTType<Id::Untyped>), I> {
        (self.ident_u(), many(self.ident_u()))
            .map(|(name, args): (_, Vec<_>)| {
                let args = args.into_iter()
                               .map(|id| {
                                   Type::generic(Generic {
                                       kind: Rc::new(Kind::Variable(0)),
                                       id: id,
                                   })
                               })
                               .collect();
                Type::data(TypeConstructor::Data(name), args)
            })
            .then(|return_type| {
                parser(move |input| {
                    let (rhs_type, input) = try!(self.reserved_op("=")
                                                     .with(self.typ()
                                                               .or(parser(|input| {
                                                                   self.parse_adt(&return_type,
                                                                                  input)
                                                               })))
                                                     .parse_state(input));
                    Ok(((return_type.clone(), rhs_type), input))
                })
            })
            .parse_state(input)
    }

    fn expr(&'s self) -> LanguageParser<'a, 's, I, F, LExpr<Id>> {
        self.parser(ParserEnv::top_expr)
    }

    fn parse_expr(&self, input: State<I>) -> ParseResult<LExpr<Id>, I> {
        let arg_expr1 = self.parser(ParserEnv::parse_arg);
        let arg_expr2 = self.parser(ParserEnv::parse_arg);
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
    fn parse_arg(&self, input: State<I>) -> ParseResult<LExpr<Id>, I> {
        let position = input.position;
        debug!("Expr start: {:?}", input.clone().uncons().map(|t| t.0));
        let loc = |expr| {
            located(Location {
                        column: position.column,
                        row: position.line,
                        absolute: 0,
                    },
                    expr)
        };
        choice::<[&mut Parser<Input = I, Output = LExpr<Id>>; 14],
                 _>([&mut parser(|input| self.if_else(input)).map(&loc),
                     &mut self.parser(ParserEnv::let_in).map(&loc),
                     &mut self.parser(ParserEnv::case_of).map(&loc),
                     &mut self.parser(ParserEnv::lambda).map(&loc),
                     &mut self.parser(ParserEnv::type_decl).map(&loc),
                     &mut self.lex(try(self.integer().skip(not_followed_by(string(".")))))
                              .map(|i| loc(Expr::Literal(LiteralStruct::Integer(i)))),
                     &mut self.lex(try(self.float()))
                              .map(|f| loc(Expr::Literal(LiteralStruct::Float(f)))),
                     &mut self.reserved("True")
                              .map(|_| loc(Expr::Literal(LiteralStruct::Bool(true)))),
                     &mut self.reserved("False")
                              .map(|_| loc(Expr::Literal(LiteralStruct::Bool(false)))),
                     &mut self.ident().map(Expr::Identifier).map(&loc),
                     &mut self.parser(ParserEnv::record).map(&loc),
                     &mut self.parens(optional(self.expr()).map(|expr| {
                         match expr {
                             Some(expr) => expr,
                             None => loc(Expr::Tuple(vec![])),
                         }
                     })),
                     &mut self.string_literal().map(|s| {
                         loc(Expr::Literal(LiteralStruct::String(self.intern(&s).to_id())))
                     }),
                     &mut self.brackets(sep_by(self.expr(), self.lex(char(','))))
                              .map(|exprs| {
                                  loc(Expr::Array(ArrayStruct {
                                      id: self.intern(""),
                                      expressions: exprs,
                                  }))
                              })])
            .and(many(self.lex(char('.')).with(self.ident())))
            .map(|(expr, fields): (_, Vec<_>)| {
                fields.into_iter().fold(expr,
                                        |expr, field| loc(Expr::FieldAccess(Box::new(expr), field)))
            })
            .parse_state(input)
    }

    ///Parses an operator
    fn op(&'s self) -> LanguageParser<'a, 's, I, F, Id> {
        self.parser(ParserEnv::parse_op)
    }

    fn parse_op(&self, input: State<I>) -> ParseResult<Id, I> {
        (optional(char('#').with(many(letter()))), try(self.env.op()))
            .map(|(builtin, op): (Option<String>, String)| {
                match builtin {
                    Some(mut builtin) => {
                        builtin.insert(0, '#');
                        builtin.extend(op.chars());
                        self.intern(&builtin)
                    }
                    None => self.intern(&op),
                }
            })
            .parse_state(input)
    }

    /// Parses any sort of expression
    fn top_expr(&self, input: State<I>) -> ParseResult<LExpr<Id>, I> {
        let term = self.parser(ParserEnv::parse_expr);
        let op = self.op()
                     .map(|op| {
                         let assoc = Assoc {
                             precedence: self.precedence(op.as_ref()),
                             fixity: self.fixity(op.as_ref()),
                         };
                         (op, assoc)
                     });
        // An expression parser from combine-language which automatically handles fixity
        // and assoicativity
        expression_parser(term, op, |l, op, r| {
            let loc = l.location.clone();
            located(loc, Expr::BinOp(Box::new(l), op.clone(), Box::new(r)))
        })
            .parse_state(input)
    }

    fn lambda(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        (self.symbol("\\"),
         many(self.ident()),
         self.symbol("->"),
         self.expr())
            .map(|(_, args, _, expr)| {
                Expr::Lambda(LambdaStruct {
                    id: self.intern(""),
                    free_vars: Vec::new(),
                    arguments: args,
                    body: Box::new(expr),
                })
            })
            .parse_state(input)
    }

    fn case_of(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        let alt = (self.reserved_op("|"),
                   self.pattern(),
                   self.reserved_op("->"),
                   self.expr())
                      .map(|(_, p, _, e)| {
                          Alternative {
                              pattern: p,
                              expression: e,
                          }
                      });
        (self.reserved("case"),
         self.expr(),
         self.reserved("of"),
         many1(alt))
            .map(|(_, e, _, alts)| Expr::Match(Box::new(e), alts))
            .parse_state(input)
    }

    fn pattern(&'s self) -> LanguageParser<'a, 's, I, F, Pattern<Id>> {
        self.parser(ParserEnv::parse_pattern)
    }

    fn parse_pattern(&self, input: State<I>) -> ParseResult<Pattern<Id>, I> {
        self.record_parser(self.ident_u(), self.ident_u(), |record| {
            self.parser(ParserEnv::parse_ident2)
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
                        types: types,
                        fields: patterns,
                    }
                }))
                .or(self.parens(self.pattern()))
                .parse_state(input)
        })
    }

    fn if_else(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        (self.reserved("if"),
         self.expr(),
         self.reserved("then"),
         self.expr(),
         self.reserved("else"),
         self.expr())
            .map(|(_, b, _, t, _, f)| Expr::IfElse(Box::new(b), Box::new(t), Some(Box::new(f))))
            .parse_state(input)
    }

    fn let_in(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        let bind1 = self.parser(ParserEnv::binding);
        let bind2 = self.parser(ParserEnv::binding);
        (self.reserved("let"),
         bind1.and(many(self.reserved("and").with(bind2))),
         self.reserved("in"),
         self.expr())
            .map(|(_, (b, bindings), _, expr)| {
                let mut bindings: Vec<_> = bindings;
                bindings.insert(0, b);
                Expr::Let(bindings, Box::new(expr))
            })
            .parse_state(input)
    }

    fn binding(&self, input: State<I>) -> ParseResult<Binding<Id>, I> {
        let type_sig = self.reserved_op(":").with(self.typ());
        let (name, input) = try!(self.pattern().parse_state(input));
        let (arguments, input) = match name {
            Pattern::Identifier(_) => {
                try!(input.combine(|input| many(self.ident()).parse_state(input)))
            }
            _ => (Vec::new(), input),
        };
        let ((typ, _, e), input) = try!(input.combine(|input| {
            (optional(type_sig), self.reserved_op("="), self.expr()).parse_state(input)
        }));
        Ok((Binding {
            name: name,
            typ: typ,
            arguments: arguments,
            expression: e,
        },
            input))
    }

    fn record(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
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
                          typ: self.intern(""),
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
        let mut field = self.parser(ParserEnv::parse_ident2)
                            .then(move |(id, is_ctor)| {
                                parser(move |input| {
                                    let result = if is_ctor {
                                        optional(self.reserved_op("=").with(p1.clone()))
                                            .map(Ok)
                                            .parse_state(input)

                                    } else {
                                        optional(self.reserved_op("=").with(p2.clone()))
                                            .map(Err)
                                            .parse_state(input)
                                    };
                                    result.map(|(x, input)| ((id.clone().to_id(), x), input))
                                })
                            });
        let mut parser = self.braces(sep_by(&mut field, self.lex(char(','))));
        f(&mut parser)
    }
}


///Parses a string to an AST which contains has identifiers which also contains a field for storing
///type information. The type will just be a dummy value until the AST has passed typechecking
pub fn parse_tc(gc: &mut Gc,
                interner: &mut Interner,
                input: &str)
                -> Result<LExpr<TcIdent<InternedStr>>, Box<StdError>> {
    interner.with_env(gc, |env| {
        let mut env = ast::TcIdentEnv {
            typ: Type::variable(ast::TypeVariable {
                id: 0,
                kind: Rc::new(ast::Kind::Star),
            }),
            env: env,
        };
        parse_module(|s| env.from_str(s), input)
    })
}

fn parse_module<F, Id>(make_ident: F, input: &str) -> Result<LExpr<Id>, Box<StdError>>
    where Id: AstId + AsRef<str> + Clone,
          F: FnMut(&str) -> Id
{

    let ops = "+-*/&|=<>";
    let env = LanguageEnv::new(LanguageDef {
        ident: Identifier {
            start: letter().or(char('_')),
            rest: alpha_num().or(char('_')),
            reserved: ["if", "then", "else", "let", "and", "in", "type", "case", "of"]
                          .iter()
                          .map(|x| (*x).into())
                          .collect(),
        },
        op: Identifier {
            start: satisfy(move |c| ops.chars().any(|x| x == c)),
            rest: satisfy(move |c| ops.chars().any(|x| x == c)),
            reserved: ["->", "\\", "|"].iter().map(|x| (*x).into()).collect(),
        },
        comment_start: string("/*").map(|_| ()),
        comment_end: string("*/").map(|_| ()),
        comment_line: string("//").map(|_| ()),
    });

    let env = ParserEnv {
        env: env,
        make_ident: RefCell::new(make_ident),
    };
    env.white_space()
       .with(env.expr())
       .parse(input)
       .map(|t| t.0)
       .map_err(|err| {
           let errors = err.errors
                           .into_iter()
                           .map(static_error)
                           .collect();
           From::from(ParseError::<&'static str> {
               position: err.position,
               errors: errors,
           })
       })
}

// Converts an error into a static error by transforming any range arguments into strings
fn static_error(e: Error<char, &str>) -> Error<char, &'static str> {
    fn static_info<I: fmt::Display>(i: Info<char, I>) -> Info<char, &'static str> {
        match i {
            Info::Token(t) => Info::Token(t),
            Info::Range(t) => Info::Owned(format!("{}", t)),
            Info::Borrowed(t) => Info::Borrowed(t),
            Info::Owned(t) => Info::Owned(t),
        }
    }
    match e {
        Error::Unexpected(t) => Error::Unexpected(static_info(t)),
        Error::Expected(t) => Error::Expected(static_info(t)),
        Error::Message(t) => Error::Message(static_info(t)),
        Error::Other(t) => Error::Other(t),
    }
}

#[cfg(test)]
pub mod tests {
    use super::parse_module;
    use base::ast::*;
    use base::interner::*;

    use std::rc::Rc;
    use std::cell::RefCell;
    use base::gc::Gc;
    use base::ast;

    ///Returns a reference to the interner stored in TLD
    pub fn get_local_interner() -> Rc<RefCell<(Interner, Gc)>> {
        thread_local!(static INTERNER: Rc<RefCell<(Interner, Gc)>>
                      = Rc::new(RefCell::new((Interner::new(), Gc::new()))));
        INTERNER.with(|interner| interner.clone())
    }

    pub fn intern(s: &str) -> InternedStr {
        let i = get_local_interner();
        let mut i = i.borrow_mut();
        let &mut (ref mut i, ref mut gc) = &mut *i;
        i.intern(gc, s)
    }

    type PExpr = LExpr<InternedStr>;

    fn binop(l: PExpr, s: &str, r: PExpr) -> PExpr {
        no_loc(Expr::BinOp(Box::new(l), intern(s), Box::new(r)))
    }
    fn int(i: i64) -> PExpr {
        no_loc(Expr::Literal(Integer(i)))
    }
    fn let_(s: &str, e: PExpr, b: PExpr) -> PExpr {
        let_a(s, &[], e, b)
    }
    fn let_a(s: &str, args: &[&str], e: PExpr, b: PExpr) -> PExpr {
        no_loc(Expr::Let(vec![Binding {
                                  name: Pattern::Identifier(intern(s)),
                                  typ: None,
                                  arguments: args.iter().map(|i| intern(i)).collect(),
                                  expression: e,
                              }],
                         Box::new(b)))
    }
    fn id(s: &str) -> PExpr {
        no_loc(Expr::Identifier(intern(s)))
    }
    fn field(s: &str, typ: ASTType<InternedStr>) -> Field<InternedStr> {
        Field {
            name: intern(s),
            typ: typ,
        }
    }
    fn typ(s: &str) -> ASTType<InternedStr> {
        assert!(s.len() != 0);
        let is_var = s.chars().next().unwrap().is_lowercase();
        match str_to_primitive_type(s) {
            Some(b) => Type::builtin(b),
            None if is_var => generic(s),
            None => Type::data(TypeConstructor::Data(intern(s)), Vec::new()),
        }
    }
    fn typ_a(s: &str, args: Vec<ASTType<InternedStr>>) -> ASTType<InternedStr> {
        assert!(s.len() != 0);
        ASTType::new(ast::type_con(intern(s), args))
    }
    fn generic(s: &str) -> ASTType<InternedStr> {
        Type::generic(Generic {
            kind: Rc::new(Kind::Variable(0)),
            id: intern(s),
        })
    }
    fn call(e: PExpr, args: Vec<PExpr>) -> PExpr {
        no_loc(Expr::Call(Box::new(e), args))
    }
    fn if_else(p: PExpr, if_true: PExpr, if_false: PExpr) -> PExpr {
        no_loc(Expr::IfElse(Box::new(p), Box::new(if_true), Some(Box::new(if_false))))
    }
    fn case(e: PExpr, alts: Vec<(Pattern<InternedStr>, PExpr)>) -> PExpr {
        no_loc(Expr::Match(Box::new(e),
                           alts.into_iter()
                               .map(|(p, e)| {
                                   Alternative {
                                       pattern: p,
                                       expression: e,
                                   }
                               })
                               .collect()))
    }
    fn lambda(name: &str, args: Vec<InternedStr>, body: PExpr) -> PExpr {
        no_loc(Expr::Lambda(LambdaStruct {
            id: intern(name),
            free_vars: Vec::new(),
            arguments: args,
            body: Box::new(body),
        }))
    }

    fn type_decl(name: ASTType<InternedStr>, typ: ASTType<InternedStr>, body: PExpr) -> PExpr {
        type_decls(vec![TypeBinding {
                            name: name,
                            typ: typ,
                        }],
                   body)
    }

    fn type_decls(binds: Vec<TypeBinding<InternedStr>>, body: PExpr) -> PExpr {
        no_loc(Expr::Type(binds, Box::new(body)))
    }

    fn bool(b: bool) -> PExpr {
        no_loc(Expr::Literal(Bool(b)))
    }
    fn record(fields: Vec<(InternedStr, Option<PExpr>)>) -> PExpr {
        record_a(Vec::new(), fields)
    }
    fn record_a(types: Vec<(InternedStr, Option<ASTType<InternedStr>>)>,
                fields: Vec<(InternedStr, Option<PExpr>)>)
                -> PExpr {
        no_loc(Expr::Record {
            typ: intern(""),
            types: types,
            exprs: fields,
        })
    }
    fn field_access(expr: PExpr, field: &str) -> PExpr {
        no_loc(Expr::FieldAccess(Box::new(expr), intern(field)))
    }
    fn array(fields: Vec<PExpr>) -> PExpr {
        no_loc(Expr::Array(ArrayStruct {
            id: intern(""),
            expressions: fields,
        }))
    }

    pub fn parse_new(input: &str) -> LExpr<InternedStr> {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut (ref mut interner, ref mut gc) = &mut *interner;
        let x = interner.with_env(gc,
                                  |mut env| parse_module(|s| AstId::from_str(&mut env, s), input))
                        .unwrap_or_else(|err| panic!("{:?}", err));
        x
    }

    #[test]
    fn expression() {
        let _ = ::env_logger::init();
        let e = parse_new("2 * 3 + 4");
        assert_eq!(e, binop(binop(int(2), "*", int(3)), "+", int(4)));
        let e = parse_new(r#"\x y -> x + y"#);
        assert_eq!(e,
                   lambda("",
                          vec![intern("x"), intern("y")],
                          binop(id("x"), "+", id("y"))));
        let e = parse_new(r#"type Test = Int in 0"#);
        assert_eq!(e, type_decl(typ("Test"), typ("Int"), int(0)));
    }

    #[test]
    fn application() {
        let _ = ::env_logger::init();
        let e = parse_new("let f = \\x y -> x + y in f 1 2");
        let a = let_("f",
                     lambda("",
                            vec![intern("x"), intern("y")],
                            binop(id("x"), "+", id("y"))),
                     call(id("f"), vec![int(1), int(2)]));
        assert_eq!(e, a);
    }

    #[test]
    fn if_else_test() {
        let _ = ::env_logger::init();
        let e = parse_new("if True then 1 else 0");
        let a = if_else(bool(true), int(1), int(0));
        assert_eq!(e, a);
    }

    #[test]
    fn let_type_decl() {
        let _ = ::env_logger::init();
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut (ref mut interner, ref mut gc) = &mut *interner;
        let e = super::parse_tc(gc, interner, "let f: Int = \\x y -> x + y in f 1 2").unwrap();
        match e.value {
            Expr::Let(bind, _) => assert_eq!(bind[0].typ, Some(typ("Int"))),
            _ => assert!(false),
        }
    }
    #[test]
    fn let_args() {
        let _ = ::env_logger::init();
        let e = parse_new("let f x y = y in f 2");
        assert_eq!(e,
                   let_a("f", &["x", "y"], id("y"), call(id("f"), vec![int(2)])));
    }

    #[test]
    fn type_decl_record() {
        let _ = ::env_logger::init();
        let e = parse_new("type Test = { x: Int, y: {} } in 1");
        let record = Type::record(Vec::new(),
                                  vec![field("x", typ("Int")),
                                       field("y", Type::record(vec![], vec![]))]);
        assert_eq!(e, type_decl(typ("Test"), record, int(1)));
    }

    #[test]
    fn type_mutually_recursive() {
        let _ = ::env_logger::init();
        let e = parse_new("type Test = | Test Int and Test2 = { x: Int, y: {} } in 1");
        let test = Type::variants(vec![(intern("Test"),
                                        Type::function(vec![typ("Int")], typ("Test")))]);
        let test2 = Type::record(Vec::new(),
                                 vec![Field {
                                          name: intern("x"),
                                          typ: typ("Int"),
                                      },
                                      Field {
                                          name: intern("y"),
                                          typ: Type::record(vec![], vec![]),
                                      }]);
        let binds = vec![
            TypeBinding { name: typ("Test"), typ: test },
            TypeBinding { name: typ("Test2"), typ: test2 },
            ];
        assert_eq!(e, type_decls(binds, int(1)));
    }

    #[test]
    fn field_access_test() {
        let _ = ::env_logger::init();
        let e = parse_new("{ x = 1 }.x");
        assert_eq!(e,
                   field_access(record(vec![(intern("x"), Some(int(1)))]), "x"));
    }

    #[test]
    fn builtin_op() {
        let _ = ::env_logger::init();
        let e = parse_new("x #Int+ 1");
        assert_eq!(e, binop(id("x"), "#Int+", int(1)));
    }

    #[test]
    fn op_identifier() {
        let _ = ::env_logger::init();
        let e = parse_new("let (==) = \\x y -> x #Int== y in (==) 1 2");
        assert_eq!(e,
                   let_("==",
                        lambda("",
                               vec![intern("x"), intern("y")],
                               binop(id("x"), "#Int==", id("y"))),
                        call(id("=="), vec![int(1), int(2)])));
    }
    #[test]
    fn variant_type() {
        let _ = ::env_logger::init();
        let e = parse_new("type Option a = | None | Some a in Some 1");
        let option = Type::data(TypeConstructor::Data(intern("Option")), vec![typ("a")]);
        let none = Type::function(vec![], option.clone());
        let some = Type::function(vec![typ("a")], option.clone());
        assert_eq!(e,
                   type_decl(option,
                             Type::variants(vec![(intern("None"), none), (intern("Some"), some)]),
                             call(id("Some"), vec![int(1)])));
    }
    #[test]
    fn case_expr() {
        let _ = ::env_logger::init();
        let e = parse_new("case None of | Some x -> x | None -> 0");
        assert_eq!(e,
                   case(id("None"),
                        vec![(Pattern::Constructor(intern("Some"), vec![intern("x")]),
                              id("x")),
                             (Pattern::Constructor(intern("None"), vec![]), int(0))]));
    }
    #[test]
    fn array_expr() {
        let _ = ::env_logger::init();
        let e = parse_new("[1, a]");
        assert_eq!(e, array(vec![int(1), id("a")]));
    }
    #[test]
    fn operator_expr() {
        let _ = ::env_logger::init();
        let e = parse_new("test + 1 * 23 #Int- test");
        assert_eq!(e,
                   binop(binop(id("test"), "+", binop(int(1), "*", int(23))),
                         "#Int-",
                         id("test")));
    }

    #[test]
    fn record_pattern() {
        let _ = ::env_logger::init();
        let e = parse_new("case x of | { y, x = z } -> z");
        let pattern = Pattern::Record {
            types: Vec::new(),
            fields: vec![(intern("y"), None), (intern("x"), Some(intern("z")))],
        };
        assert_eq!(e, case(id("x"), vec![(pattern, id("z"))]));
    }
    #[test]
    fn let_pattern() {
        let _ = ::env_logger::init();
        let e = parse_new("let {x, y} = test in x");
        assert_eq!(e,
                   no_loc(Expr::Let(vec![Binding {
                                             name: Pattern::Record {
                                                 types: Vec::new(),
                                                 fields: vec![(intern("x"), None),
                                                              (intern("y"), None)],
                                             },
                                             typ: None,
                                             arguments: vec![],
                                             expression: id("test"),
                                         }],
                                    Box::new(id("x")))));
    }

    #[test]
    fn associated_record() {
        let _ = ::env_logger::init();
        let e = parse_new("type Test a = { Fn, x: a } in { Fn = Int -> Array Int, Test, x = 1 }");

        let test_type = Type::record(vec![Field {
                                              name: typ("Fn"),
                                              typ: typ("Fn"),
                                          }],
                                     vec![Field {
                                              name: intern("x"),
                                              typ: typ("a"),
                                          }]);
        let fn_type = Type::function(vec![typ("Int")], typ_a("Array", vec![typ("Int")]));
        let record = record_a(vec![(intern("Fn"), Some(fn_type)), (intern("Test"), None)],
                              vec![(intern("x"), Some(int(1)))]);
        assert_eq!(e,
                   type_decl(typ_a("Test", vec![typ("a")]), test_type, record));
    }
}
