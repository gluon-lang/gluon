//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.
#![feature(box_syntax)]
#[macro_use]
extern crate log;
extern crate env_logger;
extern crate base;
extern crate combine;
extern crate combine_language;

use std::cell::RefCell;
use std::error::Error;
use std::iter::FromIterator;
use combine_language::{LanguageEnv, LanguageDef, Identifier, Assoc, Fixity, expression_parser, Lex, BetweenChar};
use combine::primitives::{Consumed, Stream};
use combine::combinator::{SepBy, Token};
use combine::*;

pub use base::{ast, interner, gc};

use ast::*;
use gc::Gc;
use interner::{Interner, InternedStr};

/// Parser passes the environment to each parser function
struct LanguageParser<'a: 'b, 'b, I: 'b, F: 'b, T>
    where I: Stream<Item=char> {
    env: &'b ParserEnv<'a, I, F>,
    parser: fn (&ParserEnv<'a, I, F>, State<I>) -> ParseResult<T, I>
}

impl <'a, 'b, I, F, T> Clone for LanguageParser<'a, 'b, I, F, T>
    where I: Stream<Item=char> {
    fn clone(&self) -> LanguageParser<'a, 'b, I, F, T> {
        LanguageParser { env: self.env, parser: self.parser }
    }
}
impl <'a, 'b, I, F, T> Copy for LanguageParser<'a, 'b, I, F, T>
    where I: Stream<Item=char> { }

impl <'a, 'b, F, Id, I, O> Parser for LanguageParser<'a, 'b, I, F, O>
    where I: Stream<Item=char>
        , F: FnMut(&str) -> Id
        , Id: AstId + Clone {
    type Output = O;
    type Input = I;
    fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
        (self.parser)(self.env, input)
    }
}

/// `ParserEnv` is passed around to all individual parsers so that identifiers can always be
/// constructed through calling `make_ident`.
struct ParserEnv<'a, I, F>
    where I: Stream<Item=char> {
    env: LanguageEnv<'a, I>,
    make_ident: RefCell<F>
}

impl <'a, I, F> ::std::ops::Deref for ParserEnv<'a, I, F>
    where I: Stream<Item=char> {
    type Target = LanguageEnv<'a, I>;
    fn deref(&self) -> &LanguageEnv<'a, I> {
        &self.env
    }
}

impl <'a, I, Id, F> ParserEnv<'a, I, F>
where I: Stream<Item=char>
    , F: FnMut(&str) -> Id
    , Id: AstId + AsRef<str> + Clone {

    fn intern(&self, s: &str) -> Id {
        (&mut *self.make_ident.borrow_mut())(s)
    }

    fn parser<'b, T>(&'b self, parser: fn (&ParserEnv<'a, I, F>, State<I>) -> ParseResult<T, I>) -> LanguageParser<'a, 'b, I, F, T> {
        LanguageParser { env: self, parser: parser }
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
            //Primitive operators starts with # and has the op at the end
            _ if s.starts_with("#") => {
                let op = s[1..].trim_left_matches(|c: char| c.is_alphanumeric());
                self.precedence(op)
            }
            _ => 9
        }
    }

    fn fixity(&self, i: &str) -> Fixity {
        match i {
            "*" | "/" | "%" | "+" | "-" |
            "==" | "/=" | "<" | ">" | "<=" | ">=" => Fixity::Left,
            ":" | "++" | "&&" | "||" | "$" => Fixity::Right,
            _ => Fixity::Left
        }
    }

    fn ident<'b>(&'b self) -> LanguageParser<'a, 'b, I, F, Id> {
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
            .map(|s| { debug!("Id: {}", s); (self.intern(&s), s.chars().next().unwrap().is_uppercase()) })
            .parse_state(input)
    }
    fn ident_u<'b>(&'b self) -> LanguageParser<'a, 'b, I, F, Id::Untyped> {
        self.parser(ParserEnv::parse_untyped_ident)
    }
    fn parse_untyped_ident(&self, input: State<I>) -> ParseResult<Id::Untyped, I> {
        self.ident()
            .map(AstId::to_id)
            .parse_state(input)
    }

    fn ident_type<'b>(&'b self) -> LanguageParser<'a, 'b, I, F, Type<Id::Untyped>> {
        self.parser(ParserEnv::parse_ident_type)
    }
    fn parse_ident_type(&self, input: State<I>) -> ParseResult<Type<Id::Untyped>, I> {
        try(self.env.identifier())
            .map(|s| {
                debug!("Id: {}", s);
                if s.chars().next()
                    .map(|c| c.is_lowercase())
                    .unwrap_or(false) {
                    Type::Generic(Generic { kind: Kind::Variable(0), id: self.intern(&s).to_id() })
                }
                else {
                    match str_to_primitive_type(&s) {
                        Some(prim) => Type::Builtin(prim),
                        None => Type::Data(TypeConstructor::Data(self.intern(&s).to_id()), Vec::new())
                    }
                }
            })
            .parse_state(input)
    }

    fn typ<'b>(&'b self) -> LanguageParser<'a, 'b, I, F, Type<Id::Untyped>> {
        self.parser(ParserEnv::parse_type)
    }

    fn parse_adt(&self, return_type: &Type<Id::Untyped>, input: State<I>) -> ParseResult<Type<Id::Untyped>, I> {
        let variant = (self.lex(char('|')), self.ident_u(), many(self.parser(ParserEnv::type_arg)))
                .map(|(_, id, args): (_, _, Vec<_>)| (id, fn_type(args, return_type.clone())));
        many1(variant)
            .map(Type::Variants)
            .parse_state(input)
    }

    fn parse_type(&self, input: State<I>) -> ParseResult<Type<Id::Untyped>, I> {
        let f = parser(|input| {
                let f = |l, r| match l {
                    Type::Data(ctor, mut args) => {
                        args.push(r);
                        Type::Data(ctor, args)
                    }
                    _ => Type::App(Box::new(l), Box::new(r))
                };
                Ok((f, Consumed::Empty(input)))
        });
        (chainl1(self.parser(ParserEnv::type_arg), f), optional(self.reserved_op("->").with(self.typ())))
            .map(|(arg, ret)| {
                debug!("Parse: {:?} -> {:?}", arg, ret);
                match ret {
                    Some(ret) => Type::Function(vec![arg], Box::new(ret)),
                    None => arg
                }
            })
            .parse_state(input)
    }

    fn record_type(&self, input: State<I>) -> ParseResult<Type<Id::Untyped>, I> {
        let field = (self.ident_u(), self.lex(string(":")), self.typ())
            .map(|(name, _, typ)| Field { name: name, typ: typ });
        self.braces(sep_by(field, self.lex(char(','))))
            .map(Type::Record)
            .parse_state(input)
    }

    fn type_arg(&self, input: State<I>) -> ParseResult<Type<Id::Untyped>, I> {
        let array_type = self.brackets(self.typ())
            .map(|typ| Type::Array(Box::new(typ)));
        array_type
            .or(self.parser(ParserEnv::record_type))
            .or(self.parens(optional(self.typ()))
               .map(|typ| match typ {
                    Some(typ) => typ,
                    None => Type::Builtin(BuiltinType::UnitType)
            }))
            .or(self.ident_type())
            .parse_state(input)
    }

    fn type_decl(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        debug!("type_decl");
        (self.reserved("type"), self.ident_u(), many(self.ident_u()))//TODO only variables allowed
            .map(|(_, name, args): (_, _, Vec<_>)| {
                let args = args.into_iter().map(|id| Type::Generic(Generic { kind: Kind::Variable(0), id: id })).collect();
                Type::Data(TypeConstructor::Data(name), args)
            })
            .then(|return_type| parser(move |input| {
                let (rhs_type, input) = try!(self.reserved_op("=")
                    .with(self.typ()
                        .or(parser(|input| self.parse_adt(&return_type, input))))
                    .skip(self.reserved("in"))
                    .and(self.expr())
                    .parse_state(input));
                Ok(((return_type.clone(), rhs_type), input))
            }))
            .map(|(id, (typ, expr))| Expr::Type(id, typ, Box::new(expr)))
            .parse_state(input)
    }

    fn expr<'b>(&'b self) -> LanguageParser<'a, 'b, I, F, LExpr<Id>> {
        self.parser(ParserEnv::top_expr)
    }

    fn parse_expr(&self, input: State<I>) -> ParseResult<LExpr<Id>, I> {
        let arg_expr = self.parser(ParserEnv::parse_arg);
        (arg_expr, many(arg_expr))
            .map(|(f, args): (LExpr<Id>, Vec<_>)| {
                if args.len() > 0 {
                    located(f.location, Expr::Call(Box::new(f), args))
                }
                else {
                    f
                }
            })
            .parse_state(input)
    }

    /// Parses an expression which could be an argument to a function
    fn parse_arg(&self, input: State<I>) -> ParseResult<LExpr<Id>, I> {
        let position = input.position;
        debug!("Expr start: {:?}", input.clone().uncons().map(|t| t.0));
        let loc = |expr| located(Location { column: position.column, row: position.line, absolute: 0 }, expr);
        choice::<[&mut Parser<Input=I, Output=LExpr<Id>>; 14], _>([
            &mut parser(|input| self.if_else(input)).map(&loc),
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
                    None => loc(Expr::Tuple(vec![]))
                }
            })),
            &mut self.string_literal().map(|s| loc(Expr::Literal(LiteralStruct::String(self.intern(&s).to_id())))),
            &mut self.brackets(sep_by(self.expr(), self.lex(char(','))))
                .map(|exprs| loc(Expr::Array(ArrayStruct { id: self.intern(""), expressions: exprs })))
            ])
            .and(many(self.lex(char('.')).with(self.ident())))
            .map(|(expr, fields): (_, Vec<_>)| {
                fields.into_iter().fold(expr, |expr, field|
                    loc(Expr::FieldAccess(Box::new(expr), field))
                )
            })
            .parse_state(input)
    }

    ///Parses an operator
    fn op<'b>(&'b self) -> LanguageParser<'a, 'b, I, F, Id> {
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
                    None => self.intern(&op)
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
                    fixity: self.fixity(op.as_ref())
                };
                (op, assoc)
            });
        //An expression parser from combine-language which automatically handles fixity
        //and assoicativity
        expression_parser(term, op, |l, op, r| {
                let loc = l.location.clone();
                located(loc, Expr::BinOp(Box::new(l), op.clone(), Box::new(r)))
            })
            .parse_state(input)
    }

    fn lambda(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        (self.symbol("\\"), many(self.ident()), self.symbol("->"), self.expr())
            .map(|(_, args, _, expr)| Expr::Lambda(LambdaStruct {
                id: self.intern(""),
                free_vars: Vec::new(),
                arguments: args,
                body: Box::new(expr)
            }))
            .parse_state(input)
    }

    fn case_of(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        let alt = (self.reserved_op("|"), self.pattern(), self.reserved_op("->"), self.expr())
            .map(|(_, p, _, e)| Alternative { pattern: p, expression: e });
        (self.reserved("case"), self.expr(), self.reserved("of"), many1(alt))
            .map(|(_, e, _, alts)| Expr::Match(Box::new(e), alts))
            .parse_state(input)
    }

    fn pattern<'b>(&'b self) -> LanguageParser<'a, 'b, I, F, Pattern<Id>> {
        self.parser(ParserEnv::parse_pattern)
    }

    fn parse_pattern(&self, input: State<I>) -> ParseResult<Pattern<Id>, I> {
        let record = self.record_parser(optional(self.reserved_op("=").with(self.ident_u())))
            .map(Pattern::Record);
        self.parser(ParserEnv::parse_ident2)
            .then(|(id, is_ctor)| parser(move |input| 
                if is_ctor {
                    many(self.ident())
                        .parse_state(input)
                        .map(|(args, input)| (ConstructorPattern(id.clone(), args), input))
                }
                else {
                    Ok((IdentifierPattern(id.clone()), Consumed::Empty(input)))
                }
            ))
            .or(record)
            .parse_state(input)
    }

    fn if_else(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        (self.reserved("if"), self.expr(),
            self.reserved("then"), self.expr(),
            self.reserved("else"), self.expr())
            .map(|(_, b, _, t, _, f)|
                Expr::IfElse(Box::new(b), Box::new(t), Some(Box::new(f)))
            )
            .parse_state(input)
    }

    fn let_in(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        let bind = self.parser(ParserEnv::binding);
        (self.reserved("let"), bind.and(many(self.reserved("and").with(bind))), self.reserved("in"), self.expr())
            .map(|(_, (b, bindings), _, expr)| {
                let mut bindings: Vec<_> = bindings;
                bindings.insert(0, b);
                Expr::Let(bindings, Box::new(expr))
            })
            .parse_state(input)
    }

    fn binding(&self, input: State<I>) -> ParseResult<Binding<Id>, I> {
        let type_sig = self.reserved_op(":").with(self.typ());
        (self.ident(), many(self.ident()), optional(type_sig), self.reserved_op("="), self.expr())
            .map(|(mut name, arguments, typ, _, e)| {
                if let Some(typ) = typ {
                    name.set_type(typ);
                }
                Binding { name: name, arguments: arguments, expression: e }
            })
            .parse_state(input)
    }

    fn record(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
        self.record_parser(optional(self.reserved_op("=").with(self.expr())))
            .map(|fields| Expr::Record(self.intern(""), fields))
            .parse_state(input)
    }

    fn record_parser<'b, P, O>(&'b self, p: P) -> RecordParser<'a, 'b, I, Id, F, P, O>
    where P: Parser<Input=I>
        , O: FromIterator<(Id::Untyped, P::Output)> {
        let field = (self.ident_u(), p);
        self.braces(sep_by(field, self.lex(char(','))))
    }
}

type RecordParser<'a, 'b, I, Id, F, P, O> = BetweenChar<'a, 'b, SepBy<O, (LanguageParser<'a, 'b, I, F, <Id as base::ast::AstId>::Untyped>,  P), Lex<'a, 'b, Token<I>>>>;


///Parses a string to an AST which contains has identifiers which also contains a field for storing
///type information. The type will just be a dummy value until the AST has passed typechecking
pub fn parse_tc(gc: &mut Gc, interner: &mut Interner, input: &str) -> Result<LExpr<TcIdent<InternedStr>>, Box<Error>> {
    interner.with_env(gc, |env| {
        parse_module(|s| AstId::from_str(env, s), input)
    })
}

fn parse_module<F, Id>(make_ident: F, input: &str) -> Result<LExpr<Id>, Box<Error>>
where Id: AstId + AsRef<str> + Clone
    , F: FnMut(&str) -> Id {

    let ops = "+-*/&|=<>";
    let env = LanguageEnv::new(LanguageDef {
        ident: Identifier {
            start: letter().or(char('_')),
            rest: alpha_num().or(char('_')),
            reserved: ["if", "then", "else", "let", "and", "in", "type", "case", "of"].iter().map(|x| (*x).into()).collect()
        },
        op: Identifier {
            start: satisfy(move |c| ops.chars().any(|x| x == c)),
            rest: satisfy(move |c| ops.chars().any(|x| x == c)),
            reserved: ["->", "\\", "|"].iter().map(|x| (*x).into()).collect()
        },
        comment_start: "/*",
        comment_end: "*/",
        comment_line: "//",
    });

    let env = ParserEnv {
        env: env,
        make_ident: RefCell::new(make_ident),
    };
    env.white_space()
        .with(env.expr())
        .parse(input)
        .map(|t| t.0)
        .map_err(From::from)
}

#[cfg(test)]
pub mod tests {
    use super::parse_module;
    use base::ast::*;
    use base::interner::*;
    
    use std::rc::Rc;
    use std::cell::RefCell;
    use base::gc::Gc;

    ///Returns a reference to the interner stored in TLD
    pub fn get_local_interner() -> Rc<RefCell<(Interner, Gc)>> {
        thread_local!(static INTERNER: Rc<RefCell<(Interner, Gc)>> = Rc::new(RefCell::new((Interner::new(), Gc::new()))));
        INTERNER.with(|interner| interner.clone())
    }

    pub fn intern(s: &str) -> InternedStr {
        let i = get_local_interner();
        let mut i = i.borrow_mut();
        let &mut(ref mut i, ref mut gc) = &mut *i;
        i.intern(gc, s)
    }

    type PExpr = LExpr<InternedStr>;
    
    fn binop(l: PExpr, s: &str, r: PExpr) -> PExpr {
        no_loc(Expr::BinOp(box l, intern(s), box r))
    }
    fn int(i: i64) -> PExpr {
        no_loc(Expr::Literal(Integer(i)))
    }
    fn let_(s: &str, e: PExpr, b: PExpr) -> PExpr {
        let_a(s, &[], e, b)
    }
    fn let_a(s: &str, args: &[&str], e: PExpr, b: PExpr) -> PExpr {
        no_loc(Expr::Let(vec![Binding { name: intern(s), arguments: args.iter().map(|i| intern(i)).collect(), expression: e }], Box::new(b)))
    }
    fn id(s: &str) -> PExpr {
        no_loc(Expr::Identifier(intern(s)))
    }
    fn field(s: &str, typ: Type<InternedStr>) -> Field<InternedStr> {
        Field { name: intern(s), typ: typ }
    }
    fn typ(s: &str) -> Type<InternedStr> {
        assert!(s.len() != 0);
        let is_var = s.chars().next().unwrap().is_lowercase();
        match str_to_primitive_type(s) {
            Some(b) => Type::Builtin(b),
            None if is_var => generic(s),
            None => Type::Data(TypeConstructor::Data(intern(s)), Vec::new())
        }
    }
    fn generic(s: &str) -> Type<InternedStr> {
        Type::Generic(Generic { kind: Kind::Variable(0), id: intern(s) })
    }
    fn call(e: PExpr, args: Vec<PExpr>) -> PExpr {
        no_loc(Expr::Call(box e, args))
    }
    fn if_else(p: PExpr, if_true: PExpr, if_false: PExpr) -> PExpr {
        no_loc(Expr::IfElse(box p, box if_true, Some(box if_false)))
    }
    fn case(e: PExpr, alts: Vec<(Pattern<InternedStr>, PExpr)>) -> PExpr {
        no_loc(Expr::Match(box e, alts.into_iter()
                                    .map(|(p, e)| Alternative { pattern: p, expression: e })
                                    .collect()))
    }
    fn lambda(name: &str, args: Vec<InternedStr>, body: PExpr) -> PExpr {
        no_loc(Expr::Lambda(LambdaStruct {
            id: intern(name),
            free_vars: Vec::new(),
            arguments: args,
            body: box body 
        }))
    }
    fn type_decl(name: Type<InternedStr>, typ: Type<InternedStr>, body: PExpr) -> PExpr {
        no_loc(Expr::Type(name, typ, box body))
    }

    fn bool(b: bool) -> PExpr {
        no_loc(Expr::Literal(Bool(b)))
    }
    fn record(fields: Vec<(InternedStr, Option<PExpr>)>) -> PExpr {
        no_loc(Expr::Record(intern(""), fields))
    }
    fn field_access(expr: PExpr, field: &str) -> PExpr {
        no_loc(Expr::FieldAccess(Box::new(expr), intern(field)))
    }
    fn array(fields: Vec<PExpr>) -> PExpr {
        no_loc(Expr::Array(ArrayStruct { id: intern(""), expressions: fields }))
    }

    pub fn parse_new<Id>(input: &str) -> LExpr<Id>
        where Id: AstId<Env=InternerEnv, Untyped=InternedStr> + AsRef<str> + Clone {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut(ref mut interner, ref mut gc) = &mut *interner;
        let x = interner.with_env(gc, |env| {
                parse_module(|s| AstId::from_str(env, s), input)
            })
            .unwrap_or_else(|err| panic!("{:?}", err));
        x
    }

    #[test]
    fn expression() {
        let _ = ::env_logger::init();
        let e = parse_new("2 * 3 + 4");
        assert_eq!(e, binop(binop(int(2), "*", int(3)), "+", int(4)));
        let e = parse_new(r#"\x y -> x + y"#);
        assert_eq!(e, lambda("", vec![intern("x"), intern("y")], binop(id("x"), "+", id("y"))));
        let e = parse_new(r#"type Test = Int in 0"#);
        assert_eq!(e, type_decl(typ("Test"), typ("Int"), int(0)));
    }

    #[test]
    fn application() {
        let _ = ::env_logger::init();
        let e = parse_new("let f = \\x y -> x + y in f 1 2");
        let a = let_("f", lambda("", vec![intern("x"), intern("y")], binop(id("x"), "+", id("y")))
                         , call(id("f"), vec![int(1), int(2)]));
        assert_eq!(e, a);
    }

    #[test]
    fn let_type_decl() {
        let _ = ::env_logger::init();
        let e = parse_new::<TcIdent<InternedStr>>("let f: Int = \\x y -> x + y in f 1 2");
        match e.value {
            Expr::Let(bind, _) => assert_eq!(bind[0].name.typ, typ("Int")),
            _ => assert!(false)
        }
    }
    #[test]
    fn let_args() {
        let _ = ::env_logger::init();
        let e = parse_new("let f x y = y in f 2");
        assert_eq!(e, let_a("f", &["x", "y"], id("y"), call(id("f"), vec![int(2)])));
    }

    #[test]
    fn type_decl_record() {
        let _ = ::env_logger::init();
        let e = parse_new("type Test = { x: Int, y: {} } in 1");
        let record = Type::Record(vec![Field { name: intern("x"), typ: typ("Int") }
                                    ,  Field { name: intern("y"), typ: Type::Record(vec![]) }]);
        assert_eq!(e, type_decl(typ("Test"), record, int(1)));
    }

    #[test]
    fn field_access_test() {
        let _ = ::env_logger::init();
        let e = parse_new("{ x = 1 }.x");
        assert_eq!(e, field_access(record(vec![(intern("x"), Some(int(1)))]), "x"));
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
        assert_eq!(e, let_(
                "==", lambda("", vec![intern("x"), intern("y")], binop(id("x"), "#Int==", id("y")))
                , call(id("=="), vec![int(1), int(2)])));
    }
    #[test]
    fn variant_type() {
        let _ = ::env_logger::init();
        let e = parse_new("type Option a = | None | Some a in Some 1");
        let option = Type::Data(TypeConstructor::Data(intern("Option")), vec![typ("a")]);
        let none = fn_type(vec![], option.clone());
        let some = fn_type(vec![typ("a")], option.clone());
        assert_eq!(e, type_decl(option
                , Type::Variants(vec![(intern("None"), none), (intern("Some"), some)])
                , call(id("Some"), vec![int(1)])));
    }
    #[test]
    fn case_expr() {
        let _ = ::env_logger::init();
        let e = parse_new("case None of | Some x -> x | None -> 0");
        assert_eq!(e, case(id("None"), vec![
                            (ConstructorPattern(intern("Some"), vec![intern("x")]), id("x"))
                        ,   (ConstructorPattern(intern("None"), vec![]), int(0))
                        ]));
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
        assert_eq!(e, binop(binop(id("test"), "+", binop(int(1), "*", int(23))), "#Int-", id("test")));
    }

    #[test]
    fn record_pattern() {
        let _ = ::env_logger::init();
        let e = parse_new("case x of | { y, x = z } -> z");
        assert_eq!(e, case(id("x"), vec![
            (Pattern::Record(vec![(intern("y"), None), (intern("x"), Some(intern("z")))]),
                id("z"))
        ]));
    }
}
