#![feature(box_syntax, slice_patterns)]
#[macro_use]
extern crate log;
extern crate env_logger;
extern crate base;
extern crate parser_combinators;
extern crate parser_combinators_language;


pub use base::{ast, interner, gc};

use std::marker::PhantomData;
use ast::*;
use gc::Gc;
use interner::{Interner, InternedStr};

pub fn parse_tc(gc: &mut Gc, interner: &mut Interner, input: &str) -> Result<LExpr<TcIdent>, Box<::std::error::Error>> {
    parse_module(gc, interner, input)
}
pub fn parse_str(gc: &mut Gc, interner: &mut Interner, input: &str) -> Result<LExpr<InternedStr>, Box<::std::error::Error>> {
    parse_module(gc, interner, input)
}

fn parse_module<Id>(gc: &mut Gc, interner: &mut Interner, input: &str) -> Result<LExpr<Id>, Box<::std::error::Error>>
    where Id: AstId + Clone {
    use std::cell::RefCell;
    use parser_combinators_language::{Env, LanguageDef, Identifier};
    use parser_combinators::primitives::{Stream, State};
    use parser_combinators::*;

    struct EnvParser<'a: 'b, 'b, I: 'b, Id: 'b, T> {
        env: &'b ParserEnv<'a, I, Id>,
        parser: fn (&ParserEnv<'a, I, Id>, State<I>) -> ParseResult<T, I>
    }

    impl <'a, 'b, Id, I, O> Parser for EnvParser<'a, 'b, I, Id, O>
        where I: Stream<Item=char>
            , Id: AstId + Clone {
        type Output = O;
        type Input = I;
        fn parse_state(&mut self, input: State<I>) -> ParseResult<O, I> {
            (self.parser)(self.env, input)
        }
    }

    struct ParserEnv<'a, I, Id> {
        data: RefCell<(&'a mut Gc, &'a mut Interner)>,
        env: Env<'a, I>,
        _marker: PhantomData<fn (InternedStr) -> Id>
    }

    impl <'a, I, Id> ::std::ops::Deref for ParserEnv<'a, I, Id> {
        type Target = Env<'a, I>;
        fn deref(&self) -> &Env<'a, I> {
            &self.env
        }
    }

    impl <'a, I, Id> ParserEnv<'a, I, Id>
        where I: Stream<Item=char>
            , Id: AstId + Clone {
        fn intern(&self, s: &str) -> Id {
            let mut r = self.data.borrow_mut();
            let r = &mut *r;
            Id::from_str(r.1.intern(r.0, s))
        }

        fn parser<'b, T>(&'b self, parser: fn (&ParserEnv<'a, I, Id>, State<I>) -> ParseResult<T, I>) -> EnvParser<'a, 'b, I, Id, T> {
            EnvParser { env: self, parser: parser }
        }

        fn precedence(&self, i: InternedStr) -> i32 {
            match &i[..] {
                "&&" | "||" => 0,
                "+" => 1,
                "-" => 1,
                "*" => 3,
                "/" => 3,
                "%" => 3,
                "==" => 1,
                "/=" => 1,
                "<" => 1,
                ">" => 1,
                "<=" => 1,
                ">=" => 1,
                _ => 9
            }
        }

        fn ident<'b>(&'b self) -> EnvParser<'a, 'b, I, Id, Id> {
            self.parser(ParserEnv::parse_ident)
        }
        fn parse_ident(&self, input: State<I>) -> ParseResult<Id, I> {
            try(self.env.ident())
                .map(|s| { debug!("Id: {}", s); self.intern(&s) })
                .parse_state(input)
        }
        fn ident_u<'b>(&'b self) -> EnvParser<'a, 'b, I, Id, Id::Untyped> {
            self.parser(ParserEnv::parse_untyped_ident)
        }
        fn parse_untyped_ident(&self, input: State<I>) -> ParseResult<Id::Untyped, I> {
            try(self.env.ident())
                .map(|s| { debug!("Id: {}", s); self.intern(&s).to_id() })
                .parse_state(input)
        }

        fn typ<'b>(&'b self) -> EnvParser<'a, 'b, I, Id, Type<Id::Untyped>> {
            self.parser(ParserEnv::parse_type)
        }

        fn parse_type(&self, input: State<I>) -> ParseResult<Type<Id::Untyped>, I> {
            self.ident_u()
                .and(many(self.parser(ParserEnv::type_arg)))
                .map(|(typ, args)| Type::Data(typ, args))
                .or(self.parser(ParserEnv::type_arg))
                .map(|typ| { debug!("Parse: {:?}", typ); typ })
                .parse_state(input)
        }

        fn type_arg(&self, input: State<I>) -> ParseResult<Type<Id::Untyped>, I> {
            let array_type = between(string("["), string("]"), self.typ())
                .map(|typ| Type::Array(Box::new(typ)));

            array_type
                .or(between(string("("), string(")"), self.typ()))
                .or(self.ident_u().map(|typ| Type::Data(typ, Vec::new())))
                .parse_state(input)
        }

        fn type_decl(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
            debug!("type_decl");
            self.reserved("type")
                .with(self.ident_u())
                .skip(self.reserved_op("="))
                .and(self.typ())
                .skip(self.reserved("in"))
                .and(self.expr())
                .map(|((id, typ), expr)| Expr::Type(id, typ, Box::new(expr)))
                .parse_state(input)
        }

        fn expr<'b>(&'b self) -> EnvParser<'a, 'b, I, Id, LExpr<Id>> {
            self.parser(ParserEnv::top_expr)
        }

        fn parse_expr(&self, input: State<I>) -> ParseResult<LExpr<Id>, I> {
            let position = input.position;
            debug!("Expr start: {:?}", input.clone().uncons_char().map(|t| t.0));
            let loc = |expr| located(Location { column: position.column, row: position.line, absolute: 0 }, expr);
            choice::<&mut [&mut Parser<Input=I, Output=LExpr<Id>>], _>(&mut [
                &mut parser(|input| self.if_else(input)).map(&loc),
                &mut self.parser(ParserEnv::let_in).map(&loc),
                &mut self.parser(ParserEnv::lambda).map(&loc),
                &mut self.parser(ParserEnv::type_decl).map(&loc),
                &mut self.lex(try(self.integer().skip(not_followed_by(string(".")))))
                    .map(|i| loc(Expr::Literal(LiteralStruct::Integer(i)))),
                &mut self.lex(self.float())
                    .map(|f| loc(Expr::Literal(LiteralStruct::Float(f)))),
                &mut self.ident().map(Expr::Identifier).map(&loc),
                &mut between(self.lex(string("(")), self.lex(string(")")), self.expr())
                ])
                .parse_state(input)
        }

        fn op(&self, input: State<I>) -> ParseResult<Id, I> {
            self.env.op().map(|s| self.intern(&s))
                .parse_state(input)
        }

        fn top_expr(&self, input: State<I>) -> ParseResult<LExpr<Id>, I> {
            fn binop<'b, F, T>(f: F) -> Box<FnMut(T, T) -> T + 'b>
                where F: FnMut(T, T) -> T + 'b {
                Box::new(f)
            }
            let op = parser(|i| self.op(i))
                .map(|op| binop(move |l: LExpr<Id>, r| {
                    let loc = l.location.clone();
                    let expr = Expr::BinOp(Box::new(l), op.clone(), Box::new(r));
                    located(loc, expr) 
                }));

            chainl1(self.parser(ParserEnv::parse_expr), op)
                .parse_state(input)
        }

        fn lambda(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
            self.lex(satisfy(|c| c == '\\'))
                .with(parser(|input| many(self.ident())
                    .skip(self.lex(string("->")))
                    .and(self.expr())
                    .parse_state(input)))
                .map(|(args, expr)| Expr::Lambda(LambdaStruct {
                    id: self.intern(""), free_vars: Vec::new(), arguments: args, body: Box::new(expr)
                }))
                .parse_state(input)
        }

        fn if_else(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
            self.reserved("if")
                .with(self.expr())
                .skip(self.reserved("then"))
                .and(parser(|input| self.expr()
                    .skip(self.reserved("else"))
                    .and(self.expr())
                    .parse_state(input)))
                .map(|(b, (t, f))| Expr::IfElse(Box::new(b), Box::new(t), Some(Box::new(f))))
                .parse_state(input)
        }

        fn let_in(&self, input: State<I>) -> ParseResult<Expr<Id>, I> {
            self.reserved("let")
                .with(self.ident())
                .skip(self.reserved_op("="))
                .and(parser(|input| self.expr()
                    .skip(self.reserved("in"))
                    .and(self.expr())
                    .parse_state(input)))
                .map(|(b, (e1, e2))| Expr::Let(b, Box::new(e1), Some(Box::new(e2))))
                .parse_state(input)
        }
    }


    let ops = "+-*/&|";
    let env = Env::new(LanguageDef {
        ident: Identifier {
            start: letter(),
            rest: alpha_num(),
            reserved: ["if", "then", "else", "let", "in", "type"].iter().map(|x| (*x).into()).collect()
        },
        op: Identifier {
            start: satisfy(move |c| ops.chars().find(|x| *x == c).is_some()),
            rest: satisfy(move |c| ops.chars().find(|x| *x == c).is_some()),
            reserved: ["->", "\\"].iter().map(|x| (*x).into()).collect()
        },
        comment_start: "/*",
        comment_end: "*/",
        comment_line: "//",
    });


    #[derive(Clone)]
    struct A<'a>(&'a str);
    impl <'a> Stream for A<'a> {
        type Item = char;
        fn uncons(self) -> Result<(char, A<'a>), ()> {
            debug!("{:?}", self.0.uncons());
            self.0.uncons().map(|(c, s)| (c, A(s)))
        }
    }
    let input = A(input);
    let env = ParserEnv {
        data: RefCell::new((gc, interner)),
        env: env,
        _marker: PhantomData
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
    use std::io::BufReader;
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
    fn let_(s: &str, e: PExpr) -> PExpr {
        no_loc(Expr::Let(intern(s), box e, None))
    }
    fn id(s: &str) -> PExpr {
        no_loc(Expr::Identifier(intern(s)))
    }
    fn field(s: &str, typ: VMType) -> Field<InternedStr> {
        Field { name: intern(s), typ: typ }
    }
    fn typ(s: &str) -> VMType {
        Type::Data(intern(s), Vec::new())
    }
    fn generic(s: &str) -> VMType {
        Type::Generic(intern(s))
    }
    fn call(e: PExpr, args: Vec<PExpr>) -> PExpr {
        no_loc(Expr::Call(box e, args))
    }
    fn if_else(p: PExpr, if_true: PExpr, if_false: PExpr) -> PExpr {
        no_loc(Expr::IfElse(box p, box if_true, Some(box if_false)))
    }

    fn while_(p: PExpr, expr: PExpr) -> PExpr {
        no_loc(Expr::While(box p, box expr))
    }
    fn assign(p: PExpr, rhs: PExpr) -> PExpr {
        no_loc(Expr::Assign(box p, box rhs))
    }
    fn block(xs: Vec<PExpr>) -> PExpr {
        no_loc(Expr::Block(xs))
    }
    fn lambda(name: &str, args: Vec<InternedStr>, body: PExpr) -> PExpr {
        no_loc(Expr::Lambda(LambdaStruct {
            id: intern(name),
            free_vars: Vec::new(),
            arguments: args,
            body: box body 
        }))
    }
    fn type_decl(name: &str, typ: Type<InternedStr>, body: PExpr) -> PExpr {
        no_loc(Expr::Type(intern(name), typ, box body))
    }

    fn bool(b: bool) -> PExpr {
        no_loc(Expr::Literal(Bool(b)))
    }

    pub fn parse_new<Id>(s: &str) -> LExpr<Id>
        where Id: AstId + Clone {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut(ref mut interner, ref mut gc) = &mut *interner;
        let x = parse_module(gc, interner, s)
            .unwrap_or_else(|err| panic!("{:?}", err));
        x
    }

    #[test]
    fn expression() {
        ::env_logger::init().unwrap();
        let e = parse_new("2 * 3 + 4");
        assert_eq!(e, binop(binop(int(2), "*", int(3)), "+", int(4)));
        let e = parse_new(r#"\x y -> x + y"#);
        assert_eq!(e, lambda("", vec![intern("x"), intern("y")], binop(id("x"), "+", id("y"))));
        let e = parse_new(r#"type Test = Int in 0"#);
        assert_eq!(e, type_decl("Test", Type::Data(intern("Int"), vec![]), int(0)));
    }
}
