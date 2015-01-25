use std::fmt;
use ast::*;
use gc::Gc;
use interner::{Interner, InternedStr};
use lexer::{Lexer, Token};
use lexer::Token::{
    TInteger,
    TFloat,
    TString,
    TChar,
    TTrue,
    TFalse,
    TIf,
    TElse,
    TWhile,
    TFor,
    TMatch,
    TFn,
    TData,
    TTrait,
    TImpl,
    TVariable,
    TConstructor,
    TOpenBrace,
    TCloseBrace,
    TOpenParen,
    TCloseParen,
    TOpenBracket,
    TCloseBracket,
    TOperator,
    TSemicolon,
    TDot,
    TComma,
    TColon,
    TLet,
    TAssign,
    TRArrow,
    TMatchArrow,
    TLambda,
    TEOF
};

use self::ParseError::*;

macro_rules! expect {
    ($e: expr, $p: ident (..)) => ({
        match *$e.lexer.next() {
            x@$p(..) => x,
            actual => unexpected!($e, actual, $p)
        }
    });
    ($e: expr, $p: ident) => ({
        match *$e.lexer.next() {
            x@$p => x,
            actual => unexpected!($e, actual, $p)
        }
    })
}

macro_rules! expect1 {
    ($e: expr, $p: ident ($x: ident)) => ({
        match *$e.lexer.next() {
            $p($x) => $x,
            actual => unexpected!($e, actual, $p)
        }
    })
}

macro_rules! matches {
    ($e: expr, $p: pat) => (
        match $e {
            $p => true,
            _ => false
        }
    )
}

macro_rules! unexpected (
    ($parser: expr, $token: expr, $($expected: expr),+) => { {
        $parser.lexer.backtrack();
        static EXPECTED: &'static [&'static str] = &[$(stringify!($expected)),+];
        return Err($parser.unexpected_token(EXPECTED, $token))
    } }
);

fn precedence(s : &str) -> i32 {
    match s {
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

fn is_statement<T>(e: &Expr<T>) -> bool {
    match *e {
        IfElse(..) | Match(..) | Block(..) | While(..) => true,
        _ => false
    }
}

fn is_lvalue<T>(e: &Expr<T>) -> bool {
    match *e {
        Identifier(..) | FieldAccess(..) | ArrayAccess(..) => true,
        _ => false
    }
}

type PString = InternedStr;
enum ParseError {
    UnexpectedToken(&'static [&'static str], Token)
}

impl fmt::Debug for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            UnexpectedToken(expected, actual) => write!(f, "Unexpected token {:?}, expected {:?}", actual, expected),
        }
    }
}

pub type ParseResult<T> = Result<T, Located<ParseError>>;

pub struct Parser<'a, 'b, PString> {
    lexer: Lexer<'a, 'b>,
    type_variables: Vec<InternedStr>,
    make_id_f: Box<FnMut(InternedStr) -> PString + 'static>
}

impl <'a, 'b, PString> Parser<'a, 'b, PString> {
    pub fn new<F>(interner: &'a mut Interner, gc: &'a mut Gc, input: &'b mut Buffer, make_id: F) -> Parser<'a, 'b, PString> 
        where F: FnMut(InternedStr) -> PString + 'static {
        Parser {
            lexer: Lexer::new(interner, gc, input),
            type_variables: Vec::new(),
            make_id_f: box make_id
        }
    }

    fn make_id(&mut self, s: InternedStr) -> PString {
        self.make_id_f.call_mut((s,))
    }

    pub fn module(&mut self) -> ParseResult<Module<PString>> {
        let mut fns = Vec::new();
        let mut datas = Vec::new();
        let mut traits = Vec::new();
        let mut impls = Vec::new();
        loop {
            match *self.lexer.peek() {
                TVariable(..) => fns.push(try!(self.function())),
                TData => datas.push(try!(self.data())),
                TTrait => traits.push(try!(self.trait_())),
                TImpl => impls.push(try!(self.impl_())),
                _ => break
            }
            self.type_variables.clear();
        }
        Ok(Module { datas: datas, functions: fns, traits: traits, impls: impls })
    }

    fn statement(&mut self) -> ParseResult<(LExpr<PString>, bool)> {
        let location = self.lexer.location();
        let (expr, is_stm) = try!(match *self.lexer.peek() {
            TLet => {
                self.lexer.next();
                let id = expect1!(self, TVariable(x));
                expect!(self, TAssign);
                let expr = try!(self.expression());
                expect!(self, TSemicolon);
                Ok((Let(self.make_id(id), box expr), true))
            }
            _ => {
                match self.expression() {
                    Ok(e) => {
                        if is_lvalue(&e.value) && matches!(self.lexer.peek(), &TAssign) {
                            self.lexer.next();
                            let rhs = try!(self.expression());
                            expect!(self, TSemicolon);
                            Ok((Assign(box e, box rhs), true))
                        }
                        else if is_statement(&e.value) {
                            Ok((e.value, true))
                        }
                        else if matches!(self.lexer.peek(), &TSemicolon) {
                            self.lexer.next();
                            Ok((e.value, true))
                        }
                        else {
                            Ok((e.value, false))
                        }
                    }
                    Err(e) => Err(e)
                }
            }
        });
        Ok((Located { location: location, value: expr }, is_stm))
    }

    pub fn expression(&mut self) -> ParseResult<LExpr<PString>> {
        let e = try!(self.located(|this| this.sub_expression()));
        self.binary_expression(e, 0)
    }

    fn sub_expression(&mut self) -> ParseResult<Expr<PString>> {
        let e = try!(self.sub_expression_());
        match self.lexer.peek() {
            &TOpenParen => {
                let args = try!(self.parens(|this|
                    this.sep_by(|t| matches!(t, &TComma), |this| this.expression())
                ));
                Ok(Call(box e, args))
            }
            &TDot => {
                self.lexer.next();
                let id = expect1!(self, TVariable(x));
                Ok(FieldAccess(box e, self.make_id(id.clone())))
            }
            &TOpenBracket => {
                self.lexer.next();
                let index = box try!(self.expression());
                expect!(self, TCloseBracket);
                Ok(ArrayAccess(box e, index))
            }
            _ => Ok(e.value)
        }
    }
    
    fn sub_expression_(&mut self) -> ParseResult<LExpr<PString>> {
        self.located(|this| this.sub_expression_2())
    }
    fn sub_expression_2(&mut self) -> ParseResult<Expr<PString>> {
        match *self.lexer.next() {
            TVariable(id) => {
                Ok(Identifier(self.make_id(id)))
            }
            TConstructor(id) => {
                Ok(Identifier(self.make_id(id)))
            }
            TOpenParen => {
                let e = try!(self.expression());
                expect!(self, TCloseParen);
                Ok(e.value)
            }
            TOpenBrace => {
                self.lexer.backtrack();
                self.block().map(|e| e.value)
            }
            TInteger(i) => {
                Ok(Literal(Integer(i)))
            }
            TFloat(f) => {
                Ok(Literal(Float(f)))
            }
            TString(s) => {
                Ok(Literal(String(s)))
            }
            TTrue => Ok(Literal(Bool(true))),
            TFalse => Ok(Literal(Bool(false))),
            TIf => {
                let pred = box try!(self.expression());
                let if_true = box try!(self.block());
                let if_false = match *self.lexer.peek() {
                    TElse => {
                        self.lexer.next();
                        Some(box match *self.lexer.peek() {
                            TOpenBrace => try!(self.block()),
                            TIf => try!(self.expression()),
                            x => {
                                static EXPECTED: &'static [&'static str] = &["{", "if"];
                                return Err(self.unexpected_token(EXPECTED, x))
                            }
                        })
                    }
                    _ => None
                };
                Ok(IfElse(pred, if_true, if_false))
            }
            TWhile => {
                let pred = box try!(self.expression());
                let b = box try!(self.block());
                Ok(While(pred, b))
            }
            TMatch => {
                let expr = box try!(self.expression());
                let alternatives = try!(self.braces(
                    |this| this.many(|t| *t == TCloseBrace, |this| this.alternative())
                ));
                Ok(Match(expr, alternatives))
            }
            TOpenBracket => {
                let args = try!(self.sep_by(|t| *t == TComma, |this| this.expression()));
                expect!(self, TCloseBracket);
                let dummy = self.lexer.intern("[]");
                Ok(Array(ArrayStruct { id: self.make_id(dummy), expressions: args }))
            }
            TLambda => { self.lexer.backtrack(); self.lambda() }
            x => {
                self.lexer.backtrack();
                static EXPECTED: &'static [&'static str] = &["TVariable", "(", "{", "TInteger", "TFloat", "TString", "true", "false", "if", "while", "match", "[", "\\"];
                Err(self.unexpected_token(EXPECTED, x))
            }
        }
    }

    fn lambda(&mut self) -> ParseResult<Expr<PString>> {
        expect!(self, TLambda);
        let args = try!(self.many(|t| *t == TRArrow, |this| {
            let id = expect1!(this, TVariable(x));
            Ok(this.make_id(id))
        }));
        expect!(self, TRArrow);
        let body = box try!(self.expression());
        let s = self.lexer.intern("");
        Ok(Lambda(LambdaStruct { id: self.make_id(s), free_vars: Vec::new(), arguments: args, body: body }))
    }

    fn block(&mut self) -> ParseResult<LExpr<PString>> {
        self.located(|this| this.block_())
    }
    fn block_(&mut self) -> ParseResult<Expr<PString>> {
        expect!(self, TOpenBrace);
        let mut exprs = Vec::new();
        while !matches!(self.lexer.peek(), &TCloseBrace) {
            let (expr, is_stm) = try!(self.statement());
            exprs.push(expr);
            if !is_stm {
                break
            }
        }
        expect!(self, TCloseBrace);
        Ok(Block(exprs))
    }

    fn binary_expression(&mut self, mut lhs: LExpr<PString>, min_precedence : i32) -> ParseResult<LExpr<PString>> {
        self.lexer.next();
        loop {
            let location = self.lexer.location();
            let lhs_op;
            let lhs_prec;
            match *self.lexer.current() {
                TOperator(op) => {
                    lhs_prec = precedence(op.as_slice());
                    lhs_op = op;
                    if lhs_prec < min_precedence {
                        break
                    }
                }
                _ => break
            };
            debug!("Op {}", lhs_op);

            let mut rhs = try!(self.located(|this| this.sub_expression()));
            self.lexer.next();
            loop {
                let lookahead;
                match *self.lexer.current() {
                    TOperator(op) => {
                        lookahead = precedence(op.as_slice());
                        if lookahead < lhs_prec {
                            break
                        }
                        debug!("Inner op {}", op);
                    }
                    _ => break
                }
                self.lexer.backtrack();
                rhs = try!(self.binary_expression(rhs, lookahead));
                self.lexer.next();
            }
            lhs = Located {
                location: location,
                value: BinOp(box lhs, self.make_id(lhs_op.clone()), box rhs)
            };
        }
        self.lexer.backtrack();
        Ok(lhs)
    }

    fn alternative(&mut self) -> ParseResult<Alternative<PString>> {
        let pattern = try!(self.pattern());
        expect!(self, TMatchArrow);
        let expression = try!(self.block());
        Ok(Alternative { pattern: pattern, expression: expression })
    }

    fn pattern(&mut self) -> ParseResult<Pattern<PString>> {
        match *self.lexer.next() {
            TConstructor(name) => {
                let args = try!(self.parens(|this|
                    this.sep_by(|t| *t == TComma, |this| {
                        let arg = expect1!(this, TVariable(x));
                        Ok(this.make_id(arg))
                    })
                ));
                Ok(ConstructorPattern(self.make_id(name), args))
            }
            TVariable(name) => {
                Ok(IdentifierPattern(self.make_id(name)))
            }
            x => {
                self.lexer.backtrack();
                static EXPECTED: &'static [&'static str] = &["TVariable", "TConstructor"];
                Err(self.unexpected_token(EXPECTED, x))
            }
        }
    }

    fn typ(&mut self) -> ParseResult<VMType> {
        let x = match *self.lexer.next() {
            TConstructor(x) => {
                match str_to_primitive_type(x) {
                    Some(t) => t,
                    None => {
                        let vars = match *self.lexer.peek() {
                            TOperator(op) if op.as_slice() == "<" => {
                                try!(self.angle_brackets(|this| {
                                    this.sep_by(|t| *t == TComma, |this| this.typ())
                                }))
                            }
                            _ => Vec::new()
                        };
                        Type(x, vars)
                    }
                }
            }
            TVariable(name) => Generic(name),
            TFn => {
                let args = try!(self.parens(|this|
                    this.sep_by(|t| *t == TComma, |this|
                        this.typ()
                    )
                ));
                expect!(self, TRArrow);
                FunctionType(args, box try!(self.typ()))
            }
            TOpenBracket => {
                let t = try!(self.typ());
                expect!(self, TCloseBracket);
                ArrayType(box t)
            }
            TOpenParen => {
                expect!(self, TCloseParen);
                UNIT_TYPE.clone()
            }
            x => {
                self.lexer.backtrack();
                static EXPECTED: &'static [&'static str] = &["fn"];
                return Err(self.unexpected_token(EXPECTED, x))
            }
        };
        Ok(x)
    }
    
    fn field(&mut self) -> ParseResult<Field> {
        debug!("Field");
        let name = expect1!(self, TVariable(x));
        expect!(self, TColon);
        let typ = try!(self.typ());
        Ok(Field { name: name, typ: typ })
    }

    pub fn data(&mut self) -> ParseResult<Data<PString>> {
        expect!(self, TData);
        let name = expect1!(self, TConstructor(x));
        let type_variables = try!(self.many(|t| *t == TAssign, |this| Ok(expect1!(this, TVariable(x)))));
        expect!(self, TAssign);
        let pipe = TOperator(self.lexer.intern("|"));
        let constructors = try!(self.sep_by(
            |t| *t == pipe, |this| this.constructor())
        );
        Ok(Data { name: self.make_id(name), type_variables: type_variables, constructors: constructors })
    }
    pub fn constructor(&mut self) -> ParseResult<Constructor<PString>> {
        let name = expect1!(self, TConstructor(x));
        let constructor_type = match *self.lexer.peek() {
            TOpenParen => {
                let arguments = try!(self.parens(
                    |this| this.sep_by(
                        |t| *t == TComma, |this| this.typ()
                    )
                ));
                ConstructorType::Tuple(arguments)
            }
            TOpenBrace => {
                let fields = try!(self.braces(
                    |this| this.sep_by(
                        |t| *t == TComma, |this| this.field()
                    )
                ));
                ConstructorType::Record(fields)
            }
            x => unexpected!(self, x, TOpenParen, TOpenBrace)
        };
        Ok(Constructor { name: self.make_id(name), arguments: constructor_type })
    }

    pub fn trait_(&mut self) -> ParseResult<Trait<PString>> {
        expect!(self, TTrait);
        let name = expect1!(self, TConstructor(x));
        let self_variable = self.lexer.intern("Self");;//expect1!(self, TVariable(x));//TODO parse an actual variable
        let declarations = try!(self.braces(|this| this.many(|t| *t == TCloseBrace, |this| {
            let decl = try!(this.function_declaration());
            expect!(this, TSemicolon);
            Ok(decl)
        })));
        Ok(Trait { name: self.make_id(name), self_variable: self_variable, declarations: declarations })
    }
    pub fn impl_(&mut self) -> ParseResult<Impl<PString>> {
        expect!(self, TImpl);
        let type_variables = try!(self.type_variables());
        let trait_name = expect1!(self, TConstructor(x));
        expect!(self, TFor);
        let typ = try!(self.typ());
        let functions = try!(self.braces(|this| this.many(|t| *t == TCloseBrace, |this| this.function() )));
        Ok(Impl {
            trait_name: self.make_id(trait_name),
            type_variables: type_variables,
            typ: typ,
            functions: functions
        })
    }
    
    fn angle_brackets<F, T>(&mut self, f: F) -> ParseResult<T>
        where F: FnOnce(&mut Parser<PString>) -> ParseResult<T> {
        static EXPECTED_LT: &'static [&'static str] = &["<"];
        static EXPECTED_GT: &'static [&'static str] = &[">"];
        match *self.lexer.peek() {
            TOperator(s) if s.as_slice() == "<" => {
                self.lexer.next();
                let result = try!(f(self));
                match *self.lexer.next() {
                    TOperator(x) if x.as_slice() == ">" => (),
                    x => return Err(self.unexpected_token(EXPECTED_GT, x))
                }
                Ok(result)
            }
            x => Err(self.unexpected_token(EXPECTED_LT, x))
        }
    }

    fn constraints(&mut self) -> ParseResult<Vec<Constraint>> {
        match *self.lexer.peek() {
            TOpenParen => {
                self.lexer.next();
                let vars = try!(self.sep_by(|t| *t == TComma, |this| {
                    let name = expect1!(this, TConstructor(x));
                    let var = expect1!(this, TVariable(x));
                    Ok(Constraint { name: name, type_variable: var })
                }));
                expect!(self, TCloseParen);
                Ok(vars)
            }
            _ => Ok(Vec::new())
        }
    }

    fn type_variables(&mut self) -> ParseResult<Vec<Constraint>> {
        match *self.lexer.peek() {
            TOperator(s) if s.as_slice() == "<" => {
                let vars = try!(self.angle_brackets(|this| this.sep_by(|t| *t == TComma, |this| {
                    let id = expect1!(this, TVariable(x));
                    let constraints = match *this.lexer.peek() {
                        TColon => {
                            this.lexer.next();
                            expect1!(this, TConstructor(x))
                        }
                        _ => panic!()
                    };
                    Ok(Constraint { type_variable: id, name: constraints })
                })));
                Ok(vars)
            }
            _ => Ok(Vec::new())
        }
    }

    pub fn function(&mut self) -> ParseResult<Function<PString>> {
        let declaration = try!(self.function_declaration());
        expect!(self, TSemicolon);
        expect1!(self, TVariable(x));
        expect!(self, TAssign);
        let expr = try!(self.located(|this| this.lambda()));

        Ok(Function {
            declaration: declaration,
            expression: expr
        })
    }
    pub fn function_declaration(&mut self) -> ParseResult<FunctionDeclaration<PString>> {
        let name = expect1!(self, TVariable(x));
        expect!(self, TColon);
        let type_variables = try!(self.type_variables());
        let arguments = try!(self.parens(|this|
            this.sep_by(|t| matches!(t, &TComma), |this| this.typ())
        ));
        expect!(self, TRArrow);
        let return_type = try!(self.typ());
        Ok(FunctionDeclaration {
            name: self.make_id(name),
            type_variables: type_variables,
            arguments: arguments,
            return_type: return_type
        })
    }

    fn braces<F, T>(&mut self, f: F) -> ParseResult<T>
        where F: FnOnce(&mut Parser<PString>) -> ParseResult<T> {
        expect!(self, TOpenBrace);
        let x = try!(f(self));
        expect!(self, TCloseBrace);
        Ok(x)
    }

    fn parens<F, T>(&mut self, f: F) -> ParseResult<T>
        where F: FnOnce(&mut Parser<PString>) -> ParseResult<T> {
        expect!(self, TOpenParen);
        let x = try!(f(self));
        expect!(self, TCloseParen);
        Ok(x)
    }

    fn many<P, F, T>(&mut self, mut terminator: P, mut f: F) -> ParseResult<Vec<T>>
        where P: FnMut(&Token) -> bool,
              F: FnMut(&mut Parser<PString>) -> ParseResult<T> {
        let mut result = Vec::new();
        while !terminator(self.lexer.peek()) {
            result.push(try!(f(self)));
        }
        Ok(result)
    }
    fn sep_by<F, S, T>(&mut self, mut sep: S, mut f: F) -> ParseResult<Vec<T>>
        where S: FnMut(&Token) -> bool,
              F: FnMut(&mut Parser<PString>) -> ParseResult<T> {
        let mut result = Vec::new();
        match f(self) {
            Ok(x) => result.push(x),
            Err(_) => return Ok(result)
        }
        while sep(self.lexer.peek()) {
            self.lexer.next();
            let x = try!(f(self));
            result.push(x);
        }
        Ok(result)
    }
    fn located<F, T>(&mut self, f: F) -> ParseResult<Located<T>>
        where F: FnOnce(&mut Parser<PString>) -> ParseResult<T> {
        let location = self.lexer.location();
        let value = try!(f(self));
        Ok(Located { location: location, value: value })
    }

    fn unexpected_token(&self, expected: &'static [&'static str], actual: Token) -> Located<ParseError> {
        Located { location: self.lexer.location(), value: UnexpectedToken(expected, actual) }
    }
}

#[cfg(test)]
pub mod tests {
    use super::{Parser, ParseResult};
    use ast::*;
    use std::io::BufReader;
    use interner::*;
    use interner::tests::*;
    
    type PExpr = LExpr<InternedStr>;
    
    fn binop(l: PExpr, s: &str, r: PExpr) -> PExpr {
        no_loc(BinOp(box l, intern(s), box r))
    }
    fn int(i: i64) -> PExpr {
        no_loc(Literal(Integer(i)))
    }
    fn let_(s: &str, e: PExpr) -> PExpr {
        no_loc(Let(intern(s), box e))
    }
    fn id(s: &str) -> PExpr {
        no_loc(Identifier(intern(s)))
    }
    fn field(s: &str, typ: VMType) -> Field {
        Field { name: intern(s), typ: typ }
    }
    fn typ(s: &str) -> VMType {
        Type(intern(s), Vec::new())
    }
    fn call(e: PExpr, args: Vec<PExpr>) -> PExpr {
        no_loc(Call(box e, args))
    }
    fn if_else(p: PExpr, if_true: PExpr, if_false: PExpr) -> PExpr {
        no_loc(IfElse(box p, box if_true, Some(box if_false)))
    }

    fn while_(p: PExpr, expr: PExpr) -> PExpr {
        no_loc(While(box p, box expr))
    }
    fn assign(p: PExpr, rhs: PExpr) -> PExpr {
        no_loc(Assign(box p, box rhs))
    }
    fn block(xs: Vec<PExpr>) -> PExpr {
        no_loc(Block(xs))
    }
    fn lambda(args: Vec<InternedStr>, body: PExpr) -> PExpr {
        no_loc(Lambda(LambdaStruct {
            id: intern(""),
            free_vars: Vec::new(),
            arguments: args,
            body: box body 
        }))
    }

    fn bool(b: bool) -> PExpr {
        no_loc(Literal(Bool(b)))
    }

    pub fn parse<F, T>(s: &str, f: F) -> T
        where F: FnOnce(&mut Parser<InternedStr>) -> ParseResult<T> {
        let mut buffer = BufReader::new(s.as_bytes());
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut(ref mut interner, ref mut gc) = &mut *interner;
        let mut parser = Parser::new(interner, gc, &mut buffer, |s| s);
        let x = f(&mut parser)
            .unwrap_or_else(|err| panic!("{:?}", err));
        x
    }

    #[test]
    fn operators() {
        let expr = parse("1 / 4 + (2 - 3) * 2", |p| p.expression());
        assert_eq!(expr, binop(binop(int(1), "/", int(4)), "+", binop(binop(int(2), "-", int(3)), "*", int(2))));
    }
    #[test]
    fn block_test() {
        let expr = parse("1 / { let x = 2; x }", |p| p.expression());
        assert_eq!(expr, binop(int(1), "/", block(vec!(let_("x", int(2)), id("x")))));
    }
    #[test]
    fn function() {
        let s =
r"
main : (Int,Float) -> ();
main = \x y -> { }";
        let func = parse(s, |p| p.function());
        let expected = Function {
            declaration: FunctionDeclaration {
                name: intern("main"),
                type_variables: Vec::new(),
                arguments: vec!(INT_TYPE.clone(), FLOAT_TYPE.clone()),
                return_type: UNIT_TYPE.clone()
            },
            expression: lambda(vec![intern("x"), intern("y")], block(vec!()))
        };
        assert_eq!(func, expected);
    }
    #[test]
    fn generic_function() {
        let func = parse(
r"
id : (a) -> a;
id = \x -> { x }
", |p| p.function());
        let a = Generic(intern("a"));
        let expected = Function {
            declaration: FunctionDeclaration {
                name: intern("id"),
                type_variables: Vec::new(),
                arguments: vec![a.clone()],
                return_type: a.clone()
            },
            expression: lambda(vec![intern("x")], block(vec![id("x")]))
        };
        assert_eq!(func, expected);
    }
    #[test]
    fn call_function() {
        let expr = parse("test(1, x)", |p| p.expression());
        assert_eq!(expr, call(id("test"), vec![int(1), id("x")]));
    }
    #[test]
    fn test_if_else() {
        let expr = parse("if 1 < x { 1 } else { 0 }", |p| p.expression());
        assert_eq!(expr, if_else(binop(int(1), "<", id("x")), block(vec![int(1)]), block(vec![int(0)])));
    }
    #[test]
    fn test_while() {
        let expr = parse("while true { }", |p| p.expression());
        assert_eq!(expr, while_(bool(true), block(vec![])));
    }
    #[test]
    fn test_assign() {
        let expr = parse("{ y = 2; 2 }", |p| p.expression());
        assert_eq!(expr, block(vec![assign(id("y"), int(2)), int(2)]));
    }
    #[test]
    fn data() {
        let module = parse("data Test = Test { y: Int, f: Float }", |p| p.data());
        let expected = Data {
            name: intern("Test"),
            type_variables: Vec::new(),
            constructors: vec![Constructor {
                name: intern("Test"),
                arguments: ConstructorType::Record(vec![field("y", INT_TYPE.clone()), field("f", FLOAT_TYPE.clone())])
            }]
        };
        assert_eq!(module, expected);
    }
    #[test]
    fn trait_() {
        let module = parse(
r"
trait Test {
    test : (Self) -> Int;
    test2 : (Int, Self) -> ();
}", |p| p.trait_());
        let expected = Trait {
            name: intern("Test"),
            self_variable: intern("Self"),
            declarations: vec![
                FunctionDeclaration {
                    name: intern("test"),
                    type_variables: Vec::new(),
                    arguments: vec![typ("Self")],
                    return_type: INT_TYPE.clone()
                },
                FunctionDeclaration {
                    name: intern("test2"),
                    type_variables: Vec::new(),
                    arguments: vec![INT_TYPE.clone(), typ("Self")],
                    return_type: UNIT_TYPE.clone()
                },
            ]
        };
        assert_eq!(module, expected);
    }
    #[test]
    fn impl_() {
        parse(
r"
impl Test for Int {
    test : (Self) -> Int;
    test = \x -> { x }

    test2 : (Int, Self) -> ();
    test2 = \x y -> { x + y; }
}
", |p| p.impl_());
    }

    #[test]
    fn function_type() {
        let typ = parse("fn () -> fn (Int) -> Float", |p| p.typ());
        assert_eq!(typ, FunctionType(Vec::new(), box FunctionType(vec![INT_TYPE.clone()], box FLOAT_TYPE.clone())));
    }

    #[test]
    fn create_lambda() {
        parse(
r"
main : () -> fn (int) -> float;
main = \ -> {
    \x -> 1.0
}", |p| p.function());
    }
    #[test]
    fn parameterized_types() {
        parse(
r"data Option a = Some(a) |None()

data Named a = Named {
    name: String,
    value: a
}

trait Test {
}

test : <a: Test> (a) -> Option<a>;
test = \x -> {
    Some(x)
}

", |p| p.module());
    }
}
