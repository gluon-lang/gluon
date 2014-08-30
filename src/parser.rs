use std::fmt;
use ast::*;
use interner::{Interner, InternedStr};
use lexer::{
    Lexer,
    Token,
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
    TStruct,
    TEnum,
    TTrait,
    TImpl,
    TIdentifier,
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

macro_rules! expect(
    ($e: expr, $p: ident (..)) => ({
        match *$e.lexer.next() {
            x@$p(..) => x,
            actual => {
                $e.lexer.backtrack();
                static expected: &'static [&'static str] = &[stringify!($p)];
                return Err($e.unexpected_token(expected, actual))
            }
        }
    });
    ($e: expr, $p: ident) => ({
        match *$e.lexer.next() {
            x@$p => x,
            actual => {
                $e.lexer.backtrack();
                static expected: &'static [&'static str] = &[stringify!($p)];
                return Err($e.unexpected_token(expected, actual))
            }
        }
    })
)
macro_rules! expect1(
    ($e: expr, $p: ident ($x: ident)) => ({
        match *$e.lexer.next() {
            $p($x) => $x,
            actual => {
                $e.lexer.backtrack();
                static expected: &'static [&'static str] = &[stringify!($p)];
                return Err($e.unexpected_token(expected, actual))
            }
        }
    })
)

macro_rules! matches(
    ($e: expr, $p: pat) => (
        match $e {
            $p => true,
            _ => false
        }
    )
)
fn precedence(s : &str) -> int {
    match s {
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

impl fmt::Show for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            UnexpectedToken(expected, actual) => write!(f, "Unexpected token {}, expected {}", actual, expected),
        }
    }
}

pub type ParseResult<T> = Result<T, Located<ParseError>>;

pub struct Parser<'a, 'b, PString> {
    lexer: Lexer<'a, 'b>,
    make_id_f: |InternedStr|:'static -> PString
}

impl <'a, 'b, PString> Parser<'a, 'b, PString> {
    pub fn new(interner: &'a mut Interner, input: &'b mut Buffer, make_id: |InternedStr|:'static -> PString) -> Parser<'a, 'b, PString> {
        Parser { lexer: Lexer::new(interner, input), make_id_f: make_id }
    }

    fn make_id(&mut self, s: InternedStr) -> PString {
        (self.make_id_f)(s)
    }

    pub fn module(&mut self) -> ParseResult<Module<PString>> {
        let mut fns = Vec::new();
        let mut structs = Vec::new();
        let mut enums = Vec::new();
        let mut traits = Vec::new();
        let mut impls = Vec::new();
        loop {
            match *self.lexer.peek() {
                TFn => fns.push(try!(self.function())),
                TStruct => structs.push(try!(self.struct_())),
                TEnum => enums.push(try!(self.enum_())),
                TTrait => traits.push(try!(self.trait_())),
                TImpl => impls.push(try!(self.impl_())),
                _ => break
            }
        }
        Ok(Module { enums: enums, functions: fns, structs: structs, traits: traits, impls: impls })
    }

    fn statement(&mut self) -> ParseResult<(LExpr<PString>, bool)> {
        let location = self.lexer.location();
        let (expr, is_stm) = try!(match *self.lexer.peek() {
            TLet => {
                self.lexer.next();
                let id = match expect!(self, TIdentifier(..)) {
                    TIdentifier(id) => id,
                    _ => fail!()
                };
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
                let id = expect1!(self, TIdentifier(x));
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
            TIdentifier(id) => {
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
                expect!(self, TElse);
                let if_false = box try!(self.block());
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
                    |this| this.many(|this| this.alternative())
                ));
                Ok(Match(expr, alternatives))
            }
            TOpenBracket => {
                let args = try!(self.sep_by(|t| *t == TComma, |this| this.expression()));
                expect!(self, TCloseBracket);
                let dummy = self.lexer.interner.intern("[]");
                Ok(Array(Array { id: self.make_id(dummy), expressions: args }))
            }
            TLambda => {
                let args = try!(self.many(|this| {
                    let id = expect1!(this, TIdentifier(x));
                    Ok(this.make_id(id))
                }));
                expect!(self, TRArrow);
                let body = box try!(self.expression());
                let s = self.lexer.interner.intern("");
                Ok(Lambda(Lambda { id: self.make_id(s), free_vars: Vec::new(), arguments: args, body: body }))
            }
            x => {
                self.lexer.backtrack();
                static expected: &'static [&'static str] = &["TIdentifier", "(", "{", "TInteger", "TFloat", "TString", "true", "false", "if", "while", "match", "[", "\\"];
                Err(self.unexpected_token(expected, x))
            }
        }
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

    fn binary_expression(&mut self, mut lhs: LExpr<PString>, min_precedence : int) -> ParseResult<LExpr<PString>> {
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
        let name = expect1!(self, TIdentifier(x));
        if *self.lexer.peek() == TOpenParen {
            let args = try!(self.parens(|this|
                this.sep_by(|t| *t == TComma, |this| {
                    let arg = expect1!(this, TIdentifier(x));
                    Ok(this.make_id(arg))
                })
            ));
            Ok(ConstructorPattern(self.make_id(name), args))
        }
        else {
            Ok(IdentifierPattern(self.make_id(name)))
        }
    }

    fn typ(&mut self) -> ParseResult<Type<InternedStr>> {
        let x = match *self.lexer.next() {
            TIdentifier(x) => {
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
            x => {
                self.lexer.backtrack();
                static expected: &'static [&'static str] = &["fn"];
                return Err(self.unexpected_token(expected, x))
            }
        };
        Ok(x)
    }
    
    fn field(&mut self) -> ParseResult<Field> {
        debug!("Field");
        let name = expect1!(self, TIdentifier(x));
        expect!(self, TColon);
        let typ = try!(self.typ());
        Ok(Field { name: name, typ: typ })
    }

    pub fn enum_(&mut self) -> ParseResult<Enum<PString>> {
        expect!(self, TEnum);
        let name = expect1!(self, TIdentifier(x));
        let type_variables = try!(self.type_variables());
        let constructors = try!(self.braces(
            |this| this.sep_by(
                |t| *t == TComma, |this| this.constructor()
            )
        ));
        Ok(Enum { name: self.make_id(name), type_variables: type_variables, constructors: constructors })
    }
    pub fn constructor(&mut self) -> ParseResult<Constructor<PString>> {
        let name = expect1!(self, TIdentifier(x));
        let arguments = try!(self.parens(
            |this| this.sep_by(
                |t| *t == TComma, |this| this.typ()
            )
        ));
        Ok(Constructor { name: self.make_id(name), arguments: arguments })
    }

    pub fn struct_(&mut self) -> ParseResult<Struct<PString>> {
        expect!(self, TStruct);
        let name = expect1!(self, TIdentifier(x));
        let type_variables = try!(self.type_variables());
        let fields = try!(self.braces(
            |this| this.sep_by(
                |t| *t == TComma, |this| this.field()
            )
        ));
        Ok(Struct { name: self.make_id(name), type_variables: type_variables, fields: fields })
    }

    pub fn trait_(&mut self) -> ParseResult<Trait<PString>> {
        expect!(self, TTrait);
        let name = expect1!(self, TIdentifier(x));
        let declarations = try!(self.braces(|this| this.many(|this| {
            let decl = try!(this.function_declaration());
            expect!(this, TSemicolon);
            Ok(decl)
        })));
        Ok(Trait { name: self.make_id(name), declarations: declarations })
    }
    pub fn impl_(&mut self) -> ParseResult<Impl<PString>> {
        expect!(self, TImpl);
        let type_variables = try!(self.type_variables());
        let trait_name = expect1!(self, TIdentifier(x));
        expect!(self, TFor);
        let typ = try!(self.typ());
        let functions = try!(self.braces(|this| this.many(|this| this.function() )));
        Ok(Impl {
            trait_name: self.make_id(trait_name),
            type_variables: type_variables,
            typ: typ,
            functions: functions
        })
    }
    
    fn angle_brackets<T>(&mut self, f: |&mut Parser<PString>| -> ParseResult<T>) -> ParseResult<T> {
        static expected_lt: &'static [&'static str] = &["<"];
        static expected_gt: &'static [&'static str] = &[">"];
        match *self.lexer.peek() {
            TOperator(s) if s.as_slice() == "<" => {
                self.lexer.next();
                let result = try!(f(self));
                match *self.lexer.next() {
                    TOperator(x) if x.as_slice() == ">" => (),
                    x => return Err(self.unexpected_token(expected_gt, x))
                }
                Ok(result)
            }
            x => Err(self.unexpected_token(expected_lt, x))
        }
    }
    fn type_variables(&mut self) -> ParseResult<Vec<Constraints>> {
        match *self.lexer.peek() {
            TOperator(s) if s.as_slice() == "<" => {
                let vars = try!(self.angle_brackets(|this| this.sep_by(|t| *t == TComma, |this| {
                    let id = expect1!(this, TIdentifier(x));
                    let constraints = match *this.lexer.peek() {
                        TColon => {
                            this.lexer.next();
                            vec![try!(this.typ())]
                        }
                        _ => Vec::new()
                    };
                    Ok(Constraints { type_variable: id, constraints: constraints })
                })));
                Ok(vars)
            }
            _ => Ok(Vec::new())
        }
    }

    pub fn function_declaration(&mut self) -> ParseResult<FunctionDeclaration<PString>> {
        expect!(self, TFn);
        let name = expect1!(self, TIdentifier(x));
        let type_variables = try!(self.type_variables());
        let arguments = try!(self.parens(|this|
            this.sep_by(|t| matches!(t, &TComma), |this| this.field())
        ));
        let return_type = if matches!(self.lexer.peek(), &TRArrow) {
            self.lexer.next();
            try!(self.typ())
        }
        else {
            unit_type.clone()
        };
        Ok(FunctionDeclaration {
            name: self.make_id(name),
            type_variables: type_variables,
            arguments: arguments,
            return_type: return_type
        })
    }

    pub fn function(&mut self) -> ParseResult<Function<PString>> {
        let declaration = try!(self.function_declaration());
        let expr = try!(self.block());
        Ok(Function { declaration: declaration, expression: expr })
    }

    fn braces<T>(&mut self, f: |&mut Parser<PString>| -> ParseResult<T>) -> ParseResult<T> {
        expect!(self, TOpenBrace);
        let x = try!(f(self));
        expect!(self, TCloseBrace);
        Ok(x)
    }

    fn parens<T>(&mut self, f: |&mut Parser<PString>| -> ParseResult<T>) -> ParseResult<T> {
        expect!(self, TOpenParen);
        let x = try!(f(self));
        expect!(self, TCloseParen);
        Ok(x)
    }

    fn many<T>(&mut self, f: |&mut Parser<PString>| -> ParseResult<T>) -> ParseResult<Vec<T>> {
        let mut result = Vec::new();
        loop {
            match f(self) {
                Ok(x) => result.push(x),
                Err(_) => break
            }
        }
        Ok(result)
    }
    fn sep_by<T>(&mut self, sep: |&Token| -> bool, f: |&mut Parser<PString>| -> ParseResult<T>) -> ParseResult<Vec<T>> {
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
    fn located<T>(&mut self, f: |&mut Parser<PString>| -> ParseResult<T>) -> ParseResult<Located<T>> {
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
    fn int(i: int) -> PExpr {
        no_loc(Literal(Integer(i)))
    }
    fn let_(s: &str, e: PExpr) -> PExpr {
        no_loc(Let(intern(s), box e))
    }
    fn id(s: &str) -> PExpr {
        no_loc(Identifier(intern(s)))
    }
    fn field(s: &str, typ: Type<InternedStr>) -> Field {
        Field { name: intern(s), typ: typ }
    }
    fn typ(s: &str) -> Type<InternedStr> {
        Type(intern(s), Vec::new())
    }
    fn call(e: PExpr, args: Vec<PExpr>) -> PExpr {
        no_loc(Call(box e, args))
    }
    fn if_else(p: PExpr, if_true: PExpr, if_false: PExpr) -> PExpr {
        no_loc(IfElse(box p, box if_true, box if_false))
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

    fn bool(b: bool) -> PExpr {
        no_loc(Literal(Bool(b)))
    }

    pub fn parse<T>(s: &str, f: |&mut Parser<InternedStr>|:'static -> ParseResult<T>) -> T {
        let mut buffer = BufReader::new(s.as_bytes());
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let mut parser = Parser::new(&mut *interner, &mut buffer, |s| s);
        let x = f(&mut parser)
            .unwrap_or_else(|err| fail!(err));
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
        let func = parse("fn main(x: int, y: float) { }", |p| p.function());
        let expected = Function {
            declaration: FunctionDeclaration {
                name: intern("main"),
                type_variables: Vec::new(),
                arguments: vec!(field("x", int_type.clone()), field("y", float_type.clone())),
                return_type: unit_type.clone()
            },
            expression: block(vec!())
        };
        assert_eq!(func, expected);
    }
    #[test]
    fn generic_function() {
        let func = parse("fn id<T>(x: T) -> T { x }", |p| p.function());
        let expected = Function {
            declaration: FunctionDeclaration {
                name: intern("id"),
                type_variables: vec![Constraints { type_variable: intern("T"), constraints: Vec::new() }],
                arguments: vec![field("x", typ("T"))],
                return_type: typ("T")
            },
            expression: block(vec![id("x")])
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
    fn struct_() {
        let module = parse("struct Test { y: int, f: float }", |p| p.struct_());
        let expected = Struct {
            name: intern("Test"),
            type_variables: Vec::new(),
            fields: vec![field("y", int_type.clone()), field("f", float_type.clone())]
        };
        assert_eq!(module, expected);
    }
    #[test]
    fn trait_() {
        let module = parse("trait Test { fn test(x: Self) -> int; fn test2(x: int, y: Self); }", |p| p.trait_());
        let expected = Trait {
            name: intern("Test"),
            declarations: vec![
                FunctionDeclaration {
                    name: intern("test"),
                    type_variables: Vec::new(),
                    arguments: vec![field("x", typ("Self"))],
                    return_type: int_type.clone()
                },
                FunctionDeclaration {
                    name: intern("test2"),
                    type_variables: Vec::new(),
                    arguments: vec![field("x", int_type.clone()), field("y", typ("Self"))],
                    return_type: unit_type.clone()
                },
            ]
        };
        assert_eq!(module, expected);
    }
    #[test]
    fn impl_() {
        parse(
r"impl Test for int { fn test(x: Self) -> int { x } fn test2(x: int, y: Self) { x + y; } }", |p| p.impl_());
    }
    #[test]
    fn function_type() {
        let typ = parse("fn () -> fn (int) -> float", |p| p.typ());
        assert_eq!(typ, FunctionType(Vec::new(), box FunctionType(vec![int_type.clone()], box float_type.clone())));
    }
    #[test]
    fn lambda() {
        parse(
r"fn main() -> fn (int) -> float {
    \x -> 1.0
}", |p| p.function());
    }
    #[test]
    fn parameterized_types() {
        parse(
r"enum Option<T> {
    Some(T),
    None()
}
struct Named<T> {
    name: String,
    value: T
}

trait Test {
}

fn test<T: Test>(x: T) -> Option<T> {
    Some(x)
}

", |p| p.module());
    }
}
