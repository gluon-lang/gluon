use lexer::*;
use ast::*;
use interner::InternedStr;

macro_rules! expect(
    ($e: expr, $p: ident (..)) => (
        match *$e.lexer.next() {
            x@$p(..) => x,
            x => {
                $e.lexer.backtrack();
                return Err(format!("Unexpected token {}, expected {}", x, stringify!($p)))
            }
        }
    );
    ($e: expr, $p: ident) => (
        match *$e.lexer.next() {
            x@$p => x,
            x => {
                $e.lexer.backtrack();
                return Err(format!("Unexpected token {}, expected {}", x, $p))
            }
        }
    )
)
macro_rules! expect1(
    ($e: expr, $p: ident ($x: ident)) => (
        match *$e.lexer.next() {
            $p($x) => $x,
            x => {
                $e.lexer.backtrack();
                return Err(format!("Unexpected token {}", x))
            }
        }
    )
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
        Identifier(..) => true,
        _ => false
    }
}

type PString = InternedStr;
type ParseResult<T> = Result<T, String>;

pub struct Parser<'a> {
    lexer: Lexer<'a>
}

impl <'a> Parser<'a> {
    pub fn new(input: &'a mut Buffer) -> Parser<'a> {
        Parser { lexer: Lexer::new(input) }
    }

    pub fn module(&mut self) -> ParseResult<Module<PString>> {
        let mut fns = Vec::new();
        let mut structs = Vec::new();
        loop {
            match *self.lexer.peek() {
                TFn => fns.push(try!(self.function())),
                TStruct => structs.push(try!(self.struct_())),
                _ => break
            }
        }
        Ok(Module { functions: fns, structs: structs })
    }

    fn statement(&mut self) -> ParseResult<(Expr<PString>, bool)> {
        match *self.lexer.peek() {
            TLet => {
                self.lexer.next();
                let id = match expect!(self, TIdentifier(..)) {
                    TIdentifier(id) => id,
                    _ => fail!()
                };
                expect!(self, TAssign);
                let expr = try!(self.expression());
                expect!(self, TSemicolon);
                Ok((Let(id, box expr), true))
            }
            _ => {
                match self.expression() {
                    Ok(e) => {
                        if is_lvalue(&e) && matches!(self.lexer.peek(), &TAssign) {
                            self.lexer.next();
                            let rhs = try!(self.expression());
                            expect!(self, TSemicolon);
                            Ok((Assign(box e, box rhs), true))
                        }
                        else if is_statement(&e) {
                            Ok((e, true))
                        }
                        else if matches!(self.lexer.peek(), &TSemicolon) {
                            self.lexer.next();
                            Ok((e, true))
                        }
                        else {
                            Ok((e, false))
                        }
                    }
                    Err(e) => Err(e)
                }
            }
        }
    }

    pub fn expression(&mut self) -> ParseResult<Expr<PString>> {
        let e = try!(self.sub_expression());
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
                Ok(FieldAccess(box e, id.clone()))
            }
            _ => Ok(e)
        }
    }
    
    fn sub_expression_(&mut self) -> ParseResult<Expr<PString>> {
        match *self.lexer.next() {
            TIdentifier(id) => {
                Ok(Identifier(id))
            }
            TOpenParen => {
                let e = try!(self.expression());
                expect!(self, TCloseParen);
                Ok(e)
            }
            TOpenBrace => {
                self.lexer.backtrack();
                self.block()
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
            x => {
                self.lexer.backtrack();
                Err(format!("Token {} does not start an expression", x))
            }
        }
    }
    fn block(&mut self) -> ParseResult<Expr<PString>> {
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

    fn binary_expression(&mut self, inL: Expr<PString>, minPrecedence : int) -> ParseResult<Expr<PString>> {
        let mut lhs = inL;
        self.lexer.next();
        loop {
            let lhs_op;
            let lhs_prec;
            match *self.lexer.current() {
                TOperator(op) => {
                    lhs_prec = precedence(op.as_slice());
                    lhs_op = op;
                    if lhs_prec < minPrecedence {
                        break
                    }
                }
                _ => break
            };
            debug!("Op {}", lhs_op);

            let mut rhs = try!(self.sub_expression());
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
            lhs = BinOp(box lhs, lhs_op.clone(), box rhs)
        }
        self.lexer.backtrack();
        Ok(lhs)
    }

    fn typ(&mut self) -> ParseResult<Type<PString>> {
        let x = expect1!(self, TIdentifier(x));
        Ok(Type(x))
    }
    
    fn field(&mut self) -> ParseResult<Field<PString>> {
        debug!("Field");
        let name = expect1!(self, TIdentifier(x));
        expect!(self, TColon);
        let typ = try!(self.typ());
        Ok(Field { name: name, typ: typ })
    }

    pub fn struct_(&mut self) -> ParseResult<Struct<PString>> {
        expect!(self, TStruct);
        let name = expect1!(self, TIdentifier(x));
        let fields = try!(self.braces(
            |this| this.sep_by(
                |t| *t == TComma, |this| this.field()
            )
        ));
        Ok(Struct { name: name, fields: fields })
    }

    pub fn function(&mut self) -> ParseResult<Function<PString>> {
        expect!(self, TFn);
        let name = expect1!(self, TIdentifier(x));
        let arguments = try!(self.parens(|this|
            this.sep_by(|t| matches!(t, &TComma), |this| this.field())
        ));
        let return_type = if matches!(self.lexer.peek(), &TRArrow) {
            self.lexer.next();
            try!(self.typ())
        }
        else {
            unit_type()
        };
        let expr = try!(self.block());
        Ok(Function { name: name, arguments: arguments, return_type: return_type, expression: expr })
    }

    fn braces<T>(&mut self, f: |&mut Parser| -> ParseResult<T>) -> ParseResult<T> {
        expect!(self, TOpenBrace);
        let x = try!(f(self));
        expect!(self, TCloseBrace);
        Ok(x)
    }

    fn parens<T>(&mut self, f: |&mut Parser| -> ParseResult<T>) -> ParseResult<T> {
        expect!(self, TOpenParen);
        let x = try!(f(self));
        expect!(self, TCloseParen);
        Ok(x)
    }
    fn sep_by<T>(&mut self, sep: |&Token| -> bool, f: |&mut Parser| -> ParseResult<T>) -> ParseResult<Vec<T>> {
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
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use super::ParseResult;
    use ast::*;
    use std::io::BufReader;
    use interner::*;
    
    type PExpr = Expr<InternedStr>;
    
    fn binop(l: PExpr, s: &str, r: PExpr) -> PExpr {
        BinOp(box l, intern(s), box r)
    }
    fn int(i: int) -> PExpr {
        Literal(Integer(i))
    }
    fn let_(s: &str, e: PExpr) -> PExpr {
        Let(intern(s), box e)
    }
    fn id(s: &str) -> PExpr {
        Identifier(intern(s))
    }
    fn field(s: &str, typ: Type<InternedStr>) -> Field<InternedStr> {
        Field { name: intern(s), typ: typ }
    }
    fn typ(s: &str) -> Type<InternedStr> {
        Type(intern(s))
    }
    fn call(e: PExpr, args: Vec<PExpr>) -> PExpr {
        Call(box e, args)
    }
    fn if_else(p: PExpr, if_true: PExpr, if_false: PExpr) -> PExpr {
        IfElse(box p, box if_true, box if_false)
    }

    fn while_(p: PExpr, expr: PExpr) -> PExpr {
        While(box p, box expr)
    }
    fn assign(p: PExpr, rhs: PExpr) -> PExpr {
        Assign(box p, box rhs)
    }

    fn bool(b: bool) -> PExpr {
        Literal(Bool(b))
    }

    pub fn parse<T>(s: &str, f: |&mut Parser| -> ParseResult<T>) -> T {
        let mut buffer = BufReader::new(s.as_bytes());
        let mut parser = Parser::new(&mut buffer);
        f(&mut parser)
            .unwrap_or_else(|err| fail!(err))
    }

    #[test]
    fn operators() {
        let expr = parse("1 / 4 + (2 - 3) * 2", |p| p.expression());
        assert_eq!(expr, binop(binop(int(1), "/", int(4)), "+", binop(binop(int(2), "-", int(3)), "*", int(2))));
    }
    #[test]
    fn block() {
        let expr = parse("1 / { let x = 2; x }", |p| p.expression());
        assert_eq!(expr, binop(int(1), "/", Block(vec!(let_("x", int(2)), id("x")))));
    }
    #[test]
    fn function() {
        let func = parse("fn main(x: int, y: float) { }", |p| p.function());
        let expected = Function {
            name: intern("main"),
            arguments: vec!(field("x", typ("int")), field("y", typ("float"))),
            expression: Block(vec!()),
            return_type: unit_type()
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
        assert_eq!(expr, if_else(binop(int(1), "<", id("x")), Block(vec![int(1)]), Block(vec![int(0)])));
    }
    #[test]
    fn test_while() {
        let expr = parse("while true { }", |p| p.expression());
        assert_eq!(expr, while_(bool(true), Block(vec![])));
    }
    #[test]
    fn test_assign() {
        let expr = parse("{ y = 2; 2 }", |p| p.expression());
        assert_eq!(expr, Block(vec![assign(id("y"), int(2)), int(2)]));
    }
    #[test]
    fn struct_() {
        let module = parse("struct Test { y: int, f: float }", |p| p.module());
        let expected = Module {
            structs: vec![Struct {
                name: intern("Test"),
                fields: vec![field("y", typ("int")), field("f", typ("float"))]
            }],
            functions: vec![]
        };
        assert_eq!(module, expected);
    }
}
