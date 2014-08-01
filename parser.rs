use lexer::*;
use ast::*;
use interner::InternedStr;

macro_rules! expect(
    ($e: expr, $p: pat) => (
        match $e.lexer.next() {
            x@&$p => x,
            x => return Err(format!("Unexpected token {}", x))
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
        IfElse(..) | Match(..) | Block(..) => true,
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
    fn statement(&mut self) -> ParseResult<(Expr<PString>, bool)> {
        match *self.lexer.peek() {
            TLet => {
                self.lexer.next();
                let id = match *expect!(self, TIdentifier(..)) {
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
                        if is_statement(&e) {
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

    fn expression(&mut self) -> ParseResult<Expr<PString>> {
        let e = try!(self.sub_expression());
        self.binary_expression(e, 0)
    }

    fn sub_expression(&mut self) -> ParseResult<Expr<PString>> {
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
                let mut exprs = Vec::new();
                loop {
                    let (expr, is_stm) = try!(self.statement());
                    exprs.push(expr);
                    if !is_stm {
                        break
                    }
                }
                expect!(self, TCloseBrace);
                Ok(Block(exprs))
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
            x => {
                self.lexer.backtrack();
                Err(format!("Token {} does not start an expression", x))
            }
        }
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::*;
    use std::io::BufReader;
    use interner::*;

    fn binop(l: Expr<InternedStr>, s: &str, r: Expr<InternedStr>) -> Expr<InternedStr> {
        BinOp(box l, intern(s), box r)
    }
    fn int(i: int) -> Expr<InternedStr> {
        Literal(Integer(i))
    }
    fn let_(s: &str, e: Expr<InternedStr>) -> Expr<InternedStr> {
        Let(intern(s), box e)
    }
    fn id(s: &str) -> Expr<InternedStr> {
        Identifier(intern(s))
    }

    #[test]
    fn operators() {
        let mut buffer = BufReader::new("1 / 4 + (2 - 3) * 2".as_bytes());
        let mut parser = Parser::new(&mut buffer);
        let expr = parser.expression()
            .unwrap_or_else(|err| fail!(err));
        assert_eq!(expr, binop(binop(int(1), "/", int(4)), "+", binop(binop(int(2), "-", int(3)), "*", int(2))));
    }
    #[test]
    fn block() {
        let mut buffer = BufReader::new("1 / { let x = 2; x }".as_bytes());
        let mut parser = Parser::new(&mut buffer);
        let expr = parser.expression()
            .unwrap_or_else(|err| fail!(err));
        assert_eq!(expr, binop(int(1), "/", Block(vec!(let_("x", int(2)), id("x")))));
    }
}
