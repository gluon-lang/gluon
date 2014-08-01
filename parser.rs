use lexer::*;
use ast::*;
use interner::InternedStr;

macro_rules! expect(
    ($e: expr, $p: pat) => (
        match $e.lexer.next() {
            x@&$p => x,
            _ => return Err(String::from_str("Expected other token"))
        }
    )
)

type PString = InternedStr;
type ParseResult<T> = Result<T, String>;

pub struct Parser<'a> {
    lexer: Lexer<'a>
}

impl <'a> Parser<'a> {
    pub fn new(input: &'a mut Buffer) -> Parser<'a> {
        Parser { lexer: Lexer::new(input) }
    }

    fn expression(&mut self) -> ParseResult<Expr<PString>> {
        match *self.lexer.next() {
            TIdentifier(id) => {
                Ok(Identifier(id))
            }
            TOpenParen => {
                let e = try!(self.expression());
                expect!(self, TCloseParen);
                Ok(e)
            }
            _ => Err(String::from_str("Not an expression"))
        }
    }
}
