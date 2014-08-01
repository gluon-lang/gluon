use collections::RingBuf;
use std::from_str::FromStr;
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;

use interner::*;


#[deriving(PartialEq, Clone, Show)]
pub enum Token {
    TInteger(int),
    TFloat(f64),
    TString(InternedStr),
    TChar(char),
    TIf,
    TElse,
    TMatch,
    TFn,
    TIdentifier(InternedStr),
    TOpenBrace,
    TCloseBrace,
    TOpenParen,
    TCloseParen,
    TOpenBracket,
    TCloseBracket,
    TOperator(InternedStr),
    TSemicolon,
    TDot,
    TComma,
    TColon,
    TEOF
}

fn name_or_keyword(interner: &mut Interner, s: &str) -> Token {
    match s {
        "if" => TIf,
        "else" => TElse,
        "fn" => TFn,
        _ => TIdentifier(interner.intern(s)),
    }
}


#[deriving(Clone, PartialEq)]
pub struct Location {
    pub column : int,
    pub row : int,
    pub absolute : int
}

impl Location {
    pub fn eof() -> Location {
        Location { column: -1, row: -1, absolute: -1 }
    }
}

impl fmt::Show for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Line {}, Row {}", self.row, self.column)
    }
}

///Returns whether the character is a haskell operator
fn is_operator(first_char : char) -> bool {
    match first_char {
        '+' | '-' | '*' | '/' | '.' | '$' |
        ':' | '=' | '<' | '>' | '|' | '&' | '!' => true,
        _ => false
    }
}

pub struct Lexer<'a> {
    input: &'a mut Buffer,
    buffer: String,
    peek_c: Option<char>,
    location: Location,
    tokens: RingBuf<Token>,
    offset: uint,
    interner: Rc<RefCell<Interner>>
}

impl <'a> Lexer<'a> {

    pub fn new(s: &'a mut Buffer) -> Lexer<'a> {
        Lexer {
            peek_c: Some(s.read_char().unwrap()),
            input: s,
            buffer: String::new(),
            location: Location { row: 1, column: 1, absolute: 0 },
            tokens: RingBuf::with_capacity(20),
            offset: 0,
            interner: get_local_interner()
        }
    }

    pub fn peek<'b>(&'b mut self) -> &'b Token {
        if self.offset != 0 && self.tokens.len() != 0 {
            self.tokens.get(self.tokens.len() - self.offset + 1)
        }
        else {
            self.next();
            self.backtrack();
            self.tokens.get(self.tokens.len() - 1)
        }
    }
    
    ///Returns the next token in the lexer
    pub fn next<'b>(&'b mut self) -> &'b Token {
        let t = self.next_token();
        self.tokens.push(t);
        self.reset_str();
        debug!("Token {}", self.current());
        self.current()
    }

    ///Returns a reference to the current token
    pub fn current<'b>(&'b self) -> &'b Token {
        self.tokens.get(self.tokens.len() - self.offset - 1)
    }

    ///Moves the lexer back one token
    ///TODO check for overflow in the buffer
    pub fn backtrack(&mut self) {
        self.offset += 1;
    }

    ///Peeks at the next character in the input
    fn peek_char(&mut self) -> Option<char> {
        self.peek_c
    }

    fn reset_str(&mut self) {
        self.buffer.clear();
    }

    ///Reads a character from the input and increments the current position
    fn read_char(&mut self) -> Option<char> {
        let result = self.peek_c;
        match self.peek_c {
            Some(c) => {
                self.buffer.push_char(c);
                self.peek_c = match self.input.read_char() {
                    Ok(c) => Some(c),
                    Err(_) => None
                };
            }
            None => ()
        }
        result
    }

    fn current_str<'b>(&'b self) -> &'b str {
        self.buffer.as_slice()
    }

    fn intern(&self, s: &str) -> InternedStr {
        (*self.interner.borrow_mut()).intern(s)
    }

    ///Scans digits into a string
    fn scan_digits(&mut self) {
        loop {
            match self.peek_char() {
                Some(x) => {
                    if !x.is_digit() {
                        break;
                    }
                    self.read_char();
                }
                None => break
            }
        }
    }
    ///Scans a number, float or integer and returns the appropriate token
    fn scan_number<'b>(&'b mut self) -> Token {
        self.scan_digits();
        let mut is_float = false;
        match self.peek_char() {
            Some('.') => {
                self.read_char();
                is_float = true;
                self.scan_digits();
            }
            _ => ()
        }
        if is_float {
            TFloat(FromStr::from_str(self.current_str()).unwrap())
        }
        else {
            TInteger(FromStr::from_str(self.current_str()).unwrap())
        }
    }

    ///Scans an identifier or a keyword
    fn scan_identifier<'b>(&'b mut self) -> Token {
        loop {
            match self.peek_char() {
                Some(ch) => {
                    if !ch.is_alphanumeric() && ch != '_' {
                        break;
                    }
                    self.read_char();
                }
                None => break
            }
        }
        name_or_keyword(&mut *self.interner.borrow_mut(), self.current_str())
    }
    
    ///Scans the character stream for the next token
    ///Return EOF token if the token stream has ehas ended
    fn next_token<'b>(&'b mut self) -> Token {
        let mut c = ' ';
        //Skip all whitespace before the token
        while c.is_whitespace() {
            self.reset_str();
            match self.read_char() {
                Some(x) => {
                    c = x;
                }
                None => { return TEOF }
            }
        }

        //Decide how to tokenize depending on what the first char is
        //ie if its an operator then more operators will follow
        if is_operator(c) {
            loop {
                match self.peek_char() {
                    Some(ch) => {
                        if !is_operator(ch) {
                            break;
                        }
                        self.read_char();
                    }
                    None => { break; }
                }
            }
            return TOperator(self.intern(self.current_str()));
        }
        else if c.is_digit() {
            return self.scan_number();
        }
        else if c.is_alphabetic() || c == '_' {
            return self.scan_identifier();
        }
        else if c == '"' {
            loop {
                match self.read_char() {
                    Some('"') => return TString(self.intern(self.current_str())),
                    Some(x) => (),
                    None => fail!("Unexpected EOF")
                }
            }
        }
        else if c == '\'' {
            match self.read_char() {
                Some(x) => {
                    if self.read_char() == Some('\'') {
                        return TChar(x);
                    }
                    else {
                        fail!("Multi char character")
                    }
                }
                None => fail!("Unexpected EOF")
            }
        }
        else {
            match c {
                ';' => TSemicolon,
                '(' => TOpenParen,
                ')' => TCloseParen,
                '[' => TOpenBracket,
                ']' => TCloseBracket,
                '{' => TOpenBrace,
                '}' => TCloseBrace,
                ',' => TComma,
                _   => TEOF
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use interner::intern;
    use std::io::BufReader;

    fn buffer<'a>(s: &'a str) -> BufReader<'a> {
        BufReader::new(s.as_bytes())
    }

    #[test]
    fn lex() {
        let mut buffer = buffer("fn main() { 1 + 2 }");
        let mut lexer = Lexer::new(&mut buffer);
        assert_eq!(lexer.next(), &TFn);
        assert_eq!(lexer.next(), &TIdentifier(intern("main")));
        assert_eq!(lexer.next(), &TOpenParen);
        assert_eq!(lexer.next(), &TCloseParen);
        assert_eq!(lexer.next(), &TOpenBrace);
        assert_eq!(lexer.next(), &TInteger(1));
        assert_eq!(lexer.next(), &TOperator(intern("+")));
        assert_eq!(lexer.next(), &TInteger(2));
        assert_eq!(lexer.next(), &TCloseBrace);
    }
}
