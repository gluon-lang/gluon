use collections::RingBuf;
use std::str::FromStr;
use std::fmt;

use interner::{Interner, InternedStr};

use self::Token::*;

#[deriving(PartialEq, Clone, Show)]
pub enum Token {
    TInteger(int),
    TFloat(f64),
    TString(InternedStr),
    TChar(char),
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
    TLet,
    TAssign,
    TRArrow,
    TMatchArrow,
    TLambda,
    TEOF
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

pub struct Lexer<'a, 'b> {
    input: &'b mut Buffer + 'b,
    buffer: String,
    peek_c: Option<char>,
    location: Location,
    tokens: RingBuf<Token>,
    offset: uint,
    pub interner: &'a mut Interner
}

impl <'a, 'b> Lexer<'a, 'b> {

    pub fn new(interner: &'a mut Interner, s: &'b mut Buffer) -> Lexer<'a, 'b> {
        Lexer {
            peek_c: Some(s.read_char().unwrap()),
            input: s,
            buffer: String::new(),
            location: Location { row: 1, column: 1, absolute: 0 },
            tokens: RingBuf::with_capacity(20),
            offset: 0,
            interner: interner
        }
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn peek<'b>(&'b mut self) -> &'b Token {
        if self.offset != 0 && self.tokens.len() != 0 {
            &self.tokens[self.tokens.len() - self.offset]
        }
        else {
            self.next();
            self.backtrack();
            &self.tokens[self.tokens.len() - 1]
        }
    }
    
    ///Returns the next token in the lexer
    pub fn next<'b>(&'b mut self) -> &'b Token {
        if self.offset > 0 {
            self.offset -= 1;
        }
        else {
            let t = self.next_token();
            self.tokens.push(t);
            self.reset_str();
            debug!("Token {}", self.current());
        }
        self.current()
    }

    ///Returns a reference to the current token
    pub fn current<'b>(&'b self) -> &'b Token {
        &self.tokens[self.tokens.len() - self.offset - 1]
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
                self.buffer.push(c);
                self.peek_c = match self.input.read_char() {
                    Ok(c) => Some(c),
                    Err(_) => None
                };
                self.location.absolute += 1;
                self.location.column += 1;
                if c == '\n' || c == '\r' {
                    self.location.column = 0;
                    self.location.row += 1;
                    //If this is a \n\r line ending skip the next char without increasing the location
                    if c == '\r' && self.peek_c == Some('\n') {
                        self.peek_c = self.input.read_char().ok();
                    }
                }
            }
            None => ()
        }
        result
    }

    fn current_str<'b>(&'b self) -> &'b str {
        self.buffer.as_slice()
    }

    fn intern_current(&mut self) -> InternedStr {
        self.interner.intern(self.buffer.as_slice())
    }

    ///Scans digits into a string
    fn scan_digits(&mut self) {
        loop {
            match self.peek_char() {
                Some(x) => {
                    if !x.is_digit(10) {
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
        match self.current_str() {
            "if" => TIf,
            "else" => TElse,
            "while" => TWhile,
            "for" => TFor,
            "match" => TMatch,
            "fn" => TFn,
            "struct" => TStruct,
            "trait" => TTrait,
            "impl" => TImpl,
            "enum" => TEnum,
            "let" => TLet,
            "true" => TTrue,
            "false" => TFalse,
            _ => TIdentifier(self.intern_current()),
        }
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
            return match self.current_str() {
                "=" => TAssign,
                ":" => TColon,
                "->" => TRArrow,
                "." => TDot,
                "=>" => TMatchArrow,
                _ => TOperator(self.intern_current())
            }
        }
        else if c.is_digit(10) {
            return self.scan_number();
        }
        else if c.is_alphabetic() || c == '_' {
            return self.scan_identifier();
        }
        else if c == '"' {
            loop {
                match self.read_char() {
                    Some('"') => {
                        //Drop the '"' at the start and end
                        let contents = self.buffer
                            .as_slice()
                            .slice_to(self.buffer.len() - 1)
                            .slice_from(1);
                        let s = self.interner.intern(contents);
                        return TString(s)
                    }
                    Some(_) => (),
                    None => panic!("Unexpected EOF")
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
                        panic!("Multi char character")
                    }
                }
                None => panic!("Unexpected EOF")
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
                '\\' => TLambda,
                _   => TEOF
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use lexer;
    use lexer::Token::*;
    use super::*;
    use interner::Interner;
    use std::io::BufReader;

    fn buffer<'a>(s: &'a str) -> BufReader<'a> {
        BufReader::new(s.as_bytes())
    }

    #[test]
    fn lex() {
        let mut buffer = buffer("fn main() { 1 + 2 }");
        let mut interner = Interner::new();
        let mut lexer = lexer::Lexer::new(&mut interner, &mut buffer);
        let plus = lexer.interner.intern("+");
        let main = lexer.interner.intern("main");
        assert_eq!(lexer.next(), &TFn);
        assert_eq!(lexer.next(), &TIdentifier(main));
        assert_eq!(lexer.next(), &TOpenParen);
        assert_eq!(lexer.next(), &TCloseParen);
        assert_eq!(lexer.next(), &TOpenBrace);
        assert_eq!(lexer.next(), &TInteger(1));
        assert_eq!(lexer.next(), &TOperator(plus));
        assert_eq!(lexer.next(), &TInteger(2));
        assert_eq!(lexer.next(), &TCloseBrace);
    }
}
