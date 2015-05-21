use std::collections::VecDeque;
use std::io::{BufRead, Read};
use std::str::FromStr;
use std::fmt;

use base::ast::Location;
use base::gc::Gc;
use base::interner::{Interner, InternedStr};

use self::Token::*;

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum Token {
    TInteger(i64),
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
    TData,
    TTrait,
    TImpl,
    TVariable(InternedStr),
    TConstructor(InternedStr),
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
    TEOF,
    TError(&'static str)
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
    input: ::std::io::Chars<&'b mut (BufRead + 'b)>,
    buffer: String,
    peek_c: Option<char>,
    location: Location,
    tokens: VecDeque<Token>,
    offset: usize,
    interner: &'a mut Interner,
    gc: &'a mut Gc
}

impl <'a, 'b> Lexer<'a, 'b> {

    pub fn new(interner: &'a mut Interner, gc: &'a mut Gc, s: &'b mut BufRead) -> Lexer<'a, 'b> {
        let mut chars = s.chars();
        Lexer {
            peek_c: chars.next().and_then(|result| result.ok()),
            input: chars,
            buffer: String::new(),
            location: Location { row: 1, column: 1, absolute: 0 },
            tokens: VecDeque::with_capacity(20),
            offset: 0,
            interner: interner,
            gc: gc
        }
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn peek(&mut self) -> &Token {
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
    pub fn next(&mut self) -> &Token {
        if self.offset > 0 {
            self.offset -= 1;
        }
        else {
            let t = self.next_token();
            self.tokens.push_back(t);
            self.reset_str();
            debug!("Token {:?}", self.current());
        }
        self.current()
    }

    ///Returns a reference to the current token
    pub fn current(&self) -> &Token {
        &self.tokens[self.tokens.len() - self.offset - 1]
    }

    ///Moves the lexer back one token
    pub fn backtrack(&mut self) {
        self.offset += 1;
        if self.offset > self.tokens.len() {
            panic!("ICE:{} Backtracked outside the token buffer", self.location());
        }
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
                self.peek_c = self.input.next().and_then(|result| result.ok());
                self.location.absolute += 1;
                self.location.column += 1;
                if c == '\n' || c == '\r' {
                    self.location.column = 0;
                    self.location.row += 1;
                    //If this is a \n\r line ending skip the next char without increasing the location
                    if c == '\r' && self.peek_c == Some('\n') {
                        self.peek_c = self.input.next().and_then(|result| result.ok());
                    }
                }
            }
            None => ()
        }
        result
    }
    fn current_str(&self) -> &str {
        &self.buffer
    }

    pub fn intern(&mut self, s: &str) -> InternedStr {
        self.interner.intern(self.gc, s)
    }
    fn intern_current(&mut self) -> InternedStr {
        self.interner.intern(self.gc, &self.buffer)
    }

    ///Scans digits into a string
    fn scan_digits(&mut self) {
        loop {
            match self.peek_char() {
                Some(x) if x.is_digit(10) =>  {
                    self.read_char();
                }
                _ => break
            }
        }
    }
    ///Scans a number, float or integer and returns the appropriate token
    fn scan_number(&mut self) -> Token {
        self.scan_digits();
        let mut is_float = false;
        if self.peek_char() == Some('.') {
            self.read_char();
            is_float = true;
            self.scan_digits();
        }
        if is_float {
            TFloat(FromStr::from_str(self.current_str()).unwrap())
        }
        else {
            TInteger(FromStr::from_str(self.current_str()).unwrap())
        }
    }

    ///Scans an identifier or a keyword
    fn scan_identifier(&mut self) -> Token {
        loop {
            match self.peek_char() {
                Some(ch) if ch.is_alphanumeric() || ch == '_' => {
                    self.read_char();
                }
                _ => break
            }
        }
        match self.current_str() {
            "if" => TIf,
            "else" => TElse,
            "while" => TWhile,
            "for" => TFor,
            "match" => TMatch,
            "trait" => TTrait,
            "impl" => TImpl,
            "data" => TData,
            "let" => TLet,
            "true" => TTrue,
            "false" => TFalse,
            _ => {
                let s = self.intern_current();
                if s.chars().next().unwrap().is_uppercase() {
                    TConstructor(s)
                }
                else {
                    TVariable(s)
                }
            }
        }
    }
    
    ///Scans the character stream for the next token
    ///Return EOF token if the token stream has ehas ended
    fn next_token(&mut self) -> Token {
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
                    Some(ch) if is_operator(ch) => {
                        self.read_char();
                    }
                    _ => break
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
                        let contents = &self.buffer[1..self.buffer.len() - 1];
                        let s = self.interner.intern(self.gc, contents);
                        return TString(s)
                    }
                    Some(_) => (),
                    None => return TError("Unexpected EOF when lexing string literal")
                }
            }
        }
        else if c == '\'' {
            match self.read_char() {
                Some(x) => {
                    return if self.read_char() == Some('\'') {
                        TChar(x)
                    }
                    else {
                        TError("Attempted to lex a character literal with multiple characters")
                    }
                }
                None => return TError("Unexpected EOF when lexing char literal")
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
    use base::gc::Gc;
    use base::interner::Interner;
    use std::io::BufReader;

    #[test]
    fn lex() {
        let mut buffer = BufReader::new("main : () -> Int; main = { 1 + 2 }".as_bytes());
        let mut gc = Gc::new();
        let mut interner = Interner::new();
        let mut lexer = lexer::Lexer::new(&mut interner, &mut gc, &mut buffer);
        let plus = lexer.intern("+");
        let main = lexer.intern("main");
        let i = lexer.intern("Int");
        assert_eq!(lexer.next(), &TVariable(main));
        assert_eq!(lexer.next(), &TColon);
        assert_eq!(lexer.next(), &TOpenParen);
        assert_eq!(lexer.next(), &TCloseParen);
        assert_eq!(lexer.next(), &TRArrow);
        assert_eq!(lexer.next(), &TConstructor(i));
        assert_eq!(lexer.next(), &TSemicolon);
        assert_eq!(lexer.next(), &TVariable(main));
        assert_eq!(lexer.next(), &TAssign);
        assert_eq!(lexer.next(), &TOpenBrace);
        assert_eq!(lexer.next(), &TInteger(1));
        assert_eq!(lexer.next(), &TOperator(plus));
        assert_eq!(lexer.next(), &TInteger(2));
        assert_eq!(lexer.next(), &TCloseBrace);
    }
}
