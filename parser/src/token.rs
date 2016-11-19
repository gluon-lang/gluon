use std::fmt;

use base::pos::{Location, Spanned};

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Delimiter {
    Brace,
    Bracket,
    Paren,
}

impl Delimiter {
    fn as_str(&self) -> &'static str {
        use self::Delimiter::*;
        match *self {
            Brace => "Brace",
            Bracket => "Bracket",
            Paren => "Paren",
        }
    }
}

impl fmt::Display for Delimiter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Token<'input> {
    Identifier(&'input str),
    Operator(&'input str),
    String(String),
    Char(char),
    Int(i64),
    Byte(u8),
    Float(f64),
    DocComment(String),
    Let,
    And,
    In,
    Type,
    Match,
    With,
    If,
    Then,
    Else,
    Open(Delimiter),
    Close(Delimiter),
    Lambda,
    RightArrow,
    Colon,
    Dot,
    Comma,
    Pipe,
    Equals,
    OpenBlock,
    CloseBlock,
    Semi,
    EOF,
}

impl<'input> fmt::Display for Token<'input> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Token::*;
        use self::Delimiter::*;

        let s = match *self {
            Identifier(_) => "Identifier",
            Operator(_) => "Operator",
            String(_) => "String",
            Char(_) => "Char",
            Int(_) => "Int",
            Byte(_) => "Byte",
            Float(_) => "Float",
            DocComment(_) => "DocComment",
            Let => "Let",
            And => "And",
            In => "In",
            Type => "Type",
            Match => "Match",
            With => "With",
            If => "If",
            Then => "Then",
            Else => "Else",
            Open(Brace) => "OpenBrace",
            Close(Brace) => "CloseBrace",
            Open(Paren) => "OpenParen",
            Close(Paren) => "CloseParen",
            Open(Bracket) => "OpenBracket",
            Close(Bracket) => "CloseBracket",
            Lambda => "Lambda",
            RightArrow => "RightArrow",
            Colon => "Colon",
            Dot => "Dot",
            Comma => "Comma",
            Pipe => "Pipe",
            Equals => "Equal",
            OpenBlock => "OpenBlock",
            CloseBlock => "CloseBlock",
            Semi => "Semi",
            EOF => "EOF",
        };
        s.fmt(f)
    }
}

pub type SpannedToken<'input> = Spanned<Token<'input>, Location>;
