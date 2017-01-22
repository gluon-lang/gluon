use base::ast::is_operator_char;
use base::pos::{self, BytePos, Column, Line, Location, Spanned};
use std::error::Error as StdError;
use std::fmt;
use std::str::Chars;

use self::ErrorCode::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Token<'input> {
    Identifier(&'input str),
    Operator(&'input str),

    StringLiteral(String),
    CharLiteral(char),
    IntLiteral(i64),
    ByteLiteral(u8),
    FloatLiteral(f64),
    DocComment(String),

    And,
    Else,
    If,
    In,
    Let,
    Match,
    Then,
    Type,
    With,

    Colon,
    Comma,
    Dot,
    Equals,
    Lambda,
    Pipe,
    RArrow,

    LBrace,
    LBracket,
    LParen,
    RBrace,
    RBracket,
    RParen,

    OpenBlock,
    CloseBlock,
    Semi,

    EOF, // Required for the layout algorithm
}

impl<'input> fmt::Display for Token<'input> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Token::*;

        let s = match *self {
            Identifier(_) => "Identifier",
            Operator(_) => "Operator",
            StringLiteral(_) => "StringLiteral",
            CharLiteral(_) => "CharLiteral",
            IntLiteral(_) => "IntLiteral",
            ByteLiteral(_) => "ByteLiteral",
            FloatLiteral(_) => "FloatLiteral",
            DocComment(_) => "DocComment",

            And => "And",
            Else => "Else",
            If => "If",
            In => "In",
            Let => "Let",
            Match => "Match",
            Then => "Then",
            Type => "Type",
            With => "With",

            LBrace => "LBrace",
            LBracket => "LBracket",
            LParen => "LParen",

            RBrace => "RBrace",
            RBracket => "RBracket",
            RParen => "RParen",

            Colon => "Colon",
            Comma => "Comma",
            Dot => "Dot",
            Equals => "Equal",
            Lambda => "Lambda",
            Pipe => "Pipe",
            RArrow => "RArrow",

            OpenBlock => "OpenBlock",
            CloseBlock => "CloseBlock",
            Semi => "Semi",

            EOF => "EOF",
        };
        s.fmt(f)
    }
}

pub type SpannedToken<'input> = Spanned<Token<'input>, Location>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub location: Location,
    pub code: ErrorCode,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.description()) // TODO: Improve
    }
}

impl StdError for Error {
    fn description(&self) -> &str {
        self.code.description()
    }
}

quick_error! {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum ErrorCode {
        EmptyCharLiteral {
            description("empty char literal")
        }
        UnexpectedChar(ch: char) {
            description("unexpected character")
        }
        UnexpectedEof {
            description("unexpected end of file")
        }
        UnexpectedEscapeCode(ch: char) {
            description("unexpected escape code")
        }
        UnterminatedCharLiteral {
            description("unterminated character literal")
        }
        UnterminatedStringLiteral {
            description("unterminated string literal")
        }
        NonParseableInt {
            description("cannot parse integer, probable overflow")
        }
    }
}

fn error<T>(location: Location, code: ErrorCode) -> Result<T, Error> {
    Err(Error {
        location: location,
        code: code,
    })
}

fn is_ident_start(ch: char) -> bool {
    // TODO: Unicode?
    match ch {
        '_' | 'a'...'z' | 'A'...'Z' => true,
        _ => false,
    }
}

fn is_ident_continue(ch: char) -> bool {
    // TODO: Unicode?
    match ch {
        '0'...'9' | '\'' => true,
        ch => is_ident_start(ch),
    }
}

fn is_digit(ch: char) -> bool {
    ch.is_digit(10)
}

struct CharLocations<'input> {
    location: Location,
    chars: Chars<'input>,
}

impl<'input> CharLocations<'input> {
    pub fn new(input: &'input str) -> CharLocations<'input> {
        CharLocations {
            location: Location {
                line: Line::from(0),
                column: Column::from(1),
                absolute: BytePos::from(0),
            },
            chars: input.chars(),
        }
    }
}

impl<'input> Iterator for CharLocations<'input> {
    type Item = (Location, char);

    fn next(&mut self) -> Option<(Location, char)> {
        self.chars.next().map(|ch| {
            let location = self.location;
            self.location = self.location.shift(ch);
            // HACK: The layout algorithm expects `1` indexing for columns -
            // this could be altered in the future though
            if self.location.column == Column::from(0) {
                self.location.column = Column::from(1);
            }
            (location, ch)
        })
    }
}

pub struct Tokenizer<'input> {
    input: &'input str,
    chars: CharLocations<'input>,
    eof_location: Location,
    lookahead: Option<(Location, char)>,
}

impl<'input> Tokenizer<'input> {
    pub fn new(input: &'input str) -> Tokenizer<'input> {
        let mut chars = CharLocations::new(input);
        let eof_location = chars.location;

        Tokenizer {
            input: input,
            eof_location: eof_location,
            lookahead: chars.next(),
            chars: chars,
        }
    }

    fn bump(&mut self) -> Option<(Location, char)> {
        match self.lookahead {
            Some((location, ch)) => {
                self.eof_location = self.eof_location.shift(ch);
                self.lookahead = self.chars.next();
                Some((location, ch))
            }
            None => None,
        }
    }

    fn skip_to_end(&mut self) {
        while let Some(_) = self.bump() {}
    }

    fn error<T>(&mut self, location: Location, code: ErrorCode) -> Result<T, Error> {
        self.skip_to_end();
        error(location, code)
    }

    fn eof_error<T>(&mut self) -> Result<T, Error> {
        let location = self.eof_location;
        self.error(location, UnexpectedEof)
    }

    fn slice(&self, start: Location, end: Location) -> &'input str {
        let start = start.absolute;
        let end = end.absolute;

        &self.input[start.to_usize()..end.to_usize()]
    }

    fn take_while<F>(&mut self, start: Location, mut keep_going: F) -> (Location, &'input str)
        where F: FnMut(char) -> bool,
    {
        self.take_until(start, |c| !keep_going(c))
    }

    fn take_until<F>(&mut self, start: Location, mut terminate: F) -> (Location, &'input str)
        where F: FnMut(char) -> bool,
    {
        while let Some((end, ch)) = self.lookahead {
            if terminate(ch) {
                return (end, self.slice(start, end));
            } else {
                self.bump();
            }
        }
        (self.eof_location, self.slice(start, self.eof_location))
    }

    fn test_lookahead<F>(&self, mut test: F) -> bool
        where F: FnMut(char) -> bool,
    {
        self.lookahead.map_or(false, |(_, ch)| test(ch))
    }

    fn line_comment(&mut self, start: Location) -> Option<SpannedToken<'input>> {
        let (end, comment) = self.take_until(start, |ch| ch == '\n');

        if comment.starts_with("///") {
            let skip = if comment.starts_with("/// ") { 4 } else { 3 };
            let doc = Token::DocComment(comment[skip..].to_string());
            Some(pos::spanned2(start, end, doc))
        } else {
            None
        }
    }

    fn block_comment(&mut self, start: Location) -> Result<Option<SpannedToken<'input>>, Error> {
        self.bump(); // Skip first '*'

        loop {
            let (_, comment) = self.take_until(start, |ch| ch == '*');
            self.bump(); // Skip next '*'
            match self.lookahead {
                Some((end, '/')) => {
                    self.bump();
                    if comment.starts_with("/**") && comment != "/**" {
                        // FIXME: whitespace alignment
                        let doc = Token::DocComment(comment[3..].trim_left().to_string());
                        return Ok(Some(pos::spanned2(start, end.shift('/'), doc)));
                    } else {
                        return Ok(None);
                    }
                }
                Some((_, _)) => continue,
                None => return self.eof_error(),
            }
        }
    }

    fn operator(&mut self, start: Location) -> SpannedToken<'input> {
        let (end, op) = self.take_while(start, is_operator_char);

        let token = match op {
            "." => Token::Dot,
            ":" => Token::Colon,
            "=" => Token::Equals,
            "|" => Token::Pipe,
            "->" => Token::RArrow,
            "#" => {
                // Is this too permissive?
                self.take_while(start, is_ident_start);
                let (_, op) = self.take_while(start, is_operator_char);
                Token::Operator(op)
            }
            op => Token::Operator(op),
        };

        pos::spanned2(start, end, token)
    }

    fn escape_code(&mut self) -> Result<char, Error> {
        match self.bump() {
            Some((_, '\'')) => Ok('\''),
            Some((_, '"')) => Ok('"'),
            Some((_, '\\')) => Ok('\\'),
            Some((_, '/')) => Ok('/'),
            Some((_, 'n')) => Ok('\n'),
            Some((_, 'r')) => Ok('\r'),
            Some((_, 't')) => Ok('\t'),
            // TODO: Unicode escape codes
            Some((start, ch)) => self.error(start, UnexpectedEscapeCode(ch)),
            None => return self.eof_error(),
        }
    }

    fn string_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, Error> {
        let mut string = String::new();

        while let Some((next, ch)) = self.bump() {
            match ch {
                '\\' => string.push(self.escape_code()?),
                '"' => {
                    let end = next.shift(ch);
                    let token = Token::StringLiteral(string);
                    return Ok(pos::spanned2(start, end, token));
                }
                ch => string.push(ch),
            }
        }

        self.error(start, UnterminatedStringLiteral)
    }

    fn char_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, Error> {
        let ch = match self.bump() {
            Some((_, '\\')) => self.escape_code()?,
            Some((_, '\'')) => return self.error(start, EmptyCharLiteral),
            Some((_, ch)) => ch,
            None => return self.eof_error(),
        };

        match self.bump() {
            Some((end, '\'')) => Ok(pos::spanned2(start, end.shift('\''), Token::CharLiteral(ch))),
            Some((_, _)) => self.error(start, UnterminatedCharLiteral), // UnexpectedEscapeCode?
            None => self.eof_error(),
        }
    }

    fn numeric_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, Error> {
        let (end, int) = self.take_while(start, is_digit);

        let (start, end, token) = match self.lookahead {
            Some((_, '.')) => {
                self.bump(); // Skip '.'
                let (end, float) = self.take_while(start, is_digit);
                (start, end, Token::FloatLiteral(float.parse().unwrap()))
            }
            Some((end, 'b')) => {
                self.bump(); // Skip 'b'
                if let Ok(val) = int.parse() {
                    (start, end.shift('b'), Token::ByteLiteral(val))
                }
                else {
                    return self.error(start, NonParseableInt);
                }
            }
            Some((start, ch)) if is_ident_start(ch) => return self.error(start, UnexpectedChar(ch)),
            None | Some(_) => {
                if let Ok(val) = int.parse() {
                    (start, end, Token::IntLiteral(val))
                }
                else {
                    return self.error(start, NonParseableInt);
                }
            }
        };

        Ok(pos::spanned2(start, end, token))
    }

    fn identifier(&mut self, start: Location) -> SpannedToken<'input> {
        let (end, ident) = self.take_while(start, is_ident_continue);

        let token = match ident {
            "and" => Token::And,
            "else" => Token::Else,
            "if" => Token::If,
            "in" => Token::In,
            "let" => Token::Let,
            "match" => Token::Match,
            "then" => Token::Then,
            "type" => Token::Type,
            "with" => Token::With,
            src => Token::Identifier(src),
        };

        pos::spanned2(start, end, token)
    }
}

impl<'input> Iterator for Tokenizer<'input> {
    type Item = Result<SpannedToken<'input>, Error>;

    fn next(&mut self) -> Option<Result<SpannedToken<'input>, Error>> {
        while let Some((start, ch)) = self.bump() {
            return match ch {
                ',' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::Comma))),
                '\\' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::Lambda))),
                '{' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::LBrace))),
                '[' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::LBracket))),
                '(' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::LParen))),
                '}' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::RBrace))),
                ']' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::RBracket))),
                ')' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::RParen))),

                '"' => Some(self.string_literal(start)),
                '\'' => Some(self.char_literal(start)),

                '/' if self.test_lookahead(|ch| ch == '/') => {
                    match self.line_comment(start) {
                        Some(token) => Some(Ok(token)),
                        None => continue,
                    }
                }
                '/' if self.test_lookahead(|ch| ch == '*') => {
                    match self.block_comment(start) {
                        Ok(Some(token)) => Some(Ok(token)),
                        Ok(None) => continue,
                        Err(err) => Some(Err(err)),
                    }
                }

                ch if is_ident_start(ch) => Some(Ok(self.identifier(start))),
                ch if is_digit(ch) => Some(self.numeric_literal(start)), // TODO: negative numbers?
                ch if is_operator_char(ch) => Some(Ok(self.operator(start))),
                ch if ch.is_whitespace() => continue,

                ch => Some(self.error(start, UnexpectedChar(ch))),
            };
        }
        None
    }
}


#[cfg(test)]
mod test {
    use base::pos::{self, BytePos, Column, Line, Location};

    use super::{Tokenizer, error};
    use super::ErrorCode::*;
    use token::Token;
    use token::Token::*;

    fn loc(byte: usize) -> Location {
        Location {
            line: Line::from(0),
            column: Column::from(byte + 1),
            absolute: BytePos::from(byte),
        }
    }

    fn test(input: &str, expected: Vec<(&str, Token)>) {
        let tokenizer = Tokenizer::new(input);
        let len = expected.len();

        for (token, (expected_span, expected_tok)) in tokenizer.zip(expected.into_iter()) {
            println!("{:?}", token);
            let start = loc(expected_span.find("~").unwrap());
            let end = loc(expected_span.rfind("~").unwrap() + 1);
            assert_eq!(Ok(pos::spanned2(start, end, expected_tok)), token);
        }

        // Make sure that there is nothing else to consume
        let tokenizer = Tokenizer::new(input);
        assert_eq!(None, tokenizer.skip(len).next());
    }

    #[test]
    fn sample_lambda_expr() {
        test(r#"(hi_, \a -> a ** a)"#,
             vec![
            (r#"~                  "#, LParen),
            (r#" ~~~               "#, Identifier("hi_")),
            (r#"    ~              "#, Comma),
            (r#"      ~            "#, Lambda),
            (r#"       ~           "#, Identifier("a")),
            (r#"         ~~        "#, RArrow),
            (r#"            ~      "#, Identifier("a")),
            (r#"              ~~   "#, Operator("**")),
            (r#"                 ~ "#, Identifier("a")),
            (r#"                  ~"#, RParen),
        ]);
    }

    #[test]
    fn sample_array() {
        test(r#"[1, a]"#,
             vec![
            (r#"~     "#, LBracket),
            (r#" ~    "#, IntLiteral(1)),
            (r#"  ~   "#, Comma),
            (r#"    ~ "#, Identifier("a")),
            (r#"     ~"#, RBracket),
        ]);
    }

    #[test]
    fn builtin_operators() {
        test(r#". : = | ->"#,
             vec![
            (r#"~         "#, Dot),
            (r#"  ~       "#, Colon),
            (r#"    ~     "#, Equals),
            (r#"      ~   "#, Pipe),
            (r#"        ~~"#, RArrow),
        ]);
    }

    #[test]
    fn user_defined_operators() {
        test(r#"+-* * /&|=<>: .. <->"#,
             vec![
            (r#"~~~                 "#, Operator("+-*")), // Horiffic!
            (r#"    ~               "#, Operator("*")),
            (r#"      ~~~~~~~       "#, Operator("/&|=<>:")), // Oh my...
            (r#"              ~~    "#, Operator("..")),
            (r#"                 ~~~"#, Operator("<->")),
        ]);
    }

    #[test]
    fn delimters() {
        test(r#"{][ () }] "#,
             vec![
            (r#"~         "#, LBrace),
            (r#" ~        "#, RBracket),
            (r#"  ~       "#, LBracket),
            (r#"    ~     "#, LParen),
            (r#"     ~    "#, RParen),
            (r#"       ~  "#, RBrace),
            (r#"        ~ "#, RBracket),
        ]);
    }

    #[test]
    fn string_literals() {
        test(r#"foo "bar\"\n" baz "" "\t""#,
             vec![
            (r#"~~~                      "#, Identifier("foo")),
            (r#"    ~~~~~~~~~            "#, StringLiteral("bar\"\n".to_string())),
            (r#"              ~~~        "#, Identifier("baz")),
            (r#"                  ~~     "#, StringLiteral("".to_string())),
            (r#"                     ~~~~"#, StringLiteral("\t".to_string())),
        ]);
    }

    #[test]
    fn string_literal_unexpected_escape_code() {
        assert_eq!(Tokenizer::new(r#""\X""#).last(),
                   Some(error(loc(2), UnexpectedEscapeCode('X'))));
    }

    #[test]
    fn string_literal_unterminated() {
        assert_eq!(Tokenizer::new(r#"foo "bar\"\n baz"#).last(),
                   Some(error(loc(4), UnterminatedStringLiteral)));
    }

    #[test]
    fn char_literals() {
        test(r#"foo 'b' '\\' '\''"#,
             vec![
            (r#"~~~              "#, Identifier("foo")),
            (r#"    ~~~          "#, CharLiteral('b')),
            (r#"        ~~~~     "#, CharLiteral('\\')),
            (r#"             ~~~~"#, CharLiteral('\'')),
        ]);
    }

    #[test]
    fn char_literal_empty() {
        assert_eq!(Tokenizer::new(r#"foo ''"#).last(),
                   Some(error(loc(4), EmptyCharLiteral)));
    }

    #[test]
    fn char_literal_unexpected_escape_code() {
        assert_eq!(Tokenizer::new(r#"'\X'"#).last(),
                   Some(error(loc(2), UnexpectedEscapeCode('X'))));
    }

    #[test]
    fn char_literal_unexpected_eof() {
        assert_eq!(Tokenizer::new(r#"'"#).last(),
                   Some(error(loc(1), UnexpectedEof)));
        assert_eq!(Tokenizer::new(r#"  '"#).last(),
                   Some(error(loc(3), UnexpectedEof)));
        assert_eq!(Tokenizer::new(r#"'b"#).last(),
                   Some(error(loc(2), UnexpectedEof)));
        assert_eq!(Tokenizer::new(r#"'\\"#).last(),
                   Some(error(loc(3), UnexpectedEof)));
        assert_eq!(Tokenizer::new(r#"'\'"#).last(),
                   Some(error(loc(3), UnexpectedEof)));
    }

    #[test]
    fn char_literal_unterminated() {
        assert_eq!(Tokenizer::new(r#"'frooble'"#).last(),
                   Some(error(loc(0), UnterminatedCharLiteral)));
    }

    #[test]
    fn int_literals() {
        test(r#"3 1036 45"#,
             vec![
            (r#"~        "#, IntLiteral(3)),
            (r#"  ~~~~   "#, IntLiteral(1036)),
            (r#"       ~~"#, IntLiteral(45)),
        ]);
    }

    #[test]
    fn int_literal_overflow() {
        assert_eq!(Tokenizer::new(r#"12345678901234567890"#).last(),
                   Some(error(loc(0), NonParseableInt)));
    }

    #[test]
    fn byte_literals() {
        test(r#"3b 255b 45b"#,
             vec![
            (r#"~~         "#, ByteLiteral(3)),
            (r#"   ~~~~    "#, ByteLiteral(255)),
            (r#"        ~~~"#, ByteLiteral(45)),
        ]);
    }

    #[test]
    fn float_literals() {
        test(r#"03.1415 1036.2"#,
             vec![
            (r#"~~~~~~~       "#, FloatLiteral(3.1415)),
            (r#"        ~~~~~~"#, FloatLiteral(1036.2)),
        ]);
    }

    #[test]
    fn line_comments() {
        test(r#"hi // hellooo"#,
             vec![
            (r#"~~           "#, Identifier("hi")),
        ]);
    }

    #[test]
    fn line_doc_comments() {
        test(r#"hi ///hellooo/// hi"#,
             vec![
            (r#"~~                  "#, Identifier("hi")),
            (r#"   ~~~~~~~~~~~~~~~~~"#, DocComment("hellooo/// hi".to_string())),
        ]);
    }

    #[test]
    fn line_doc_comments_with_space() {
        test(r#"hi /// hellooo/// hi"#,
             vec![
            (r#"~~                  "#, Identifier("hi")),
            (r#"   ~~~~~~~~~~~~~~~~~"#, DocComment("hellooo/// hi".to_string())),
        ]);
    }
}
