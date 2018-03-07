use base::ast::{is_operator_char, Comment, CommentType};
use base::pos::{self, BytePos, Column, Line, Location, Spanned};
use std::fmt;
use std::str::Chars;

use self::Error::*;

#[derive(Clone, PartialEq, Debug)]
pub enum Token<'input> {
    ShebangLine(&'input str),
    Identifier(&'input str),
    Operator(&'input str),

    StringLiteral(String),
    CharLiteral(char),
    IntLiteral(i64),
    ByteLiteral(u8),
    FloatLiteral(f64),
    DocComment(Comment),

    And,
    Else,
    Forall,
    If,
    In,
    Let,
    Do,
    Match,
    Then,
    Type,
    With,

    At,
    Colon,
    Comma,
    Dot,
    DotDot,
    Equals,
    Lambda,
    Pipe,
    RArrow,
    Question,

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
            ShebangLine(_) => "ShebangLine",
            Identifier(_) => "Identifier",
            Operator(_) => "Operator",
            StringLiteral(_) => "StringLiteral",
            CharLiteral(_) => "CharLiteral",
            IntLiteral(_) => "IntLiteral",
            ByteLiteral(_) => "ByteLiteral",
            FloatLiteral(_) => "FloatLiteral",
            DocComment { .. } => "DocComment",

            And => "And",
            Else => "Else",
            Forall => "Forall",
            If => "If",
            In => "In",
            Let => "Let",
            Do => "Do",
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

            At => "At",
            Colon => "Colon",
            Comma => "Comma",
            Dot => "Dot",
            DotDot => "DotDot",
            Equals => "Equal",
            Lambda => "Lambda",
            Pipe => "Pipe",
            RArrow => "RArrow",
            Question => "Question",

            OpenBlock => "OpenBlock",
            CloseBlock => "CloseBlock",
            Semi => "Semi",

            EOF => "EOF",
        };
        s.fmt(f)
    }
}

impl<'input> Token<'input> {
    pub fn is_doc_comment(&self) -> bool {
        match *self {
            Token::DocComment(_) => true,
            _ => false,
        }
    }
}

pub type SpannedToken<'input> = Spanned<Token<'input>, Location>;

pub type SpError = Spanned<Error, Location>;

quick_error! {
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum Error {
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
        HexLiteralOverflow {
            description("cannot parse hex literal, overflow")
        }
        HexLiteralUnderflow {
            description("cannot parse hex literal, underflow")
        }
        HexLiteralWrongPrefix {
            description("wrong hex literal prefix, should start as '0x' or '-0x'")
        }
        HexLiteralIncomplete {
            description("cannot parse hex literal, incomplete")
        }
    }
}

fn error<T>(location: Location, code: Error) -> Result<T, SpError> {
    Err(pos::spanned2(location, location, code))
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

fn is_hex(ch: char) -> bool {
    ch.is_digit(16)
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

    fn error<T>(&mut self, location: Location, code: Error) -> Result<T, SpError> {
        self.skip_to_end();
        error(location, code)
    }

    fn eof_error<T>(&mut self) -> Result<T, SpError> {
        let location = self.eof_location;
        self.error(location, UnexpectedEof)
    }

    fn slice(&self, start: Location, end: Location) -> &'input str {
        let start = start.absolute;
        let end = end.absolute;

        &self.input[start.to_usize()..end.to_usize()]
    }

    fn take_while<F>(&mut self, start: Location, mut keep_going: F) -> (Location, &'input str)
    where
        F: FnMut(char) -> bool,
    {
        self.take_until(start, |c| !keep_going(c))
    }

    fn take_until<F>(&mut self, start: Location, mut terminate: F) -> (Location, &'input str)
    where
        F: FnMut(char) -> bool,
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
    where
        F: FnMut(char) -> bool,
    {
        self.lookahead.map_or(false, |(_, ch)| test(ch))
    }

    fn line_comment(&mut self, start: Location) -> Option<SpannedToken<'input>> {
        let (end, comment) = self.take_until(start, |ch| ch == '\n');

        if comment.starts_with("///") {
            let skip = if comment.starts_with("/// ") { 4 } else { 3 };
            let doc = Token::DocComment(Comment {
                typ: CommentType::Line,
                content: comment[skip..].to_string(),
            });
            Some(pos::spanned2(start, end, doc))
        } else {
            None
        }
    }

    fn block_comment(&mut self, start: Location) -> Result<Option<SpannedToken<'input>>, SpError> {
        self.bump(); // Skip first '*'

        loop {
            let (_, comment) = self.take_until(start, |ch| ch == '*');
            self.bump(); // Skip next '*'
            match self.lookahead {
                Some((end, '/')) => {
                    self.bump();
                    if comment.starts_with("/**") && comment != "/**" {
                        // FIXME: whitespace alignment
                        let doc = Token::DocComment(Comment {
                            typ: CommentType::Block,
                            content: comment[3..].trim().to_string(),
                        });
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
            "@" => Token::At,
            "." => Token::Dot,
            ".." => Token::DotDot,
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

    fn escape_code(&mut self) -> Result<char, SpError> {
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
            None => self.eof_error(),
        }
    }

    fn string_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, SpError> {
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

    fn shebang_line(&mut self, start: Location) -> Option<SpannedToken<'input>> {
        let (end, line) = self.take_until(start, |ch| ch == '\n');

        if line.starts_with("#!") {
            let skip = 2;
            let result = line[skip..].trim_right();
            let tok = Token::ShebangLine(result);
            Some(pos::spanned2(start, end, tok))
        } else {
            None
        }
    }

    fn char_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, SpError> {
        let ch = match self.bump() {
            Some((_, '\\')) => self.escape_code()?,
            Some((_, '\'')) => return self.error(start, EmptyCharLiteral),
            Some((_, ch)) => ch,
            None => return self.eof_error(),
        };

        match self.bump() {
            Some((end, '\'')) => Ok(pos::spanned2(
                start,
                end.shift('\''),
                Token::CharLiteral(ch),
            )),
            Some((_, _)) => self.error(start, UnterminatedCharLiteral), // UnexpectedEscapeCode?
            None => self.eof_error(),
        }
    }

    fn numeric_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, SpError> {
        let (end, int) = self.take_while(start, is_digit);

        let (start, end, token) = match self.lookahead {
            Some((_, '.')) => {
                self.bump(); // Skip '.'
                let (end, float) = self.take_while(start, is_digit);
                match self.lookahead {
                    Some((_, ch)) if is_ident_start(ch) => {
                        return self.error(end, UnexpectedChar(ch))
                    }
                    _ => (start, end, Token::FloatLiteral(float.parse().unwrap())),
                }
            }
            Some((end, 'x')) => {
                self.bump(); // Skip 'x'
                let (end, hex) = self.take_while(end.shift('x'), is_hex);
                match int {
                    "0" | "-0" => match self.lookahead {
                        Some((_, ch)) if is_ident_start(ch) => {
                            return self.error(end, UnexpectedChar(ch))
                        }
                        _ => {
                            if hex.is_empty() {
                                return self.error(start, HexLiteralIncomplete);
                            }
                            let is_positive = int == "0";
                            match i64_from_hex(hex, is_positive) {
                                Ok(val) => (start, end, Token::IntLiteral(val)),
                                Err(err) => return self.error(start, err),
                            }
                        }
                    },
                    _ => return self.error(start, HexLiteralWrongPrefix),
                }
            }
            Some((end, 'b')) => {
                self.bump(); // Skip 'b'
                match self.lookahead {
                    Some((pos, ch)) if is_ident_start(ch) => {
                        return self.error(pos, UnexpectedChar(ch))
                    }
                    _ => if let Ok(val) = int.parse() {
                        (start, end.shift('b'), Token::ByteLiteral(val))
                    } else {
                        return self.error(start, NonParseableInt);
                    },
                }
            }
            Some((start, ch)) if is_ident_start(ch) => return self.error(start, UnexpectedChar(ch)),
            None | Some(_) => if let Ok(val) = int.parse() {
                (start, end, Token::IntLiteral(val))
            } else {
                return self.error(start, NonParseableInt);
            },
        };

        Ok(pos::spanned2(start, end, token))
    }

    fn identifier(&mut self, start: Location) -> SpannedToken<'input> {
        let (mut end, mut ident) = self.take_while(start, is_ident_continue);
        match self.lookahead {
            Some((_, c)) if c == '!' => {
                self.bump();
                end.column += 1.into();
                end.absolute += 1.into();
                ident = self.slice(start, end);
            }
            _ => (),
        }

        let token = match ident {
            "and" => Token::And,
            "else" => Token::Else,
            "forall" => Token::Forall,
            "if" => Token::If,
            "in" => Token::In,
            "let" => Token::Let,
            "do" => Token::Do,
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
    type Item = Result<SpannedToken<'input>, SpError>;

    fn next(&mut self) -> Option<Result<SpannedToken<'input>, SpError>> {
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
                '?' => Some(Ok(pos::spanned2(start, start.shift(ch), Token::Question))),

                '"' => Some(self.string_literal(start)),
                '\'' => Some(self.char_literal(start)),

                '/' if self.test_lookahead(|ch| ch == '/') => match self.line_comment(start) {
                    Some(token) => Some(Ok(token)),
                    None => continue,
                },
                '/' if self.test_lookahead(|ch| ch == '*') => match self.block_comment(start) {
                    Ok(Some(token)) => Some(Ok(token)),
                    Ok(None) => continue,
                    Err(err) => Some(Err(err)),
                },
                '#' if start.absolute == BytePos::from(0) && self.test_lookahead(|ch| {
                    ch == '!'
                }) =>
                {
                    match self.shebang_line(start) {
                        Some(token) => Some(Ok(token)),
                        None => continue,
                    }
                }

                ch if is_ident_start(ch) => Some(Ok(self.identifier(start))),
                ch if is_digit(ch) || (ch == '-' && self.test_lookahead(is_digit)) => {
                    Some(self.numeric_literal(start))
                }
                ch if is_operator_char(ch) => Some(Ok(self.operator(start))),
                ch if ch.is_whitespace() => continue,

                ch => Some(self.error(start, UnexpectedChar(ch))),
            };
        }
        // Return EOF instead of None so that the layout algorithm receives the eof location
        Some(Ok(pos::spanned2(
            self.eof_location,
            self.eof_location,
            Token::EOF,
        )))
    }
}

/// Converts partial hex literal (i.e. part after `0x` or `-0x`) to 64 bit signed integer.
///
/// This is basically a copy and adaptation of `std::num::from_str_radix`.
fn i64_from_hex(hex: &str, is_positive: bool) -> Result<i64, Error> {
    const RADIX: u32 = 16;
    let digits = hex.as_bytes();
    let sign: i64 = if is_positive { 1 } else { -1 };
    let mut result = 0i64;
    for &c in digits {
        let x = (c as char).to_digit(RADIX).expect("valid hex literal");
        result = result
            .checked_mul(RADIX as i64)
            .and_then(|result| result.checked_add((x as i64) * sign))
            .ok_or_else(|| {
                if is_positive {
                    HexLiteralOverflow
                } else {
                    HexLiteralUnderflow
                }
            })?;
    }
    Ok(result)
}

#[cfg(test)]
mod test {
    use base::ast::Comment;
    use base::pos::{self, BytePos, Column, Line, Location, Spanned};
    use base::source;

    use super::*;
    use super::{error, Tokenizer};
    use token::Token;
    use token::Token::*;

    fn loc(byte: usize) -> Location {
        Location {
            line: Line::from(0),
            column: Column::from(byte + 1),
            absolute: BytePos::from(byte),
        }
    }

    fn tokenizer<'input>(
        input: &'input str,
    ) -> Box<Iterator<Item = Result<SpannedToken<'input>, SpError>> + 'input> where {
        Box::new(Tokenizer::new(input).take_while(|token| match *token {
            Ok(Spanned {
                value: Token::EOF, ..
            }) => false,
            _ => true,
        }))
    }

    fn test(input: &str, expected: Vec<(&str, Token)>) {
        let mut tokenizer = tokenizer(input);
        let mut count = 0;
        let length = expected.len();
        let source = source::Lines::new(input.as_bytes().iter().cloned());
        for (token, (expected_span, expected_tok)) in tokenizer.by_ref().zip(expected.into_iter()) {
            count += 1;
            println!("{:?}", token);
            let start_byte = expected_span.find("~").unwrap();
            let mut start = source.location(start_byte.into()).unwrap();
            start.column += Column::from(1);

            let end_byte = expected_span.rfind("~").unwrap() + 1;
            let mut end = source.location(end_byte.into()).unwrap();
            end.column += Column::from(1);

            assert_eq!(Ok(pos::spanned2(start, end, expected_tok)), token);
        }

        assert_eq!(count, length);
        assert_eq!(true, count > 0);

        // Make sure that there is nothing else to consume
        assert_eq!(None, tokenizer.next());
    }

    #[test]
    fn sample_lambda_expr() {
        test(
            r#"(hi_, \a -> a ** a)"#,
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
            ],
        );
    }

    #[test]
    fn sample_array() {
        test(
            r#"[1, a]"#,
            vec![
                (r#"~     "#, LBracket),
                (r#" ~    "#, IntLiteral(1)),
                (r#"  ~   "#, Comma),
                (r#"    ~ "#, Identifier("a")),
                (r#"     ~"#, RBracket),
            ],
        );
    }

    #[test]
    fn builtin_operators() {
        test(
            r#". : = | ->"#,
            vec![
                (r#"~         "#, Dot),
                (r#"  ~       "#, Colon),
                (r#"    ~     "#, Equals),
                (r#"      ~   "#, Pipe),
                (r#"        ~~"#, RArrow),
            ],
        );
    }

    #[test]
    fn user_defined_operators() {
        test(
            r#"+-* * /&|=<>: ... <->"#,
            vec![
                (r#"~~~                  "#, Operator("+-*")), // Horiffic!
                (r#"    ~                "#, Operator("*")),
                (r#"      ~~~~~~~        "#, Operator("/&|=<>:")), // Oh my...
                (r#"              ~~~    "#, Operator("...")),
                (r#"                  ~~~"#, Operator("<->")),
            ],
        );
    }

    #[test]
    fn delimters() {
        test(
            r#"{][ () }] "#,
            vec![
                (r#"~         "#, LBrace),
                (r#" ~        "#, RBracket),
                (r#"  ~       "#, LBracket),
                (r#"    ~     "#, LParen),
                (r#"     ~    "#, RParen),
                (r#"       ~  "#, RBrace),
                (r#"        ~ "#, RBracket),
            ],
        );
    }

    #[test]
    fn string_literals() {
        test(
            r#"foo "bar\"\n" baz "" "\t""#,
            vec![
                (r#"~~~                      "#, Identifier("foo")),
                (
                    r#"    ~~~~~~~~~            "#,
                    StringLiteral("bar\"\n".to_string()),
                ),
                (r#"              ~~~        "#, Identifier("baz")),
                (
                    r#"                  ~~     "#,
                    StringLiteral("".to_string()),
                ),
                (
                    r#"                     ~~~~"#,
                    StringLiteral("\t".to_string()),
                ),
            ],
        );
    }

    #[test]
    fn string_literal_unexpected_escape_code() {
        assert_eq!(
            tokenizer(r#""\X""#).last(),
            Some(error(loc(2), UnexpectedEscapeCode('X')))
        );
    }

    #[test]
    fn string_literal_unterminated() {
        assert_eq!(
            tokenizer(r#"foo "bar\"\n baz"#).last(),
            Some(error(loc(4), UnterminatedStringLiteral))
        );
    }

    #[test]
    fn char_literals() {
        test(
            r#"foo 'b' '\\' '\''"#,
            vec![
                (r#"~~~              "#, Identifier("foo")),
                (r#"    ~~~          "#, CharLiteral('b')),
                (r#"        ~~~~     "#, CharLiteral('\\')),
                (r#"             ~~~~"#, CharLiteral('\'')),
            ],
        );
    }

    #[test]
    fn char_literal_empty() {
        assert_eq!(
            tokenizer(r#"foo ''"#).last(),
            Some(error(loc(4), EmptyCharLiteral))
        );
    }

    #[test]
    fn char_literal_unexpected_escape_code() {
        assert_eq!(
            tokenizer(r#"'\X'"#).last(),
            Some(error(loc(2), UnexpectedEscapeCode('X')))
        );
    }

    #[test]
    fn char_literal_unexpected_eof() {
        assert_eq!(tokenizer(r#"'"#).last(), Some(error(loc(1), UnexpectedEof)));
        assert_eq!(
            tokenizer(r#"  '"#).last(),
            Some(error(loc(3), UnexpectedEof))
        );
        assert_eq!(
            tokenizer(r#"'b"#).last(),
            Some(error(loc(2), UnexpectedEof))
        );
        assert_eq!(
            tokenizer(r#"'\\"#).last(),
            Some(error(loc(3), UnexpectedEof))
        );
        assert_eq!(
            tokenizer(r#"'\'"#).last(),
            Some(error(loc(3), UnexpectedEof))
        );
    }

    #[test]
    fn char_literal_unterminated() {
        assert_eq!(
            tokenizer(r#"'frooble'"#).last(),
            Some(error(loc(0), UnterminatedCharLiteral))
        );
    }

    #[test]
    fn int_literals() {
        test(
            r#"3 1036 45 -123"#,
            vec![
                (r#"~             "#, IntLiteral(3)),
                (r#"  ~~~~        "#, IntLiteral(1036)),
                (r#"       ~~     "#, IntLiteral(45)),
                (r#"          ~~~~"#, IntLiteral(-123)),
            ],
        );
    }

    #[test]
    fn hex_literals() {
        test(
            r#"0x1f 0xf 0x123 0x001 -0xA"#,
            vec![
                (r#"~~~~                     "#, IntLiteral(31)),
                (r#"     ~~~                 "#, IntLiteral(15)),
                (r#"         ~~~~~           "#, IntLiteral(291)),
                (r#"               ~~~~~     "#, IntLiteral(1)),
                (r#"                     ~~~~"#, IntLiteral(-10)),
            ],
        )
    }

    #[test]
    fn hex_literals_wrong_prefix() {
        assert_eq!(
            tokenizer(r#"10x1"#).last(),
            Some(error(loc(0), HexLiteralWrongPrefix))
        );
    }

    #[test]
    fn hex_literals_overflow() {
        assert_eq!(
            tokenizer(r#"0x8000000000000000"#).last(),
            Some(error(loc(0), HexLiteralOverflow))
        );
    }

    #[test]
    fn hex_literals_underflow() {
        assert_eq!(
            tokenizer(r#"-0x8000000000000001"#).last(),
            Some(error(loc(0), HexLiteralUnderflow))
        );
    }

    #[test]
    fn hex_literals_incomplete() {
        assert_eq!(
            tokenizer(r#"0x"#).last(),
            Some(error(loc(0), HexLiteralIncomplete))
        );

        assert_eq!(
            tokenizer(r#"0x "#).last(),
            Some(error(loc(0), HexLiteralIncomplete))
        );
    }

    #[test]
    fn hex_literals_unexpected_char() {
        assert_eq!(
            tokenizer(r#"0x1q"#).last(),
            Some(error(loc(3), UnexpectedChar('q')))
        );

        assert_eq!(
            tokenizer(r#"0xff_"#).last(),
            Some(error(loc(4), UnexpectedChar('_')))
        );

        assert_eq!(
            tokenizer(r#"0xx"#).last(),
            Some(error(loc(2), UnexpectedChar('x')))
        );
    }

    #[test]
    fn hex_literals_bounds() {
        test(
            r#"-0x8000000000000000 0x7fffffffffffffff"#,
            vec![
                (
                    "~~~~~~~~~~~~~~~~~~~                   ",
                    IntLiteral(::std::i64::MIN),
                ),
                (
                    "                    ~~~~~~~~~~~~~~~~~~",
                    IntLiteral(::std::i64::MAX),
                ),
            ],
        );
    }

    #[test]
    fn int_literal_overflow() {
        assert_eq!(
            tokenizer(r#"12345678901234567890"#).last(),
            Some(error(loc(0), NonParseableInt))
        );
    }

    #[test]
    fn byte_literals() {
        test(
            r#"3b 255b 45b"#,
            vec![
                (r#"~~         "#, ByteLiteral(3)),
                (r#"   ~~~~    "#, ByteLiteral(255)),
                (r#"        ~~~"#, ByteLiteral(45)),
            ],
        );
    }

    #[test]
    fn byte_literals_unexpected_char() {
        assert_eq!(
            tokenizer(r#"3bs"#).last(),
            Some(error(loc(2), UnexpectedChar('s')))
        );
    }

    #[test]
    fn float_literals() {
        test(
            r#"03.1415 1036.2 -0.0"#,
            vec![
                (r#"~~~~~~~            "#, FloatLiteral(3.1415)),
                (r#"        ~~~~~~     "#, FloatLiteral(1036.2)),
                (r#"               ~~~~"#, FloatLiteral(-0.0)),
            ],
        );
    }

    #[test]
    fn float_literals_unexpected_char() {
        assert_eq!(
            tokenizer(r#"12.3a"#).last(),
            Some(error(loc(4), UnexpectedChar('a')))
        );
    }

    #[test]
    fn line_comments() {
        test(
            r#"hi // hellooo"#,
            vec![(r#"~~           "#, Identifier("hi"))],
        );
    }

    #[test]
    fn line_doc_comments() {
        test(
            r#"hi ///hellooo/// hi"#,
            vec![
                (r#"~~                 "#, Identifier("hi")),
                (
                    r#"   ~~~~~~~~~~~~~~~~"#,
                    DocComment(Comment {
                        typ: CommentType::Line,
                        content: "hellooo/// hi".to_string(),
                    }),
                ),
            ],
        );
    }

    #[test]
    fn line_doc_comments_with_space() {
        test(
            r#"hi /// hellooo/// hi"#,
            vec![
                (r#"~~                  "#, Identifier("hi")),
                (
                    r#"   ~~~~~~~~~~~~~~~~~"#,
                    DocComment(Comment {
                        typ: CommentType::Line,
                        content: "hellooo/// hi".to_string(),
                    }),
                ),
            ],
        );
    }

    #[test]
    fn shebang_line_token_test() {
        test(
            "#!/bin/gluon\nhi /// hellooo/// hi",
            vec![
                (
                    "~~~~~~~~~~~~\n                   ",
                    ShebangLine("/bin/gluon"),
                ),
                ("            \n~~                 ", Identifier("hi")),
                (
                    "            \n   ~~~~~~~~~~~~~~~~~",
                    DocComment(Comment {
                        typ: CommentType::Line,
                        content: "hellooo/// hi".to_string(),
                    }),
                ),
            ],
        );
    }
}
