use std::{fmt, str};

use codespan::ByteOffset;

use ordered_float::NotNan;

use self::Error::*;

use crate::{
    base::{
        ast::is_operator_byte,
        error::Errors,
        metadata::{Comment, CommentType},
        pos::{self, BytePos, Column, Line, Location, Spanned},
    },
    str_suffix::{self, StrSuffix},
};

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Token<S> {
    ShebangLine(S),
    Identifier(S),
    Operator(S),

    StringLiteral(StringLiteral<S>),
    CharLiteral(char),
    IntLiteral(i64),
    ByteLiteral(u8),
    FloatLiteral(NotNan<f64>),
    DocComment(Comment<S>),

    Rec,
    Else,
    Forall,
    If,
    In,
    Let,
    Do,
    Seq,
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

    AttributeOpen,

    EOF, // Required for the layout algorithm
}

impl<S> fmt::Display for Token<S>
where
    S: fmt::Display,
{
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

            Rec => "Rec",
            Else => "Else",
            Forall => "Forall",
            If => "If",
            In => "In",
            Let => "Let",
            Do => "Do",
            Seq => "Seq",
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

            AttributeOpen => "#[",

            EOF => "EOF",
        };
        s.fmt(f)
    }
}

impl<S> Token<S> {
    pub(crate) fn map<R>(self, f: impl FnOnce(S) -> R) -> Token<R> {
        use self::Token::*;
        match self {
            ShebangLine(s) => ShebangLine(f(s)),
            Identifier(s) => Identifier(f(s)),
            Operator(s) => Operator(f(s)),
            StringLiteral(s) => StringLiteral(match s {
                self::StringLiteral::Escaped(s) => self::StringLiteral::Escaped(f(s)),
                self::StringLiteral::Raw(s) => self::StringLiteral::Raw(f(s)),
            }),
            CharLiteral(x) => CharLiteral(x),
            IntLiteral(x) => IntLiteral(x),
            ByteLiteral(x) => ByteLiteral(x),
            FloatLiteral(x) => FloatLiteral(x),
            DocComment(Comment { typ, content }) => DocComment(Comment {
                typ,
                content: f(content),
            }),

            Rec => Rec,
            Else => Else,
            Forall => Forall,
            If => If,
            In => In,
            Let => Let,
            Do => Do,
            Seq => Seq,
            Match => Match,
            Then => Then,
            Type => Type,
            With => With,

            LBrace => LBrace,
            LBracket => LBracket,
            LParen => LParen,

            RBrace => RBrace,
            RBracket => RBracket,
            RParen => RParen,

            At => At,
            Colon => Colon,
            Comma => Comma,
            Dot => Dot,
            DotDot => DotDot,
            Equals => Equals,
            Lambda => Lambda,
            Pipe => Pipe,
            RArrow => RArrow,
            Question => Question,

            OpenBlock => OpenBlock,
            CloseBlock => CloseBlock,
            Semi => Semi,

            AttributeOpen => AttributeOpen,

            EOF => EOF,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum StringLiteral<S> {
    Escaped(S),
    Raw(S),
}

impl StringLiteral<&'_ str> {
    pub fn unescape(&self) -> String {
        match self {
            StringLiteral::Escaped(s) => unescape_string_literal(s),
            StringLiteral::Raw(s) => s.to_string(),
        }
    }
}

fn unescape_string_literal(mut s: &str) -> String {
    let mut string = String::new();
    while let Some(i) = s.bytes().position(|b| b == b'\\') {
        let c = match s.as_bytes()[i + 1] {
            b'\'' => '\'',
            b'"' => '"',
            b'\\' => '\\',
            b'/' => '/',
            b'n' => '\n',
            b'r' => '\r',
            b't' => '\t',
            _ => panic!("Invalid escape"),
        };
        string.push_str(&s[..i]);
        string.push(c);
        s = &s[i + 2..];
    }
    string.push_str(s);

    string
}

pub type BorrowedToken<'input> = Token<&'input str>;
pub type SpannedToken<'input> = Spanned<Token<&'input str>, Location>;

pub type SpError = Spanned<Error, Location>;
pub type Result<T, E = SpError> = std::result::Result<T, E>;

quick_error! {
    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    pub enum Error {
        EmptyCharLiteral {
            display("empty char literal")
        }
        UnexpectedChar(ch: char) {
            display("unexpected character")
        }
        UnexpectedEof {
            display("unexpected end of file")
        }
        UnexpectedEscapeCode(ch: char) {
            display("unexpected escape code")
        }
        UnterminatedCharLiteral {
            display("unterminated character literal")
        }
        UnterminatedStringLiteral {
            display("unterminated string literal")
        }
        InvalidRawStringDelimiter {
            display("raw strings can only use `#` as a delimter")
        }
        NonParseableInt {
            display("cannot parse integer, probable overflow")
        }
        HexLiteralOverflow {
            display("cannot parse hex literal, overflow")
        }
        HexLiteralUnderflow {
            display("cannot parse hex literal, underflow")
        }
        HexLiteralWrongPrefix {
            display("wrong hex literal prefix, should start as '0x' or '-0x'")
        }
        HexLiteralIncomplete {
            display("cannot parse hex literal, incomplete")
        }
    }
}

fn error<T>(location: Location, code: Error) -> Result<T, SpError> {
    Err(pos::spanned2(location, location, code))
}

fn is_ident_start(ch: u8) -> bool {
    // TODO: Unicode?
    match ch {
        b'_' | b'a'..=b'z' | b'A'..=b'Z' => true,
        _ => false,
    }
}

fn is_ident_continue(ch: u8) -> bool {
    // TODO: Unicode?
    match ch {
        b'0'..=b'9' | b'\'' => true,
        ch => is_ident_start(ch),
    }
}

fn is_digit(ch: u8) -> bool {
    (ch as char).is_digit(10)
}

fn is_hex(ch: u8) -> bool {
    (ch as char).is_digit(16)
}

struct CharLocations<'input> {
    location: Location,
    chars: str_suffix::Iter<'input>,
}

impl<'input> CharLocations<'input> {
    pub fn new<S>(input: &'input S) -> CharLocations<'input>
    where
        S: ?Sized + crate::ParserSource,
    {
        CharLocations {
            location: Location {
                line: Line::from(0),
                column: Column::from(1),
                absolute: input.start_index(),
            },
            chars: StrSuffix::new(input.src()).iter(),
        }
    }
}

impl<'input> Iterator for CharLocations<'input> {
    type Item = (Location, u8);

    fn next(&mut self) -> Option<(Location, u8)> {
        self.chars.next().map(|ch| {
            let location = self.location;
            self.location.shift(ch);
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
    start_index: BytePos,
    pub errors: Errors<SpError>,
}

impl<'input> Tokenizer<'input> {
    pub fn new<S>(input: &'input S) -> Tokenizer<'input>
    where
        S: ?Sized + crate::ParserSource,
    {
        let chars = CharLocations::new(input);

        Tokenizer {
            input: input.src(),
            chars,
            start_index: input.start_index(),
            errors: Errors::new(),
        }
    }

    fn bump(&mut self) -> Option<(Location, u8)> {
        self.chars.next()
    }

    fn lookahead(&self) -> Option<(Location, u8)> {
        self.chars
            .chars
            .as_str_suffix()
            .first()
            .map(|b| (self.chars.location, b))
    }

    fn skip_to_end(&mut self) {
        while let Some(_) = self.bump() {}
    }

    fn error<T>(&mut self, location: Location, code: Error) -> Result<T, SpError> {
        self.skip_to_end();
        error(location, code)
    }

    fn recover<T>(
        &mut self,
        start: Location,
        end: Location,
        code: Error,
        value: T,
    ) -> Result<Spanned<T, Location>, SpError> {
        self.errors.push(pos::spanned2(start, end, code));

        Ok(pos::spanned2(start, end, value))
    }

    fn eof_recover<T>(&mut self, value: T) -> Result<Spanned<T, Location>, SpError> {
        let end = self.next_loc();
        self.recover(end, end, UnexpectedEof, value)
    }

    fn next_loc(&self) -> Location {
        self.lookahead()
            .as_ref()
            .map_or(self.chars.location, |l| l.0)
    }

    fn eof_error<T>(&mut self) -> Result<T, SpError> {
        let location = self.next_loc();
        self.error(location, UnexpectedEof)
    }

    fn slice(&self, start: Location, end: Location) -> &'input str {
        let start = start.absolute - ByteOffset::from(self.start_index.to_usize() as i64);
        let end = end.absolute - ByteOffset::from(self.start_index.to_usize() as i64);

        &self.input[start.to_usize()..end.to_usize()]
    }

    fn take_while<F>(&mut self, start: Location, mut keep_going: F) -> (Location, &'input str)
    where
        F: FnMut(u8) -> bool,
    {
        self.take_until(start, |c| !keep_going(c))
    }

    fn take_until<F>(&mut self, start: Location, mut terminate: F) -> (Location, &'input str)
    where
        F: FnMut(u8) -> bool,
    {
        while let Some((end, ch)) = self.lookahead() {
            if terminate(ch) {
                return (end, self.slice(start, end));
            } else {
                self.bump();
            }
        }
        (self.next_loc(), self.slice(start, self.next_loc()))
    }

    fn test_lookahead<F>(&self, mut test: F) -> bool
    where
        F: FnMut(u8) -> bool,
    {
        self.lookahead().map_or(false, |(_, ch)| test(ch))
    }

    fn line_comment(&mut self, start: Location) -> Option<SpannedToken<'input>> {
        let (end, comment) = self.take_until(start, |ch| ch == b'\n');

        if comment.starts_with("///") {
            let skip = if comment.starts_with("/// ") { 4 } else { 3 };
            let doc = Token::DocComment(Comment {
                typ: CommentType::Line,
                content: &comment[skip..],
            });
            Some(pos::spanned2(start, end, doc))
        } else {
            None
        }
    }

    fn block_comment(&mut self, start: Location) -> Result<Option<SpannedToken<'input>>, SpError> {
        self.bump(); // Skip first b'*'

        loop {
            let (_, comment) = self.take_until(start, |ch| ch == b'*');
            self.bump(); // Skip next b'*'
            match self.lookahead() {
                Some((_, b'/')) => {
                    self.bump();
                    let end = self.next_loc();
                    if comment.starts_with("/**") && comment != "/**" {
                        // FIXME: whitespace alignment
                        let doc = Token::DocComment(Comment {
                            typ: CommentType::Block,
                            content: comment[3..].trim(),
                        });
                        return Ok(Some(pos::spanned2(start, end, doc)));
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
        let (end, op) = self.take_while(start, is_operator_byte);

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
                let (_, op) = self.take_while(start, is_operator_byte);
                Token::Operator(op)
            }
            op => Token::Operator(op),
        };

        pos::spanned2(start, end, token)
    }

    fn escape_code(&mut self, start: Location) -> Result<u8, SpError> {
        match self.bump() {
            Some((_, b'\'')) => Ok(b'\''),
            Some((_, b'"')) => Ok(b'"'),
            Some((_, b'\\')) => Ok(b'\\'),
            Some((_, b'/')) => Ok(b'/'),
            Some((_, b'n')) => Ok(b'\n'),
            Some((_, b'r')) => Ok(b'\r'),
            Some((_, b't')) => Ok(b'\t'),
            // TODO: Unicode escape codes
            Some((end, b)) => {
                let ch = self.chars.chars.as_str_suffix().restore_char(&[b]);
                self.recover(start, end, UnexpectedEscapeCode(ch), b)
                    .map(|s| s.value)
            }
            None => self.eof_recover(b'\0').map(|s| s.value),
        }
    }

    fn string_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, SpError> {
        let content_start = self.next_loc();
        loop {
            let scan_start = self.next_loc();
            self.take_until(scan_start, |b| b == b'"' || b == b'\\');
            match self.bump() {
                Some((start, b'\\')) => {
                    self.escape_code(start)?;
                }
                Some((_, b'"')) => {
                    let end = self.next_loc();

                    let mut content_end = end;
                    content_end.absolute.0 -= 1;

                    let token = Token::StringLiteral(StringLiteral::Escaped(
                        self.slice(content_start, content_end),
                    ));
                    return Ok(pos::spanned2(start, end, token));
                }
                _ => break,
            }
        }

        let end = self.chars.location;

        let token = Token::StringLiteral(StringLiteral::Escaped(self.slice(content_start, end)));
        self.recover(start, end, UnterminatedStringLiteral, token)
    }

    fn raw_string_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, SpError> {
        let mut delimiters = 0;
        while let Some((_, ch)) = self.bump() {
            match ch {
                b'#' => delimiters += 1,
                b'"' => break,
                _ => return self.error(start, InvalidRawStringDelimiter),
            }
        }

        let content_start = self.next_loc();
        loop {
            self.take_until(content_start, |b| b == b'"');
            match self.bump() {
                Some((_, b'"')) => {
                    let mut found_delimiters = 0;
                    loop {
                        if found_delimiters == delimiters {
                            let end = self.next_loc();
                            let mut content_end = end;
                            content_end.absolute.0 -= delimiters + 1;
                            let string = self.slice(content_start, content_end);

                            let token = Token::StringLiteral(StringLiteral::Raw(string));
                            return Ok(pos::spanned2(start, end, token));
                        }
                        if let Some((_, ch)) = self.bump() {
                            match ch {
                                b'#' => found_delimiters += 1,
                                b'"' => found_delimiters = 0,
                                _ => break,
                            }
                        } else {
                            break;
                        }
                    }
                }
                _ => break,
            }
        }

        let end = self.chars.location;

        let token = Token::StringLiteral(StringLiteral::Raw(self.slice(content_start, end)));
        self.recover(start, end, UnterminatedStringLiteral, token)
    }

    fn shebang_line(&mut self, start: Location) -> Option<SpannedToken<'input>> {
        let (end, line) = self.take_until(start, |ch| ch == b'\n');

        if line.starts_with("#!") {
            let skip = 2;
            let result = line[skip..].trim_end();
            let tok = Token::ShebangLine(result);
            Some(pos::spanned2(start, end, tok))
        } else {
            None
        }
    }

    fn char_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, SpError> {
        let ch = match self.bump() {
            Some((start, b'\\')) => self.escape_code(start)?,
            Some((end, b'\'')) => {
                return self.recover(start, end, EmptyCharLiteral, Token::CharLiteral('\0'))
            }
            Some((_, ch)) => ch,
            None => return self.eof_recover(Token::CharLiteral('\0')),
        };

        match self.bump() {
            Some((_, b'\'')) => {
                let ch = self.chars.chars.as_str_suffix().restore_char(&[ch]);
                Ok(pos::spanned2(
                    start,
                    self.next_loc(),
                    Token::CharLiteral(ch),
                ))
            }
            Some((end, _)) => {
                let ch = self.chars.chars.as_str_suffix().restore_char(&[ch]);
                self.recover(start, end, UnterminatedCharLiteral, Token::CharLiteral(ch))
            } // UnexpectedEscapeCode?
            None => self.eof_recover(Token::CharLiteral('\0')),
        }
    }

    fn numeric_literal(&mut self, start: Location) -> Result<SpannedToken<'input>, SpError> {
        let (end, int) = self.take_while(start, is_digit);

        Ok(match self.lookahead() {
            Some((_, b'.')) => {
                self.bump(); // Skip b'.'
                let (end, float) = self.take_while(start, is_digit);
                match self.lookahead() {
                    Some((next, ch)) if is_ident_start(ch) => {
                        let ch = self.chars.chars.as_str_suffix().restore_char(&[ch]);
                        self.recover(end, next, UnexpectedChar(ch), ())?;
                    }
                    _ => (),
                }
                pos::spanned2(
                    start,
                    end,
                    Token::FloatLiteral(NotNan::new(float.parse().unwrap()).unwrap()),
                )
            }
            Some((_, b'x')) => {
                self.bump(); // Skip b'x'
                let int_start = self.next_loc();
                let end1 = end;
                let (end, hex) = self.take_while(int_start, is_hex);
                match int {
                    "0" | "-0" => {
                        match self.lookahead() {
                            Some((lookahead_end, ch)) if is_ident_start(ch) => {
                                let ch = self.chars.chars.as_str_suffix().restore_char(&[ch]);

                                self.recover(end, lookahead_end, UnexpectedChar(ch), ())?;
                            }
                            _ => (),
                        }
                        if hex.is_empty() {
                            return self.recover(
                                start,
                                end,
                                HexLiteralIncomplete,
                                Token::IntLiteral(0),
                            );
                        }
                        let is_positive = int == "0";
                        match i64_from_hex(hex, is_positive) {
                            Ok(val) => pos::spanned2(start, end, Token::IntLiteral(val)),
                            Err(err) => return self.recover(start, end, err, Token::IntLiteral(0)),
                        }
                    }
                    _ => {
                        return self.recover(
                            start,
                            end1,
                            HexLiteralWrongPrefix,
                            Token::IntLiteral(0),
                        )
                    }
                }
            }
            Some((_, b'b')) => {
                self.bump(); // Skip b'b'
                let end = self.next_loc();
                match self.lookahead() {
                    Some((pos, ch)) if is_ident_start(ch) => {
                        let ch = self.chars.chars.as_str_suffix().restore_char(&[ch]);
                        self.recover(end, pos, UnexpectedChar(ch), ())?;
                    }
                    _ => (),
                }
                if let Ok(val) = int.parse() {
                    pos::spanned2(start, end, Token::ByteLiteral(val))
                } else {
                    self.recover(start, end, NonParseableInt, Token::ByteLiteral(0))?
                }
            }
            Some((start, ch)) if is_ident_start(ch) => {
                let ch = self.chars.chars.as_str_suffix().restore_char(&[ch]);
                self.recover(start, start, UnexpectedChar(ch), ())?;

                if let Ok(val) = int.parse() {
                    pos::spanned2(start, end, Token::IntLiteral(val))
                } else {
                    self.recover(start, end, NonParseableInt, Token::IntLiteral(0))?
                }
            }
            None | Some(_) => {
                if let Ok(val) = int.parse() {
                    pos::spanned2(start, end, Token::IntLiteral(val))
                } else {
                    self.recover(start, end, NonParseableInt, Token::IntLiteral(0))?
                }
            }
        })
    }

    fn identifier(&mut self, start: Location) -> Result<SpannedToken<'input>, SpError> {
        let (mut end, mut ident) = self.take_while(start, is_ident_continue);
        match self.lookahead() {
            Some((_, c)) if c == b'!' => {
                self.bump();
                end.column += 1.into();
                end.absolute += 1.into();
                ident = self.slice(start, end);
            }
            _ => (),
        }

        let token = match ident {
            "rec" => Token::Rec,
            "else" => Token::Else,
            "forall" => Token::Forall,
            "if" => Token::If,
            "in" => Token::In,
            "let" => Token::Let,
            "do" => Token::Do,
            "seq" => Token::Seq,
            "match" => Token::Match,
            "then" => Token::Then,
            "type" => Token::Type,
            "with" => Token::With,
            src => Token::Identifier(src),
        };

        Ok(pos::spanned2(start, end, token))
    }
}

impl<'input> Iterator for Tokenizer<'input> {
    type Item = Result<SpannedToken<'input>, SpError>;

    fn next(&mut self) -> Option<Result<SpannedToken<'input>, SpError>> {
        while let Some((start, ch)) = self.bump() {
            return match ch {
                b',' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::Comma))),
                b'\\' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::Lambda))),
                b'{' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::LBrace))),
                b'[' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::LBracket))),
                b'(' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::LParen))),
                b'}' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::RBrace))),
                b']' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::RBracket))),
                b')' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::RParen))),
                b'?' => Some(Ok(pos::spanned2(start, self.next_loc(), Token::Question))),

                b'r' if self.test_lookahead(|ch| ch == b'"' || ch == b'#') => {
                    Some(self.raw_string_literal(start))
                }
                b'"' => Some(self.string_literal(start)),
                b'\'' => Some(self.char_literal(start)),

                b'/' if self.test_lookahead(|ch| ch == b'/') => match self.line_comment(start) {
                    Some(token) => Some(Ok(token)),
                    None => continue,
                },
                b'/' if self.test_lookahead(|ch| ch == b'*') => match self.block_comment(start) {
                    Ok(Some(token)) => Some(Ok(token)),
                    Ok(None) => continue,
                    Err(err) => Some(Err(err)),
                },
                b'#' if start.absolute == self.start_index
                    && self.test_lookahead(|ch| ch == b'!') =>
                {
                    match self.shebang_line(start) {
                        Some(token) => Some(Ok(token)),
                        None => continue,
                    }
                }

                b'#' if self.test_lookahead(|ch| ch == b'[') => {
                    self.bump();
                    Some(Ok(pos::spanned2(
                        start,
                        self.next_loc(),
                        Token::AttributeOpen,
                    )))
                }
                ch if is_ident_start(ch) => Some(self.identifier(start)),
                ch if is_digit(ch) || (ch == b'-' && self.test_lookahead(is_digit)) => {
                    Some(self.numeric_literal(start))
                }
                ch if is_operator_byte(ch) => Some(Ok(self.operator(start))),
                ch if (ch as char).is_whitespace() => continue, // TODO Unicode whitespace

                ch => {
                    let ch = self.chars.chars.as_str_suffix().restore_char(&[ch]);
                    let end = self.next_loc();
                    if let Err(err) = self.recover(start, end, UnexpectedChar(ch), ()) {
                        return Some(Err(err));
                    }
                    continue;
                }
            };
        }
        // Return EOF instead of None so that the layout algorithm receives the eof location
        Some(Ok(pos::spanned2(
            self.next_loc(),
            self.next_loc(),
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
    use crate::base::metadata::Comment;
    use crate::base::pos::{self, BytePos, Column, Line, Location, Spanned};

    use codespan::{ByteOffset, ColumnOffset};

    use super::*;
    use super::{error, StringLiteral, Tokenizer};
    use crate::token::Token;
    use crate::token::Token::*;

    fn loc(byte: u32) -> Location {
        Location {
            line: Line::from(0),
            column: Column::from(byte + 1),
            absolute: BytePos::from(byte + 1),
        }
    }

    fn error2<T>(start: u32, end: u32, code: Error) -> Result<T, SpError> {
        Err(pos::spanned2(loc(start), loc(end), code))
    }

    fn tokenizer<'input>(
        input: &'input str,
    ) -> impl Iterator<Item = Result<SpannedToken<'input>, SpError>> + 'input {
        let mut tokenizer = Tokenizer::new(input);
        Box::new(std::iter::from_fn(move || {
            let result = tokenizer.next()?;
            if let Some(err) = tokenizer.errors.pop() {
                return Some(Err(err));
            }
            match result {
                Ok(Spanned {
                    value: Token::EOF, ..
                }) => None,
                result => Some(result),
            }
        }))
    }

    fn test(input: &str, expected: Vec<(&str, BorrowedToken<'_>)>) {
        use base::source::Source;

        let mut tokenizer = tokenizer(input);
        let mut count = 0;
        let length = expected.len();
        let source = <base::source::FileMap as Source>::new(input);
        for (token, (expected_span, expected_tok)) in tokenizer.by_ref().zip(expected.into_iter()) {
            count += 1;
            println!("{:?}", token);
            let start_byte =
                source.span().start() + ByteOffset::from(expected_span.find("~").unwrap() as i64);
            let mut start = Source::location(&source, start_byte).unwrap();
            start.column += ColumnOffset::from(1);

            let end_byte = source.span().start()
                + ByteOffset::from(expected_span.rfind("~").unwrap() as i64 + 1);
            let mut end = Source::location(&source, end_byte.into()).unwrap();
            end.column += ColumnOffset::from(1);

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
            r#"foo "bar\"\n" baz "" "\t" "\"\"""#,
            vec![
                (r#"~~~                      "#, Identifier("foo")),
                (
                    r#"    ~~~~~~~~~            "#,
                    Token::StringLiteral(StringLiteral::Escaped("bar\\\"\\n")),
                ),
                (r#"              ~~~        "#, Identifier("baz")),
                (
                    r#"                  ~~     "#,
                    Token::StringLiteral(StringLiteral::Escaped("")),
                ),
                (
                    r#"                     ~~~~"#,
                    Token::StringLiteral(StringLiteral::Escaped("\\t")),
                ),
                (
                    r#"                          ~~~~~~"#,
                    Token::StringLiteral(StringLiteral::Escaped(r#"\"\""#)),
                ),
            ],
        );
        assert_eq!(StringLiteral::Escaped(r#"\"\""#).unescape(), r#""""#);
    }

    #[test]
    fn raw_string_literals() {
        test(
            r#########"foo r#"bar" "# baz r##""## r#"""#  "#########,
            vec![
                (r####"~~~                      "####, Identifier("foo")),
                (
                    r#"    ~~~~~~~~~~            "#,
                    Token::StringLiteral(StringLiteral::Raw("bar\" ")),
                ),
                (r####"               ~~~        "####, Identifier("baz")),
                (
                    r#"                   ~~~~~~~     "#,
                    Token::StringLiteral(StringLiteral::Raw("")),
                ),
                (
                    r#"                           ~~~~~~     "#,
                    Token::StringLiteral(StringLiteral::Raw("\"")),
                ),
            ],
        );
    }

    #[test]
    fn string_literal_unexpected_escape_code() {
        assert_eq!(
            tokenizer(r#""\X""#).last(),
            Some(error2(1, 2, UnexpectedEscapeCode('X')))
        );
    }

    #[test]
    fn string_literal_unterminated() {
        assert_eq!(
            tokenizer(r#"foo "bar\"\n baz"#).last(),
            Some(Err(pos::spanned2(
                loc(4),
                loc(16),
                UnterminatedStringLiteral
            )))
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
            Some(error2(4, 5, EmptyCharLiteral))
        );
    }

    #[test]
    fn char_literal_unexpected_escape_code() {
        assert_eq!(
            tokenizer(r#"'\X'"#).last(),
            Some(error2(1, 2, UnexpectedEscapeCode('X')))
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
            tokenizer(r#"'frooble'"#).next(),
            Some(error2(0, 2, UnterminatedCharLiteral))
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
            tokenizer(r#"10x1"#).next(),
            Some(error2(0, 2, HexLiteralWrongPrefix))
        );
    }

    #[test]
    fn hex_literals_overflow() {
        assert_eq!(
            tokenizer(r#"0x8000000000000000"#).last(),
            Some(error2(0, 18, HexLiteralOverflow))
        );
    }

    #[test]
    fn hex_literals_underflow() {
        assert_eq!(
            tokenizer(r#"-0x8000000000000001"#).last(),
            Some(error2(0, 19, HexLiteralUnderflow))
        );
    }

    #[test]
    fn hex_literals_incomplete() {
        assert_eq!(
            tokenizer(r#"0x"#).last(),
            Some(error2(0, 2, HexLiteralIncomplete))
        );

        assert_eq!(
            tokenizer(r#"0x "#).last(),
            Some(error2(0, 2, HexLiteralIncomplete))
        );
    }

    #[test]
    fn hex_literals_unexpected_char() {
        assert_eq!(
            tokenizer(r#"0x1q"#).next(),
            Some(error2(3, 3, UnexpectedChar('q')))
        );

        assert_eq!(
            tokenizer(r#"0xff_"#).next(),
            Some(error2(4, 4, UnexpectedChar('_')))
        );

        assert_eq!(
            tokenizer(r#"0xx"#).last(),
            Some(error2(2, 2, UnexpectedChar('x')))
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
            Some(error2(0, 20, NonParseableInt))
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
            tokenizer(r#"3bs"#).next(),
            Some(error(loc(2), UnexpectedChar('s')))
        );
    }

    #[test]
    fn float_literals() {
        test(
            r#"03.1415 1036.2 -0.0"#,
            vec![
                (
                    r#"~~~~~~~            "#,
                    FloatLiteral(NotNan::new(3.1415).unwrap()),
                ),
                (
                    r#"        ~~~~~~     "#,
                    FloatLiteral(NotNan::new(1036.2).unwrap()),
                ),
                (
                    r#"               ~~~~"#,
                    FloatLiteral(NotNan::new(-0.0).unwrap()),
                ),
            ],
        );
    }

    #[test]
    fn float_literals_unexpected_char() {
        assert_eq!(
            tokenizer(r#"12.3a"#).next(),
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
                        content: "hellooo/// hi",
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
                        content: "hellooo/// hi",
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
                        content: "hellooo/// hi",
                    }),
                ),
            ],
        );
    }
}
