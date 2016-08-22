use std::cmp::Ordering;
use std::fmt;

use base::pos::{BytePos, CharPos, Location, Span, Spanned};

use combine::primitives::{Consumed, Error as CombineError, RangeStream};
use combine::combinator::{take, take_while, EnvParser};
use combine::*;
use combine::char::{alpha_num, char, letter, spaces, string};
use combine_language::{LanguageEnv, LanguageDef, Identifier};

#[derive(Clone)]
pub struct LocatedStream<I> {
    location: Location,
    input: I,
}

impl<I> StreamOnce for LocatedStream<I>
    where I: StreamOnce<Item = char>
{
    type Item = I::Item;
    type Range = I::Range;
    type Position = Location;

    fn uncons(&mut self) -> Result<Self::Item, CombineError<Self::Item, Self::Range>> {
        self.input
            .uncons()
            .map(|ch| {
                self.location.bump(ch);
                ch
            })
    }

    fn position(&self) -> Self::Position {
        self.location
    }
}

impl<'input, I> RangeStream for LocatedStream<I>
    where I: RangeStream<Item = char, Range = &'input str>
{
    fn uncons_range(&mut self,
                    len: usize)
                    -> Result<Self::Range, CombineError<Self::Item, Self::Range>> {
        self.input
            .uncons_range(len)
            .map(|range| {
                for ch in range.chars() {
                    self.location.bump(ch)
                }
                range
            })
    }
    fn uncons_while<F>(&mut self,
                       mut predicate: F)
                       -> Result<Self::Range, CombineError<Self::Item, Self::Range>>
        where F: FnMut(Self::Item) -> bool
    {
        let location = &mut self.location;
        self.input.uncons_while(|t| {
            if predicate(t.clone()) {
                location.bump(t);
                true
            } else {
                false
            }
        })
    }
}

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

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum IdentType {
    /// Constructors are identifiers starting with an uppercase letter
    Constructor,
    /// An operator in identifier position (Example: (+), (-), (>>=))
    Operator,
    /// A normal variable
    Variable,
}

pub type Error<Id> = CombineError<Token<Id>, Token<Id>>;

#[derive(Clone, PartialEq, Debug)]
pub enum Token<Id> {
    Identifier(Id, IdentType),
    Operator(Id),
    String(String),
    Char(char),
    Integer(i64),
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
    Equal,
    OpenBlock,
    CloseBlock,
    Semi,
    EOF,
}

impl<Id> fmt::Display for Token<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Token::*;
        use self::Delimiter::*;
        let s = match *self {
            Identifier(..) => "Identifier",
            Operator(..) => "Operator",
            String(..) => "String",
            Char(..) => "Char",
            Integer(..) => "Integer",
            Byte(..) => "Byte",
            Float(..) => "Float",
            DocComment(..) => "DocComment",
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
            Equal => "Equal",
            OpenBlock => "OpenBlock",
            CloseBlock => "CloseBlock",
            Semi => "Semi",
            EOF => "EOF",
        };
        s.fmt(f)
    }
}

impl<Id> Token<Id> {
    pub fn map<Id2, F>(&self, f: F) -> Token<Id2>
        where F: FnOnce(&Id) -> Id2
    {
        use self::Token::*;
        match *self {
            Identifier(ref id, b) => Identifier(f(id), b),
            Operator(ref id) => Operator(f(id)),
            String(ref s) => String(s.clone()),
            Char(c) => Char(c),
            Integer(i) => Integer(i),
            Byte(i) => Byte(i),
            Float(f) => Float(f),
            DocComment(ref s) => DocComment(s.clone()),
            Let => Let,
            And => And,
            In => In,
            Type => Type,
            Match => Match,
            With => With,
            If => If,
            Then => Then,
            Else => Else,
            Open(d) => Open(d),
            Close(d) => Close(d),
            Lambda => Lambda,
            RightArrow => RightArrow,
            Colon => Colon,
            Dot => Dot,
            Comma => Comma,
            Pipe => Pipe,
            Equal => Equal,
            OpenBlock => OpenBlock,
            CloseBlock => CloseBlock,
            Semi => Semi,
            EOF => EOF,
        }
    }
}

pub type SpannedToken<Id> = Spanned<Token<Id>, Location>;

#[derive(Clone, Debug)]
pub struct Offside {
    pub location: Location,
    pub context: Context,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Context {
    /// Contaxt which contains several expressions/declarations separated by semicolons
    Block {
        emit_semi: bool,
        needs_close: bool,
    },
    /// A simple expression
    Expr,
    Let,
    Type,
    If,
    Then,
    Delimiter(Delimiter),
    MatchClause,
    Lambda,
}

/// Parser passes the environment to each parser function
type LanguageParser<'input: 'lexer, 'lexer, I: 'lexer, T> = EnvParser<&'lexer Lexer<'input, I>,
                                                                      LocatedStream<I>,
                                                                      T>;

pub struct Contexts {
    stack: Vec<Offside>,
}

impl Contexts {
    pub fn last(&self) -> Option<&Offside> {
        self.stack.last()
    }

    pub fn last_mut(&mut self) -> Option<&mut Offside> {
        self.stack.last_mut()
    }

    pub fn pop(&mut self) -> Option<Offside> {
        self.stack.pop()
    }

    pub fn push<Id>(&mut self, offside: Offside) -> Result<(), Error<Id>> {
        try!(self.check_unindentation_limit(&offside));
        self.stack.push(offside);
        Ok(())
    }

    pub fn replace<Id>(&mut self, offside: Offside) -> Result<(), Error<Id>> {
        self.pop();
        self.push(offside)
    }

    fn check_unindentation_limit<Id>(&mut self, offside: &Offside) -> Result<(), Error<Id>> {
        let mut skip_block = false;
        for other_offside in self.stack.iter().rev() {
            match other_offside.context {
                Context::Lambda => {
                    skip_block = true;
                    continue;
                }
                Context::Delimiter(_) => return Ok(()),
                Context::Block { .. } if skip_block => continue,
                // New context should not be unindented past the closest enclosing block context
                Context::MatchClause |
                Context::Type |
                Context::Let |
                Context::Block { .. } if offside.location.column <
                                         other_offside.location.column => (),
                _ => continue,
            }
            debug!("Unindentation error: {:?} < {:?}", offside, other_offside);
            return Err(CombineError::Message("Line was unindented to far".into()));
        }
        Ok(())
    }
}

fn is_operator_char(c: char) -> bool {
    "+-*/&|=<>".chars().any(|x| x == c)
}

pub struct Lexer<'input, I>
    where I: RangeStream<Item = char, Range = &'input str>
{
    pub env: LanguageEnv<'input, LocatedStream<I>>,
    pub input: Option<LocatedStream<I>>,
    pub unprocessed_tokens: Vec<SpannedToken<&'input str>>,
    pub indent_levels: Contexts,
    /// Since the parser will call `position` before retrieving the token we need to cache one
    /// token so the span can be returned for it
    next_token: Option<SpannedToken<&'input str>>,
    end_span: Option<Span<Location>>,
}

impl<'input, I> Lexer<'input, I>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug + 'input
{
    pub fn new(input: I) -> Lexer<'input, I> {
        let env = LanguageEnv::new(LanguageDef {
            ident: Identifier {
                start: letter().or(char('_')),
                rest: alpha_num().or(char('_')),
                // ["if", "then", "else", "let", "and", "in", "type", "case", "of"]
                // .iter()
                // .map(|x| (*x).into())
                // .collect(),
                reserved: Vec::new(),
            },
            op: Identifier {
                start: satisfy(is_operator_char),
                rest: satisfy(is_operator_char),
                reserved: Vec::new(),
            },
            comment_start: satisfy(|_| false).map(|_| ()),
            comment_end: satisfy(|_| false).map(|_| ()),
            comment_line: satisfy(|_| false).map(|_| ()),
        });

        let mut lexer = Lexer {
            env: env,
            input: Some(LocatedStream {
                location: Location {
                    line: 1,
                    column: CharPos(1),
                    absolute: BytePos(0),
                },
                input: input,
            }),
            unprocessed_tokens: Vec::new(),
            indent_levels: Contexts { stack: Vec::new() },
            next_token: None,
            end_span: None,
        };
        lexer.next_token = lexer.uncons_next().ok();
        lexer
    }

    fn parser<'a, T>(&'a self,
                     parser: fn(&Lexer<'input, I>, LocatedStream<I>)
                                -> ParseResult<T, LocatedStream<I>>)
                     -> LanguageParser<'input, 'a, I, T> {
        env_parser(self, parser)
    }

    /// Parses an operator
    fn op<'a>(&'a self) -> LanguageParser<'input, 'a, I, &'input str> {
        self.parser(Lexer::parse_op)
    }

    fn parse_op(&self, input: LocatedStream<I>) -> ParseResult<&'input str, LocatedStream<I>> {
        let initial = input.clone();
        let ((builtin, op), _) = try!((optional((char('#'), take_while(char::is_alphabetic))),
                                       try(self.env.op_()))
            .parse_state(input));
        let len = builtin.map_or(0, |(c, typ)| c.len_utf8() + typ.len()) + op.len();
        take(len).parse_state(initial)
    }

    fn ident<'a>(&'a self) -> LanguageParser<'input, 'a, I, Token<&'input str>> {
        self.parser(Lexer::parse_ident)
    }

    fn parse_ident(&self,
                   input: LocatedStream<I>)
                   -> ParseResult<Token<&'input str>, LocatedStream<I>> {
        self.parser(Lexer::parse_ident2)
            .map(|x| Token::Identifier(x.0, x.1))
            .parse_state(input)
    }

    /// Identifier parser which returns the identifier as well as the type of the identifier
    fn parse_ident2(&self,
                    input: LocatedStream<I>)
                    -> ParseResult<(&'input str, IdentType), LocatedStream<I>> {
        let id = self.env.range_identifier_().map(|id| {
            let typ = if id.chars().next().unwrap().is_uppercase() {
                IdentType::Constructor
            } else {
                IdentType::Variable
            };
            (id, typ)
        });
        let op = self.env.parens(self.env.range_op_()).map(|id| (id, IdentType::Operator));
        try(id)
            .or(try(op))
            .parse_state(input)
    }

    fn layout_independent_token(&mut self,
                                token: SpannedToken<&'input str>)
                                -> Result<SpannedToken<&'input str>, Error<&'input str>> {
        layout(self, token)
    }

    fn id_to_keyword(&self, id: Token<&'input str>) -> Token<&'input str> {
        let t = match id {
            Token::Identifier(id, _) => {
                match id {
                    "let" => Some(Token::Let),
                    "type" => Some(Token::Type),
                    "and" => Some(Token::And),
                    "in" => Some(Token::In),
                    "match" => Some(Token::Match),
                    "with" => Some(Token::With),
                    "if" => Some(Token::If),
                    "then" => Some(Token::Then),
                    "else" => Some(Token::Else),
                    _ => None,
                }
            }
            _ => None,
        };
        match t {
            Some(t) => t,
            _ => id,
        }
    }

    pub fn next_token(&mut self) -> SpannedToken<&'input str> {
        if let Some(token) = self.unprocessed_tokens.pop() {
            return token;
        }
        let input = match self.input.take() {
            Some(input) => input,
            None => {
                let loc = Location {
                    line: ::std::u32::MAX,
                    column: CharPos(1),
                    absolute: BytePos(::std::u32::MAX),
                };
                return SpannedToken {
                    span: Span {
                        start: loc,
                        end: loc,
                    },
                    value: Token::EOF,
                };
            }
        };
        let mut start = input.position();
        let result = self.next_token_(&mut start, input);
        match result {
            Ok((token, input)) => {
                let input = input.into_inner();
                let end = input.position();
                let input = match self.env.white_space().parse_state(input.clone()) {
                    Ok(((), input)) => input.into_inner(),
                    Err(_) => input,
                };
                self.input = Some(input);
                SpannedToken {
                    span: Span {
                        start: start,
                        end: end,
                    },
                    value: token,
                }
            }
            Err(err) => {
                let err = err.into_inner();
                debug!("Error tokenizing: {:?}", err);
                let span = Span {
                    start: start,
                    end: start,
                };
                self.end_span = Some(span);
                SpannedToken {
                    span: span,
                    value: Token::CloseBlock,
                }
            }
        }
    }

    fn next_token_(&mut self,
                   location: &mut Location,
                   mut input: LocatedStream<I>)
                   -> ParseResult<Token<&'input str>, LocatedStream<I>> {
        loop {
            // Skip all whitespace before the token
            let (_, new_input) = try!(spaces().parse_lazy(input));
            input = new_input.into_inner();
            *location = input.position();
            let (first, one_char_consumed) = try!(any().parse_state(input.clone()));

            // Decide how to tokenize depending on what the first char is
            // ie if its an operator then more operators will follow
            if is_operator_char(first) || first == '#' {
                let (op, new_input) = try!(self.op().parse_state(input));
                input = new_input.into_inner();
                let tok = match op {
                    "=" => Token::Equal,
                    "->" => Token::RightArrow,
                    "|" => Token::Pipe,
                    _ => {
                        if op.starts_with("///") {
                            let mut comment = String::new();
                            let ((), new_input) = try!(spaces().parse_state(input));
                            input = new_input.into_inner();
                            // Merge consecutive line comments
                            loop {
                                let mut line = satisfy(|c| c != '\n' && c != '\r').iter(input);
                                comment.extend(line.by_ref());
                                comment.push('\n');
                                let ((), new_input) = try!(line.into_result(()));
                                input = new_input.into_inner();
                                let mut p = spaces().with(try(string("///"))).skip(spaces());
                                match p.parse_state(input.clone()) {
                                    Ok((_, new_input)) => input = new_input.into_inner(),
                                    Err(_) => break,
                                }
                            }
                            comment.pop();
                            return Ok((Token::DocComment(comment), Consumed::Consumed(input)));
                        } else if op.starts_with("/**") {
                            return self.block_doc_comment(input);
                        } else if op.starts_with("//") {
                            let ((), new_input) =
                                try!(skip_many(satisfy(|c| c != '\n' && c != '\r'))
                                    .parse_lazy(input));
                            input = new_input.into_inner();
                            continue;
                        } else if op.starts_with("/*") {
                            // Skip over normal comments and try to parse a new token
                            let ((), new_input) = try!(self.skip_block_comment(input));
                            input = new_input.into_inner();
                            continue;
                        } else {
                            Token::Operator(op)
                        }
                    }
                };
                return Ok((tok, Consumed::Consumed(input)));
            } else if first.is_digit(10) {
                let int_or_byte = (self.env.integer_(), optional(char('b')));
                return try(int_or_byte.skip(not_followed_by(string("."))))
                    .and_then(|(i, byte)| {
                        if byte.is_none() {
                            Ok(Token::Integer(i))
                        } else {
                            if i >= 0 && i <= 256 {
                                Ok(Token::Byte(i as u8))
                            } else {
                                Err(CombineError::Message("Byte literal out of range".into()))
                            }
                        }
                    })
                    .or(self.env.float_().map(Token::Float))
                    .parse_state(input);
            } else if first.is_alphabetic() || first == '_' {
                return self.ident().map(|t| self.id_to_keyword(t)).parse_state(input);
            }

            let tok = match first {
                '(' => {
                    match self.ident().map(|t| self.id_to_keyword(t)).parse_state(input) {
                        Ok(x) => return Ok(x),
                        Err(_) => Token::Open(Delimiter::Paren),
                    }
                }
                ')' => Token::Close(Delimiter::Paren),
                '{' => Token::Open(Delimiter::Brace),
                '}' => Token::Close(Delimiter::Brace),
                '[' => Token::Open(Delimiter::Bracket),
                ']' => Token::Close(Delimiter::Bracket),
                ':' => Token::Colon,
                ',' => Token::Comma,
                '.' => Token::Dot,
                '\\' => Token::Lambda,
                '"' => return self.env.string_literal_().map(Token::String).parse_state(input),
                '\'' => return self.env.char_literal_().map(Token::Char).parse_state(input),
                _ => Token::EOF,
            };
            return Ok((tok, one_char_consumed));
        }
    }

    fn skip_block_comment(&self, input: LocatedStream<I>) -> ParseResult<(), LocatedStream<I>> {
        let mut block_doc_comment = parser(|input| {
            let mut input = Consumed::Empty(input);
            loop {
                match input.clone()
                    .combine(|input| try(string("*/")).parse_lazy(input)) {
                    Ok((_, input)) => return Ok(((), input)),
                    Err(_) => {
                        match input.combine(|input| any().parse_state(input)) {
                            Ok((_, rest)) => {
                                input = rest;
                            }
                            Err(err) => return Err(err),
                        }
                    }
                }
            }
        });
        block_doc_comment.parse_state(input)
    }

    fn block_doc_comment(&self,
                         input: LocatedStream<I>)
                         -> ParseResult<Token<&'input str>, LocatedStream<I>> {
        let mut block_doc_comment = parser(|input| {
            let ((), mut input) = try!(spaces().parse_state(input));
            let mut out = String::new();
            loop {
                match input.clone()
                    .combine(|input| try(string("*/")).parse_lazy(input)) {
                    Ok((_, input)) => return Ok((Token::DocComment(out), input)),
                    Err(_) => {
                        match input.combine(|input| any().parse_state(input)) {
                            Ok((c, rest)) => {
                                out.push(c);
                                input = rest
                            }
                            Err(err) => return Err(err),
                        }
                    }
                }
            }
        });
        block_doc_comment.parse_state(input)
    }

    fn layout_token(&mut self,
                    token: SpannedToken<&'input str>,
                    layout_token: Token<&'input str>)
                    -> SpannedToken<&'input str> {
        let span = token.span;
        self.unprocessed_tokens.push(token);
        SpannedToken {
            span: span,
            value: layout_token,
        }
    }

    fn uncons_next(&mut self) -> Result<SpannedToken<&'input str>, Error<&'input str>> {
        let token = self.next_token();
        match self.layout_independent_token(token) {
            Ok(SpannedToken { value: Token::EOF, .. }) => Err(Error::end_of_input()),
            Ok(token) => {
                debug!("Lex {:?}", token);
                Ok(token)
            }
            Err(err) => {
                if let Some(input) = self.input.take() {
                    let loc = input.position();
                    self.end_span = Some(Span {
                        start: loc,
                        end: loc,
                    });
                }
                Err(err)
            }
        }
    }
}

fn layout<'input, I>(lexer: &mut Lexer<'input, I>,
                     mut token: SpannedToken<&'input str>)
                     -> Result<SpannedToken<&'input str>, Error<&'input str>>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug
{
    if token.value == Token::EOF {
        token.span.start.column = CharPos(0);
    }
    loop {
        // Retrieve the current indentation level if one exists
        let offside = match lexer.indent_levels.last().cloned() {
            Some(offside) => offside,
            None => {
                if token.value == Token::EOF {
                    return Ok(token);
                }
                try!(lexer.indent_levels.push(Offside {
                    context: Context::Block {
                        emit_semi: false,
                        needs_close: true,
                    },
                    location: token.span.start,
                }));
                debug!("Default block {:?}", token);
                return Ok(lexer.layout_token(token, Token::OpenBlock));
            }
        };
        debug!("--------\n{:?}\n{:?}", token, offside);
        let ordering = token.span.start.column.cmp(&offside.location.column);

        // If it is closing token we remove contexts until a context for that token is found
        if [Token::In,
            Token::CloseBlock,
            Token::Else,
            Token::Close(Delimiter::Brace),
            Token::Close(Delimiter::Bracket),
            Token::Close(Delimiter::Paren),
            Token::Comma]
            .iter()
            .any(|t| *t == token.value) {

            if token.value == Token::Comma &&
               (offside.context == Context::Delimiter(Delimiter::Brace) ||
                offside.context == Context::Delimiter(Delimiter::Bracket)) {
                return Ok(token);
            }
            lexer.indent_levels.pop();
            match (&token.value, &offside.context) {
                (&Token::Else, &Context::If) => (),
                (&Token::Close(close_delim), &Context::Delimiter(context_delim))
                    if close_delim == context_delim => return Ok(token),
                (&Token::In, &Context::Let) |
                (&Token::In, &Context::Type) |
                (&Token::CloseBlock, &Context::Block { .. }) => {
                    if let Some(offside) = lexer.indent_levels.last_mut() {
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut emit_semi, .. } = offside.context {
                            *emit_semi = false;
                        }
                    }
                    return Ok(token);
                }
                _ => {
                    match offside.context {
                        Context::Block { needs_close: true, .. } => {
                            return Ok(lexer.layout_token(token, Token::CloseBlock));
                        }
                        _ => (),
                    }
                    continue;
                }
            }
        }
        // Next we check offside rules for each of the contexts
        match offside.context {
            Context::Block { emit_semi, needs_close } => {
                match ordering {
                    Ordering::Less => {
                        if needs_close {
                            lexer.unprocessed_tokens.push(token.clone());
                            token.value = Token::CloseBlock;
                        } else {
                            lexer.indent_levels.pop();
                        }
                        continue;
                    }
                    Ordering::Equal => {
                        match token.value {
                            _ if emit_semi => {
                                if let Some(offside) = lexer.indent_levels.last_mut() {
                                    // The enclosing block should not emit a block separator for the
                                    // next expression
                                    if let Context::Block { ref mut emit_semi, .. } =
                                           offside.context {
                                        *emit_semi = false;
                                    }
                                }
                                return Ok(lexer.layout_token(token, Token::Semi));
                            }
                            Token::DocComment(_) |
                            Token::OpenBlock => (),
                            _ => {
                                // If it is the first token in a sequence we dont want to emit a
                                // separator
                                if let Some(offside) = lexer.indent_levels.last_mut() {
                                    if let Context::Block { ref mut emit_semi, .. } =
                                           offside.context {
                                        *emit_semi = true;
                                    }
                                }
                            }
                        }
                    }
                    _ => (),
                }
            }
            Context::Expr | Context::Lambda => {
                if ordering != Ordering::Greater {
                    lexer.indent_levels.pop();
                    continue;
                }
            }
            Context::MatchClause => {
                // Must allow `|` to be on the same line
                if ordering == Ordering::Less ||
                   (ordering == Ordering::Equal && token.value != Token::Pipe) {
                    lexer.indent_levels.pop();
                    continue;
                }
            }
            Context::Let | Context::Type => {
                // `and` and `}` are allowed to be on the same line as the `let` or `type`
                if ordering == Ordering::Equal && token.value != Token::And &&
                   token.value != Token::Close(Delimiter::Brace) {
                    // Insert an `in` token
                    lexer.indent_levels.pop();
                    if let Some(offside) = lexer.indent_levels.last_mut() {
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut emit_semi, .. } = offside.context {
                            *emit_semi = false;
                        }
                    }
                    return Ok(lexer.layout_token(token, Token::In));
                }
            }
            _ => (),
        }
        // Some tokens directly inserts a new context when emitted
        let push_context = match token.value {
            Token::Let => Some(Context::Let),
            Token::If => Some(Context::If),
            Token::Type => Some(Context::Type),
            Token::Match => Some(Context::Expr),
            Token::Lambda => Some(Context::Lambda),
            Token::Open(delim) => Some(Context::Delimiter(delim)),
            _ => None,
        };
        if let Some(context) = push_context {
            let offside = Offside {
                location: token.span.start,
                context: context,
            };
            return lexer.indent_levels.push(offside).map(move |()| token);
        }
        // For other tokens we need to scan for the next token to get its position
        match token.value {
            Token::In => {
                lexer.indent_levels.pop();
                if let Context::Block { needs_close: true, .. } = offside.context {
                    return Ok(lexer.layout_token(token, Token::CloseBlock));
                }
            }
            Token::Equal => {
                if offside.context == Context::Let {
                    try!(scan_for_next_block(lexer,
                                             Context::Block {
                                                 emit_semi: false,
                                                 needs_close: true,
                                             }));
                }
            }
            Token::RightArrow => {
                if offside.context == Context::MatchClause || offside.context == Context::Lambda {
                    try!(scan_for_next_block(lexer,
                                             Context::Block {
                                                 emit_semi: false,
                                                 needs_close: true,
                                             }));
                }
            }
            Token::Else => {
                let next = lexer.next_token();
                // Need to allow "else if" expressions so avoid inserting a block for those cases
                // (A block would be inserted at column 5 and we would then get unindentation
                // errors on the branches)
                // if x then
                //     1
                // else if y then
                //     2
                // else
                //     3
                let add_block = next.value != Token::If ||
                                next.span.start.line != token.span.start.line;
                lexer.unprocessed_tokens.push(next);
                if add_block {
                    try!(scan_for_next_block(lexer,
                                             Context::Block {
                                                 emit_semi: false,
                                                 needs_close: true,
                                             }));
                }
            }
            Token::Then => {
                try!(scan_for_next_block(lexer,
                                         Context::Block {
                                             emit_semi: false,
                                             needs_close: true,
                                         }));
            }
            Token::Comma => {
                // Prevent a semi to be emitted before the next token
                if let Some(offside) = lexer.indent_levels.last_mut() {
                    // The enclosing block should not emit a block separator for the next
                    // expression
                    if let Context::Block { ref mut emit_semi, .. } = offside.context {
                        *emit_semi = false;
                    }
                }
            }
            Token::With => try!(scan_for_next_block(lexer, Context::MatchClause)),
            _ => (),
        }
        return Ok(token);
    }
}

fn scan_for_next_block<'input, 'a, I>(lexer: &mut Lexer<'input, I>,
                                      context: Context)
                                      -> Result<(), Error<&'input str>>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug + 'input
{
    let next = lexer.next_token();
    let span = next.span;
    lexer.unprocessed_tokens.push(next);
    if let Context::Block { needs_close: true, .. } = context {
        lexer.unprocessed_tokens.push(SpannedToken {
            span: span,
            value: Token::OpenBlock,
        });
    }
    lexer.indent_levels.push(Offside {
        location: span.start,
        context: context,
    })
}

impl<'input, I> StreamOnce for Lexer<'input, I>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,

          I::Range: fmt::Debug
{
    type Item = Token<&'input str>;
    type Range = Token<&'input str>;
    type Position = Span<Location>;

    fn uncons(&mut self) -> Result<Token<&'input str>, Error<&'input str>> {
        match self.next_token.take() {
            Some(token) => {
                self.next_token = self.uncons_next().ok();
                Ok(token.value)
            }
            None => {
                self.next_token = Some(try!(self.uncons_next()));
                self.uncons()
            }
        }
    }

    fn position(&self) -> Self::Position {
        self.next_token
            .as_ref()
            .or_else(|| self.unprocessed_tokens.last())
            .map(|token| token.span)
            .unwrap_or_else(|| self.end_span.unwrap())
    }
}
