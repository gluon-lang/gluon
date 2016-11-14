use std::cmp::Ordering;
use std::fmt;

use base::ast::is_operator_char;
use base::pos::{BytePos, Column, Line, Location, Span, Spanned, NO_EXPANSION};

use combine::primitives::{Consumed, Error as CombineError, Info, RangeStream};
use combine::combinator::EnvParser;
use combine::range::{take, take_while};
use combine::*;
use combine::char::{alpha_num, char, letter, spaces, string};
use combine_language::{LanguageEnv, LanguageDef, Identifier};

#[derive(Clone)]
pub struct LocatedStream<I> {
    location: Location,
    input: I,
}

impl<I> StreamOnce for LocatedStream<I>
    where I: StreamOnce<Item = char>,
{
    type Item = I::Item;
    type Range = I::Range;
    type Position = Location;

    fn uncons(&mut self) -> Result<Self::Item, CombineError<Self::Item, Self::Range>> {
        self.input
            .uncons()
            .map(|ch| {
                self.location.bump(ch);
                // HACK: The layout algorithm expects `1` indexing for columns -
                // this could be altered in the future though
                if self.location.column == Column::from(0) {
                    self.location.column = Column::from(1);
                }
                ch
            })
    }

    fn position(&self) -> Self::Position {
        self.location
    }
}

impl<'input, I> RangeStream for LocatedStream<I>
    where I: RangeStream<Item = char, Range = &'input str>,
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
        where F: FnMut(Self::Item) -> bool,
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

pub type Error<'input> = CombineError<Token<&'input str>, Token<&'input str>>;

pub type StrToken<'input> = Token<&'input str>;

#[derive(Clone, PartialEq, Debug)]
pub enum Token<I> {
    Identifier(I),
    Operator(I),
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

impl<I> fmt::Display for Token<I> {
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

pub type SpannedToken<'input> = Spanned<Token<&'input str>, Location>;

#[derive(Clone, Debug)]
struct Offside {
    location: Location,
    context: Context,
}

#[derive(Clone, Debug, PartialEq)]
enum Context {
    /// Context which contains several expressions/declarations separated by semicolons
    Block { emit_semi: bool },
    /// A simple expression
    Expr,
    Let,
    Type,
    If,
    Delimiter(Delimiter),
    MatchClause,
    Lambda,
}

/// Parser passes the environment to each parser function
type LanguageParser<'input: 'lexer, 'lexer, I: 'lexer, T> = EnvParser<&'lexer Lexer<'input, I>,
                                                                      LocatedStream<I>,
                                                                      T>;

struct Contexts {
    stack: Vec<Offside>,
}

impl Contexts {
    fn last(&self) -> Option<&Offside> {
        self.stack.last()
    }

    fn last_mut(&mut self) -> Option<&mut Offside> {
        self.stack.last_mut()
    }

    fn pop(&mut self) -> Option<Offside> {
        self.stack.pop()
    }

    fn push(&mut self, offside: Offside) -> Result<(), Error<'static>> {
        self.check_unindentation_limit(&offside)?;
        self.stack.push(offside);
        Ok(())
    }

    fn check_unindentation_limit(&mut self, offside: &Offside) -> Result<(), Error<'static>> {
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

pub struct Lexer<'input, I>
    where I: RangeStream<Item = char, Range = &'input str>,
{
    env: LanguageEnv<'input, LocatedStream<I>>,
    input: Option<LocatedStream<I>>,
    unprocessed_tokens: Vec<SpannedToken<'input>>,
    indent_levels: Contexts,
    end_span: Option<Span<Location>>,
}

impl<'input, I> Lexer<'input, I>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug + 'input,
{
    pub fn new(input: I) -> Lexer<'input, I> {
        let env = LanguageEnv::new(LanguageDef {
            ident: Identifier {
                start: letter().or(char('_')),
                rest: alpha_num()
                    .or(char('_'))
                    .or(char('\'')),
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

        Lexer {
            env: env,
            input: Some(LocatedStream {
                location: Location {
                    line: Line::from(0),
                    column: Column::from(1),
                    absolute: BytePos::from(0),
                },
                input: input,
            }),
            unprocessed_tokens: Vec::new(),
            indent_levels: Contexts { stack: Vec::new() },
            end_span: None,
        }
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
        let ((builtin, op), _) = (optional((char('#'), take_while(char::is_alphabetic))),
                                  try(self.env.op_())).parse_stream(input)?;
        let len = builtin.map_or(0, |(c, typ)| c.len_utf8() + typ.len()) + op.len();
        take(len).parse_stream(initial)
    }

    fn ident<'a>(&'a self) -> LanguageParser<'input, 'a, I, Token<&'input str>> {
        self.parser(Lexer::parse_ident)
    }

    fn parse_ident(&self,
                   input: LocatedStream<I>)
                   -> ParseResult<Token<&'input str>, LocatedStream<I>> {
        self.env
            .range_identifier_()
            .map(Token::Identifier)
            .parse_stream(input)
    }

    fn layout_independent_token(&mut self,
                                token: SpannedToken<'input>)
                                -> Result<SpannedToken<'input>, Error<'input>> {
        layout(self, token)
    }

    fn id_to_keyword(&self, id: Token<&'input str>) -> Token<&'input str> {
        match id {
            Token::Identifier("let") => Token::Let,
            Token::Identifier("type") => Token::Type,
            Token::Identifier("and") => Token::And,
            Token::Identifier("in") => Token::In,
            Token::Identifier("match") => Token::Match,
            Token::Identifier("with") => Token::With,
            Token::Identifier("if") => Token::If,
            Token::Identifier("then") => Token::Then,
            Token::Identifier("else") => Token::Else,
            id => id,
        }
    }

    fn next_token(&mut self) -> SpannedToken<'input> {
        if let Some(token) = self.unprocessed_tokens.pop() {
            return token;
        }
        let input = match self.input.take() {
            Some(input) => input,
            None => {
                let loc = Location {
                    line: Line::from(0),
                    column: Column::from(1),
                    absolute: BytePos::from(0),
                };
                return SpannedToken {
                    span: Span {
                        start: loc,
                        end: loc,
                        expansion_id: NO_EXPANSION,
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
                let input = match self.env.white_space().parse_stream(input.clone()) {
                    Ok(((), input)) => input.into_inner(),
                    Err(_) => input,
                };
                self.input = Some(input);
                SpannedToken {
                    span: Span {
                        start: start,
                        end: end,
                        expansion_id: NO_EXPANSION,
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
                    expansion_id: NO_EXPANSION,
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
            let parsed_spaces: Result<_, _> = spaces().parse_lazy(input).into();
            let (_, new_input) = parsed_spaces?;
            input = new_input.into_inner();
            *location = input.position();
            let (first, one_char_consumed) = any().parse_stream(input.clone())?;

            // Decide how to tokenize depending on what the first char is
            // ie if its an operator then more operators will follow
            if is_operator_char(first) || first == '#' {
                let (op, new_input) = self.op().parse_stream(input)?;
                input = new_input.into_inner();
                let tok = match op {
                    "=" => Token::Equals,
                    "->" => Token::RightArrow,
                    "|" => Token::Pipe,
                    _ => {
                        if op.starts_with("///") {
                            let mut comment = String::new();
                            let ((), new_input) = spaces().parse_stream(input)?;
                            input = new_input.into_inner();
                            // Merge consecutive line comments
                            loop {
                                let mut line = satisfy(|c| c != '\n' && c != '\r').iter(input);
                                comment.extend(line.by_ref());
                                comment.push('\n');
                                let ((), new_input) = line.into_result(())?;
                                input = new_input.into_inner();
                                let mut p = spaces().with(try(string("///"))).skip(spaces());
                                match p.parse_stream(input.clone()) {
                                    Ok((_, new_input)) => input = new_input.into_inner(),
                                    Err(_) => break,
                                }
                            }
                            comment.pop();
                            return Ok((Token::DocComment(comment), Consumed::Consumed(input)));
                        } else if op.starts_with("/**") {
                            return self.block_doc_comment(input);
                        } else if op.starts_with("//") {
                            let result: Result<_, _> =
                                skip_many(satisfy(|c| c != '\n' && c != '\r'))
                                    .parse_lazy(input)
                                    .into();
                            let ((), new_input) = result?;
                            input = new_input.into_inner();
                            continue;
                        } else if op.starts_with("/*") {
                            // Skip over normal comments and try to parse a new token
                            let ((), new_input) = self.skip_block_comment(input)?;
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
                            Ok(Token::Int(i))
                        } else {
                            if i >= 0 && i <= 256 {
                                Ok(Token::Byte(i as u8))
                            } else {
                                Err(CombineError::Message("Byte literal out of range".into()))
                            }
                        }
                    })
                    .or(self.env.float_().map(Token::Float))
                    .parse_stream(input);
            } else if first.is_alphabetic() || first == '_' {
                return self.ident().map(|t| self.id_to_keyword(t)).parse_stream(input);
            }

            let tok = match first {
                '(' => {
                    match self.ident().map(|t| self.id_to_keyword(t)).parse_stream(input) {
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
                '"' => return self.env.string_literal_().map(Token::String).parse_stream(input),
                '\'' => return self.env.char_literal_().map(Token::Char).parse_stream(input),
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
                    .combine(|input| try(string("*/")).parse_lazy(input).into()) {
                    Ok((_, input)) => return Ok(((), input)),
                    Err(_) => {
                        match input.combine(|input| any().parse_stream(input)) {
                            Ok((_, rest)) => {
                                input = rest;
                            }
                            Err(err) => return Err(err),
                        }
                    }
                }
            }
        });
        block_doc_comment.parse_stream(input)
    }

    fn block_doc_comment(&self,
                         input: LocatedStream<I>)
                         -> ParseResult<Token<&'input str>, LocatedStream<I>> {
        let mut block_doc_comment = parser(|input| {
            let ((), mut input) = spaces().parse_stream(input)?;
            let mut out = String::new();
            loop {
                match input.clone()
                    .combine(|input| try(string("*/")).parse_lazy(input).into()) {
                    Ok((_, input)) => return Ok((Token::DocComment(out), input)),
                    Err(_) => {
                        match input.combine(|input| any().parse_stream(input)) {
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
        block_doc_comment.parse_stream(input)
    }

    fn layout_token(&mut self,
                    token: SpannedToken<'input>,
                    layout_token: Token<&'input str>)
                    -> SpannedToken<'input> {
        let span = token.span;
        self.unprocessed_tokens.push(token);
        SpannedToken {
            span: span,
            value: layout_token,
        }
    }

    fn uncons_next(&mut self) -> Result<SpannedToken<'input>, Error<'input>> {
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
                        expansion_id: NO_EXPANSION,
                    });
                }
                Err(err)
            }
        }
    }
}

fn layout<'input, I>(lexer: &mut Lexer<'input, I>,
                     mut token: SpannedToken<'input>)
                     -> Result<SpannedToken<'input>, Error<'input>>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug,
{
    if token.value == Token::EOF {
        token.span.start.column = Column::from(0);
    }

    loop {
        // Retrieve the current indentation level if one exists
        let offside = match (&token.value, lexer.indent_levels.last().cloned()) {
            (_, Some(offside)) => offside,
            (&Token::EOF, None) => return Ok(token),
            (_, None) => {
                lexer.indent_levels
                    .push(Offside {
                        context: Context::Block { emit_semi: false },
                        location: token.span.start,
                    })?;
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
                (&Token::In, &Context::Let) |
                (&Token::In, &Context::Type) => {
                    let location = {
                        let offside =
                            lexer.indent_levels.last_mut().expect("No top level block found");
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut emit_semi, .. } = offside.context {
                            *emit_semi = false;
                        }
                        offside.location
                    };
                    // Inject a block to ensure that a sequence of expressions end up in the `let` body
                    // ```
                    // let x = 1
                    // a
                    // b
                    // ```
                    // `let x = 1 in {{ a; b }}` and not `{{ (let x = 1 in a) ; b }}`
                    lexer.indent_levels
                        .push(Offside {
                            location: location,
                            context: Context::Block { emit_semi: false },
                        })?;
                    lexer.unprocessed_tokens.push(SpannedToken {
                        span: token.span,
                        value: Token::OpenBlock,
                    });
                    return Ok(token);
                }
                (_, &Context::Block { .. }) => {
                    return Ok(lexer.layout_token(token, Token::CloseBlock));
                }
                (_, _) => continue,
            }
        }

        // Next we check offside rules for each of the contexts
        match offside.context {
            Context::Block { emit_semi } => {
                match ordering {
                    Ordering::Less => {
                        lexer.unprocessed_tokens.push(token.clone());
                        token.value = Token::CloseBlock;
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
                    let location = {
                        let offside =
                            lexer.indent_levels.last_mut().expect("No top level block found");
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut emit_semi, .. } = offside.context {
                            *emit_semi = false;
                        }
                        offside.location
                    };
                    let span = token.span;
                    let result = Ok(lexer.layout_token(token, Token::In));
                    // Inject a block to ensure that a sequence of expressions end up in the `let` body
                    // ```
                    // let x = 1
                    // a
                    // b
                    // ```
                    // `let x = 1 in {{ a; b }}` and not `{{ (let x = 1 in a) ; b }}`
                    lexer.indent_levels
                        .push(Offside {
                            location: location,
                            context: Context::Block { emit_semi: false },
                        })?;
                    lexer.unprocessed_tokens.push(SpannedToken {
                        span: span,
                        value: Token::OpenBlock,
                    });
                    return result;
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
                if let Context::Block { .. } = offside.context {
                    return Ok(lexer.layout_token(token, Token::CloseBlock));
                }
            }
            Token::Equals => {
                if offside.context == Context::Let {
                    scan_for_next_block(lexer, Context::Block { emit_semi: false })?;
                }
            }
            Token::RightArrow => {
                if offside.context == Context::MatchClause || offside.context == Context::Lambda {
                    scan_for_next_block(lexer, Context::Block { emit_semi: false })?;
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
                    scan_for_next_block(lexer, Context::Block { emit_semi: false })?;
                }
            }
            Token::Then => {
                scan_for_next_block(lexer, Context::Block { emit_semi: false })?;
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
            Token::With => scan_for_next_block(lexer, Context::MatchClause)?,
            _ => (),
        }
        return Ok(token);
    }
}

fn scan_for_next_block<'input, 'a, I>(lexer: &mut Lexer<'input, I>,
                                      context: Context)
                                      -> Result<(), Error<'input>>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug + 'input,
{
    let next = lexer.next_token();
    let span = next.span;
    lexer.unprocessed_tokens.push(next);
    if let Context::Block { .. } = context {
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

// Converts an error into a static error by transforming any range arguments into strings
fn static_error<'input>(e: CombineError<Token<&'input str>, Token<&'input str>>)
                        -> CombineError<String, String> {
    let static_info = |i: Info<Token<&'input str>, Token<&'input str>>| {
        match i {
            Info::Token(t) => Info::Token(t.to_string()),
            Info::Range(t) => Info::Range(t.to_string()),
            Info::Borrowed(t) => Info::Borrowed(t),
            Info::Owned(t) => Info::Owned(t),
        }
    };

    match e {
        CombineError::Unexpected(t) => CombineError::Unexpected(static_info(t)),
        CombineError::Expected(t) => CombineError::Expected(static_info(t)),
        CombineError::Message(t) => CombineError::Message(static_info(t)),
        CombineError::Other(t) => CombineError::Other(t),
    }
}

// Adapt lexer for use with LALRPOP
impl<'input, I> Iterator for Lexer<'input, I>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug,
{
    type Item = Result<(BytePos, Token<&'input str>, BytePos), CombineError<String, String>>;

    fn next
        (&mut self)
         -> Option<Result<(BytePos, Token<&'input str>, BytePos), CombineError<String, String>>> {
        match self.uncons_next() {
            Ok(Spanned { value: Token::EOF, .. }) => None,
            Err(ref err) if *err == Error::end_of_input() => None,
            Ok(Spanned { span: Span { start, end, .. }, value }) => {
                Some(Ok((start.absolute, value, end.absolute)))
            }
            Err(error) => Some(Err(static_error(error))),
        }
    }
}
