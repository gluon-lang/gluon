use std::fmt;

use base::ast::is_operator_char;
use base::pos::{self, BytePos, Column, Line, Location};
use combine::primitives::{Consumed, Error as CombineError, RangeStream};
use combine::combinator::EnvParser;
use combine::range::{take, take_while};
use combine::{Parser, ParseResult, StreamOnce};
use combine::{any, env_parser, not_followed_by, optional, parser, satisfy, skip_many, try};
use combine::char::{alpha_num, char, letter, spaces, string};
use combine_language::{LanguageEnv, LanguageDef, Identifier};

use token::{Delimiter, SpannedToken, Token};

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

pub type Error<'input> = CombineError<Token<'input>, Token<'input>>;

/// Parser passes the environment to each parser function
type LanguageParser<'input: 'lexer, 'lexer, I: 'lexer, T> = EnvParser<&'lexer Lexer<'input, I>,
                                                                      LocatedStream<I>,
                                                                      T>;

pub struct Lexer<'input, I>
    where I: RangeStream<Item = char, Range = &'input str>,
{
    env: LanguageEnv<'input, LocatedStream<I>>,
    input: Option<LocatedStream<I>>,
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

    fn ident<'a>(&'a self) -> LanguageParser<'input, 'a, I, Token<'input>> {
        self.parser(Lexer::parse_ident)
    }

    fn parse_ident(&self, input: LocatedStream<I>) -> ParseResult<Token<'input>, LocatedStream<I>> {
        self.env
            .range_identifier_()
            .map(Token::Identifier)
            .parse_stream(input)
    }

    fn id_to_keyword(&self, id: Token<'input>) -> Token<'input> {
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

    pub fn next_token(&mut self) -> SpannedToken<'input> {
        let input = match self.input.take() {
            Some(input) => input,
            None => {
                let loc = Location {
                    line: Line::from(0),
                    column: Column::from(1),
                    absolute: BytePos::from(0),
                };
                return pos::spanned2(loc, loc, Token::EOF);
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
                pos::spanned2(start, end, token)
            }
            Err(err) => {
                let err = err.into_inner();
                debug!("Error tokenizing: {:?}", err);
                pos::spanned2(start, start, Token::CloseBlock)
            }
        }
    }

    fn next_token_(&mut self,
                   location: &mut Location,
                   mut input: LocatedStream<I>)
                   -> ParseResult<Token<'input>, LocatedStream<I>> {
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
                         -> ParseResult<Token<'input>, LocatedStream<I>> {
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
}
