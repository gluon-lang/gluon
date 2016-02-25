use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt;
use std::rc::Rc;

use base::ast::*;

use combine::primitives::{HasPosition, Stream, SourcePosition};
use combine::combinator::EnvParser;
use combine::*;
use combine_language::{LanguageEnv, LanguageDef, Identifier};

#[derive(Clone, PartialEq, Debug)]
pub enum Token<Id> {
    Identifier(Id, bool),
    Operator(Id),
    String(String),
    Char(char),
    Integer(i64),
    Float(f64),
    Let,
    And,
    In,
    Type,
    Case,
    Of,
    If,
    Then,
    Else,
    OpenBrace,
    CloseBrace,
    OpenParen,
    CloseParen,
    OpenBracket,
    CloseBracket,
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
        let s = match *self {
            Identifier(..) => "Identifier",
            Operator(..) => "Operator",
            String(..) => "String",
            Char(..) => "Char",
            Integer(..) => "Integer",
            Float(..) => "Float",
            Let => "Let",
            And => "And",
            In => "In",
            Type => "Type",
            Case => "Case",
            Of => "Of",
            If => "If",
            Then => "Then",
            Else => "Else",
            OpenBrace => "OpenBrace",
            CloseBrace => "CloseBrace",
            OpenParen => "OpenParen",
            CloseParen => "CloseParen",
            OpenBracket => "OpenBracket",
            CloseBracket => "CloseBracket",
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
            Float(f) => Float(f),
            Let => Let,
            And => And,
            In => In,
            Type => Type,
            Case => Case,
            Of => Of,
            If => If,
            Then => Then,
            Else => Else,
            OpenBrace => OpenBrace,
            CloseBrace => CloseBrace,
            OpenParen => OpenParen,
            CloseParen => CloseBracket,
            OpenBracket => OpenBracket,
            CloseBracket => CloseBracket,
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

#[derive(Clone, Debug)]
pub struct PToken<Id> {
    pub location: SourcePosition,
    pub token: Token<Id>,
}

#[derive(Clone, Debug)]
pub struct Offside {
    pub context: Context,
    pub location: SourcePosition,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Context {
    /// Contaxt which contains several expressions/declarations separated by semicolons
    Block {
        first: bool,
        needs_close: bool,
    },
    /// A simple expression
    Expr,
    Let,
    Type,
    If,
    Then,
    Brace,
    Paren,
    Bracket,
    MatchClause,
    Lambda,
}

impl<Id> Token<Id> {
    pub fn context(&self) -> Option<Context> {
        match *self {
            Token::OpenBlock => {
                Some(Context::Block {
                    first: true,
                    needs_close: true,
                })
            }
            Token::Let => Some(Context::Let),
            Token::Type => Some(Context::Type),
            _ => None,
        }
    }
}

/// Parser passes the environment to each parser function
type LanguageParser<'a: 'b, 'b, I: 'b, F: 'b, T> = EnvParser<&'b Lexer<'a, I, F>, State<I>, T>;

pub struct Lexer<'a, I, F>
    where I: Stream<Item = char>,
          F: IdentEnv
{
    pub env: LanguageEnv<'a, State<I>>,
    pub make_ident: Rc<RefCell<F>>,
    pub input: Option<State<I>>,
    pub unprocessed_tokens: Vec<PToken<F::Ident>>,
    pub indent_levels: Vec<Offside>,
    end_position: SourcePosition,
    layout: fn(&mut Lexer<'a, I, F>, PToken<F::Ident>) -> Result<Token<F::Ident>, Token<F::Ident>>,
}

impl<'a, I, F> HasPosition for Lexer<'a, I, F>
    where I: Stream<Item = char>,
          F: IdentEnv
{
    type Position = SourcePosition;
    fn position(&self) -> Self::Position {
        self.unprocessed_tokens
            .last()
            .map(|token| token.location.clone())
            .or_else(|| self.input.as_ref().map(|input| input.position.clone()))
            .unwrap_or_else(|| self.end_position.clone())
    }
}

impl<'a, 's, I, Id, F> Lexer<'a, I, F>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: AstId + Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug + 's
{
    pub fn new(layout: Option<fn(&mut Lexer<'a, I, F>, PToken<F::Ident>)
                                 -> Result<Token<F::Ident>, Token<F::Ident>>>,
               input: I,
               make_ident: Rc<RefCell<F>>)
               -> Lexer<'a, I, F> {
        let ops = "+-*/&|=<>";
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
                start: satisfy(move |c| ops.chars().any(|x| x == c)),
                rest: satisfy(move |c| ops.chars().any(|x| x == c)),
                reserved: ["->", "\\", "|"].iter().map(|x| (*x).into()).collect(),
            },
            comment_start: string("/*").map(|_| ()),
            comment_end: string("*/").map(|_| ()),
            comment_line: string("//").map(|_| ()),
        });

        let mut lexer = Lexer {
            env: env,
            make_ident: make_ident,
            input: Some(State::new(input)),
            unprocessed_tokens: Vec::new(),
            indent_levels: Vec::new(),
            end_position: SourcePosition {
                column: -1,
                line: -1,
            },
            layout: layout.unwrap_or(layout_),
        };
        lexer.skip_whitespace();
        lexer
    }

    fn skip_whitespace(&mut self) {
        if let Some(input) = self.input.take() {
            self.input = Some(self.env.white_space().parse(input).unwrap().1);
        }
    }

    fn intern(&self, s: &str) -> Id {
        self.make_ident.borrow_mut().from_str(s)
    }

    fn parser<T>(&'s self,
                 parser: fn(&Lexer<'a, I, F>, State<I>) -> ParseResult<T, State<I>>)
                 -> LanguageParser<'a, 's, I, F, T> {
        env_parser(self, parser)
    }

    ///Parses an operator
    fn op(&'s self) -> LanguageParser<'a, 's, I, F, Id> {
        self.parser(Lexer::parse_op)
    }

    fn parse_op(&self, input: State<I>) -> ParseResult<Id, State<I>> {
        (optional(char('#').with(many(letter()))), try(self.env.op()))
            .map(|(builtin, op): (Option<String>, String)| {
                match builtin {
                    Some(mut builtin) => {
                        builtin.insert(0, '#');
                        builtin.extend(op.chars());
                        self.intern(&builtin)
                    }
                    None => self.intern(&op),
                }
            })
            .parse_state(input)
    }

    fn ident(&'s self) -> LanguageParser<'a, 's, I, F, Token<Id>> {
        self.parser(Lexer::parse_ident)
    }
    fn parse_ident(&self, input: State<I>) -> ParseResult<Token<Id>, State<I>> {
        self.parser(Lexer::parse_ident2)
            .map(|x| Token::Identifier(x.0, x.1))
            .parse_state(input)
    }

    /// Identifier parser which returns `(id, true)` if the identifier is a constructor
    /// (Starts with an uppercase letter
    fn parse_ident2(&self, input: State<I>) -> ParseResult<(Id, bool), State<I>> {
        try(self.env.identifier())
            .or(try(self.env.parens(self.env.op())))
            .map(|s| (self.intern(&s), s.chars().next().unwrap().is_uppercase()))
            .parse_state(input)
    }

    fn layout_independent_token(&mut self, token: PToken<Id>) -> Result<Token<Id>, Token<Id>> {
        (self.layout)(self, token)
    }

    fn id_to_keyword(&self, id: Token<Id>) -> Token<Id> {
        let t = match id {
            Token::Identifier(ref id, _) => {
                match self.make_ident.borrow().string(&id) {
                    "let" => Some(Token::Let),
                    "type" => Some(Token::Type),
                    "and" => Some(Token::And),
                    "in" => Some(Token::In),
                    "case" => Some(Token::Case),
                    "of" => Some(Token::Of),
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

    pub fn next_token(&mut self) -> PToken<Id> {
        if let Some(token) = self.unprocessed_tokens.pop() {
            return token;
        }
        let input = match self.input.take() {
            Some(input) => input,
            None => {
                return PToken {
                    location: SourcePosition {
                        column: 1,
                        line: ::std::i32::MAX,
                    },
                    token: Token::EOF,
                }
            }
        };
        let location = input.position();
        let result = self.env
                         .lex(choice::<[&mut Parser<Input = State<I>, Output = Token<Id>>; 19],
                                       _>([&mut self.ident()
                                                    .map(|id| self.id_to_keyword(id)),
                                           &mut self.env
                                                    .reserved_op("\\")
                                                    .map(|_| Token::Lambda),
                                           &mut self.env
                                                    .reserved_op("->")
                                                    .map(|_| Token::RightArrow),
                                           &mut self.env.reserved_op(":").map(|_| Token::Colon),
                                           &mut self.env.reserved_op(".").map(|_| Token::Dot),
                                           &mut self.env.reserved_op(",").map(|_| Token::Comma),
                                           &mut self.env.reserved_op("|").map(|_| Token::Pipe),
                                           &mut self.env.reserved_op("=").map(|_| Token::Equal),
                                           &mut self.op().map(Token::Operator),
                                           &mut char('(').map(|_| Token::OpenParen),
                                           &mut char(')').map(|_| Token::CloseParen),
                                           &mut char('{').map(|_| Token::OpenBrace),
                                           &mut char('}').map(|_| Token::CloseBrace),
                                           &mut char('[').map(|_| Token::OpenBracket),
                                           &mut char(']').map(|_| Token::CloseBracket),
                                           &mut self.env.string_literal().map(Token::String),
                                           &mut self.env.char_literal().map(Token::Char),
                                           &mut try(self.env
                                                        .integer()
                                                        .skip(not_followed_by(string("."))))
                                                    .map(Token::Integer),
                                           &mut self.env.float().map(Token::Float)]))
                         .map(|token| {
                             PToken {
                                 location: location,
                                 token: token,
                             }
                         })
                         .parse(input);
        match result {
            Ok((token, input)) => {
                self.input = Some(input);
                token
            }
            Err(err) => {
                self.end_position = err.position;
                PToken {
                    location: location,
                    token: Token::CloseBlock,
                }
            }
        }
    }
}

fn layout_<'a, I, Id, F>(lexer: &mut Lexer<'a, I, F>,
                         mut token: PToken<Id>)
                         -> Result<Token<Id>, Token<Id>>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: AstId + Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug
{
    if token.token == Token::EOF {
        token.location.column = 0;
    }
    loop {
        let offside = match lexer.indent_levels.last().cloned() {
            Some(offside) => offside,
            None => {
                if token.token == Token::EOF {
                    return Ok(token.token);
                }
                lexer.indent_levels.push(Offside {
                    context: Context::Block {
                        first: true,
                        needs_close: true,
                    },
                    location: token.location,
                });
                debug!("Default block {:?}", token);
                lexer.unprocessed_tokens.push(token);
                return Ok(Token::OpenBlock);
            }
        };
        debug!("--------\n{:?}\n{:?}", token, offside);
        let ordering = token.location.column.cmp(&offside.location.column);
        // If it is closing token we remove contexts until a context for that token is found
        if [Token::In,
            Token::CloseBlock,
            Token::Else,
            Token::CloseBrace,
            Token::CloseParen,
            Token::CloseBracket,
            Token::Comma]
               .iter()
               .any(|t| *t == token.token) {

            if token.token == Token::Comma &&
               (offside.context == Context::Brace || offside.context == Context::Bracket) {
                return Ok(token.token);
            }
            lexer.indent_levels.pop();
            match (&token.token, &offside.context) {
                (&Token::Else, &Context::If) |
                (&Token::CloseBrace, &Context::Brace) |
                (&Token::CloseParen, &Context::Paren) |
                (&Token::CloseBracket, &Context::Bracket) => {
                    return Ok(token.token);
                }
                (&Token::In, &Context::Let) |
                (&Token::In, &Context::Type) |
                (&Token::CloseBlock, &Context::Block { .. }) => {
                    if let Some(offside) = lexer.indent_levels.last_mut() {
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut first, .. } = offside.context {
                            *first = true;
                        }
                    }
                    return Ok(token.token);
                }
                _ => {
                    match offside.context {
                        Context::Block { needs_close: true, .. } => {
                            lexer.unprocessed_tokens.push(token);
                            return Ok(Token::CloseBlock);
                        }
                        _ => (),
                    }
                    continue;
                }
            }
        }
        // Next we check offside rules for each of the contexts
        match offside.context {
            Context::Block { first, needs_close } => {
                match ordering {
                    Ordering::Less => {
                        if needs_close {
                            lexer.unprocessed_tokens.push(token.clone());
                            token.token = Token::CloseBlock;
                        } else {
                            lexer.indent_levels.pop();
                        }
                        continue;
                    }
                    Ordering::Equal => {
                        if first && token.token != Token::OpenBlock {
                            // If it is the first token in a sequence we dont want to emit a
                            // separator
                            if let Some(offside) = lexer.indent_levels.last_mut() {
                                // The enclosing block should not emit a block separator for the
                                // next expression
                                if let Context::Block { ref mut first, .. } = offside.context {
                                    *first = false;
                                }
                            }
                        } else if !first {
                            if let Some(offside) = lexer.indent_levels.last_mut() {
                                // The enclosing block should not emit a block separator for the
                                // next expression
                                if let Context::Block { ref mut first, .. } = offside.context {
                                    *first = true;
                                }
                            }
                            lexer.unprocessed_tokens.push(token);
                            return Ok(Token::Semi);
                        }
                    }
                    _ => (),
                }
            }
            Context::Expr | Context::MatchClause => {
                if ordering == Ordering::Less {
                    lexer.indent_levels.pop();
                    continue;
                }
            }
            Context::Let | Context::Type => {
                // `and` and `}` are allowed to be on the same line as the `let` or `type`
                if ordering == Ordering::Equal && token.token != Token::And &&
                   token.token != Token::CloseBrace {
                    // Insert an `in` token
                    lexer.indent_levels.pop();
                    if let Some(offside) = lexer.indent_levels.last_mut() {
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut first, .. } = offside.context {
                            *first = true;
                        }
                    }
                    lexer.unprocessed_tokens.push(token);
                    return Ok(Token::In);
                }
            }
            _ => (),
        }
        // Finally we check the token in case it needs to push a new context
        match token.token {
            Token::Let => {
                lexer.indent_levels.push(Offside {
                    context: Context::Let,
                    location: token.location,
                });
            }
            Token::If => {
                lexer.indent_levels.push(Offside {
                    context: Context::If,
                    location: token.location,
                });
            }
            Token::Type => {
                lexer.indent_levels.push(Offside {
                    context: Context::Type,
                    location: token.location,
                });
            }
            Token::Case => {
                lexer.indent_levels.push(Offside {
                    context: Context::Expr,
                    location: token.location,
                });
            }
            Token::Lambda => {
                lexer.indent_levels.push(Offside {
                    context: Context::Lambda,
                    location: token.location,
                });
            }
            Token::In => {
                lexer.indent_levels.pop();
                if let Context::Block { needs_close: true, .. } = offside.context {
                    lexer.unprocessed_tokens.push(token);
                    return Ok(Token::CloseBlock);
                }
            }
            Token::Equal => {
                if offside.context == Context::Let {
                    scan_for_next_block(lexer,
                                        Context::Block {
                                            first: true,
                                            needs_close: true,
                                        });
                }
            }
            Token::RightArrow => {
                if offside.context == Context::MatchClause || offside.context == Context::Lambda {
                    if offside.context == Context::Lambda {
                        lexer.indent_levels.pop();
                    }
                    scan_for_next_block(lexer,
                                        Context::Block {
                                            first: true,
                                            needs_close: true,
                                        });
                }
            }
            Token::Then => {
                scan_for_next_block(lexer,
                                    Context::Block {
                                        first: true,
                                        needs_close: true,
                                    });
            }
            Token::OpenBrace => {
                scan_for_next_block(lexer, Context::Brace);
            }
            Token::OpenBracket => {
                scan_for_next_block(lexer, Context::Bracket);
            }
            Token::OpenParen => {
                scan_for_next_block(lexer, Context::Paren);
            }
            Token::Comma => {
                // Prevent a semi to be emitted before the next token
                if let Some(offside) = lexer.indent_levels.last_mut() {
                    // The enclosing block should not emit a block separator for the next
                    // expression
                    if let Context::Block { ref mut first, .. } = offside.context {
                        *first = true;
                    }
                }
            }
            Token::Of => scan_for_next_block(lexer, Context::MatchClause),
            _ => (),
        }
        return Ok(token.token);
    }
}

fn scan_for_next_block<'a, 's, I, Id, F>(lexer: &mut Lexer<'a, I, F>, context: Context)
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: AstId + Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug + 's
{
    let next = lexer.next_token();
    let location = next.location;
    lexer.unprocessed_tokens.push(next);
    if let Context::Block { needs_close: true, .. } = context {
        lexer.unprocessed_tokens.push(PToken {
            location: location,
            token: Token::OpenBlock,
        });
    }
    lexer.indent_levels.push(Offside {
        context: context,
        location: location,
    });
}

impl<'a, I, Id, F> Iterator for Lexer<'a, I, F>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: AstId + Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug
{
    type Item = Token<Id>;
    fn next(&mut self) -> Option<Token<Id>> {
        let token = self.next_token();
        match self.layout_independent_token(token) {
            Ok(Token::EOF) => None,
            Ok(token) => {
                debug!("Lex {:?}", token);
                Some(token)
            }
            Err(_unexpected_token) => {
                self.input.take();
                None
            }
        }
    }
}
