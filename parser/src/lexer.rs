use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt;
use std::rc::Rc;

use base::ast::*;

use combine::primitives::{Consumed, SourcePosition, Error as CombineError};
use combine::combinator::EnvParser;
use combine::*;
use combine_language::{LanguageEnv, LanguageDef, Identifier};

#[derive(Clone)]
pub struct BytePositioned<I> {
    position: usize,
    input: I
}

impl<I> StreamOnce for BytePositioned<I> where I : StreamOnce<Item = char> {
    type Item = I::Item;
    type Range = I::Range;
    type Position = usize;

    fn uncons(&mut self) -> Result<Self::Item, CombineError<Self::Item, Self::Range>> {
        self.input.uncons()
            .map(|c| {
                self.position += c.len_utf8();
                c
            })
    }

    fn position(&self) -> Self::Position {
        self.position
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
type LanguageParser<'a: 'b, 'b, I: 'b, F: 'b, T> = EnvParser<&'b Lexer<'a, I, F>, BytePositioned<I>, T>;

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

pub struct Lexer<'a, I, F>
    where I: Stream<Item = char>,
          F: IdentEnv
{
    pub env: LanguageEnv<'a, BytePositioned<I>>,
    pub make_ident: Rc<RefCell<F>>,
    pub input: Option<BytePositioned<I>>,
    pub unprocessed_tokens: Vec<PToken<F::Ident>>,
    pub indent_levels: Contexts,
    end_position: SourcePosition,
}

impl<'a, 's, I, Id, F> Lexer<'a, I, F>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug + 's
{
    pub fn new(input: I, make_ident: Rc<RefCell<F>>) -> Lexer<'a, I, F> {
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

        Lexer {
            env: env,
            make_ident: make_ident,
            input: Some(BytePositioned { position: 0, input : input }),
            unprocessed_tokens: Vec::new(),
            indent_levels: Contexts { stack: Vec::new() },
            end_position: SourcePosition {
                column: -1,
                line: -1,
            },
        }
    }

    fn intern(&self, s: &str) -> Id {
        self.make_ident.borrow_mut().from_str(s)
    }

    fn parser<T>(&'s self,
                 parser: fn(&Lexer<'a, I, F>, BytePositioned<I>) -> ParseResult<T, BytePositioned<I>>)
                 -> LanguageParser<'a, 's, I, F, T> {
        env_parser(self, parser)
    }

    /// Parses an operator
    fn op(&'s self) -> LanguageParser<'a, 's, I, F, Id> {
        self.parser(Lexer::parse_op)
    }

    fn parse_op(&self, input: BytePositioned<I>) -> ParseResult<Id, BytePositioned<I>> {
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
    fn parse_ident(&self, input: BytePositioned<I>) -> ParseResult<Token<Id>, BytePositioned<I>> {
        self.parser(Lexer::parse_ident2)
            .map(|x| Token::Identifier(x.0, x.1))
            .parse_state(input)
    }

    fn integer<'b>(&'b self) -> LanguageParser<'a, 'b, I, F, i64> {
        self.parser(Self::integer_)
    }

    fn integer_<'b>(&'b self, input: BytePositioned<I>) -> ParseResult<i64, BytePositioned<I>> {
        let (s, input) = try!(many1::<String, _>(digit()).parse_lazy(input));
        let mut n = 0;
        for c in s.chars() {
            n = n * 10 + (c as i64 - '0' as i64);
        }
        Ok((n, input))
    }

    /// Identifier parser which returns the identifier as well as the type of the identifier
    fn parse_ident2(&self, input: BytePositioned<I>) -> ParseResult<(Id, IdentType), BytePositioned<I>> {
        let id = self.env.identifier().map(|id| {
            let typ = if id.chars().next().unwrap().is_uppercase() {
                IdentType::Constructor
            } else {
                IdentType::Variable
            };
            (id, typ)
        });
        let op = self.env.parens(self.env.op()).map(|id| (id, IdentType::Operator));
        try(id)
            .or(try(op))
            .map(|(s, typ)| (self.intern(&s), typ))
            .parse_state(input)
    }

    fn layout_independent_token(&mut self, token: PToken<Id>) -> Result<Token<Id>, Error<Id>> {
        layout(self, token)
    }

    fn id_to_keyword(&self, id: Token<Id>) -> Token<Id> {
        let t = match id {
            Token::Identifier(ref id, _) => {
                match self.make_ident.borrow().string(&id) {
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
        let mut location = input.position();
        let result = self.next_token_(&mut location, input);
        match result {
            Ok((token, input)) => {
                self.input = Some(input.into_inner());
                PToken {
                    location: location,
                    token: token,
                }
            }
            Err(err) => {
                let err = err.into_inner();
                debug!("Error tokenizing: {:?}", err);
                self.end_position = err.position;
                PToken {
                    location: location,
                    token: Token::CloseBlock,
                }
            }
        }
    }

    fn next_token_(&mut self,
                   location: &mut usize,
                   mut input: BytePositioned<I>)
                   -> ParseResult<Token<Id>, BytePositioned<I>> {
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
                let ids = self.make_ident.borrow();
                let s = ids.string(&op);
                let tok = match s {
                    "=" => Token::Equal,
                    "->" => Token::RightArrow,
                    "|" => Token::Pipe,
                    _ => {
                        if s.starts_with("///") {
                            let mut comment = String::new();
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
                        } else if s.starts_with("/**") {
                            return self.block_doc_comment(input);
                        } else if s.starts_with("//") {
                            let ((), new_input) =
                                try!(skip_many(satisfy(|c| c != '\n' && c != '\r'))
                                    .parse_lazy(input));
                            input = new_input.into_inner();
                            continue;
                        } else if s.starts_with("/*") {
                            // Skip over normal comments and try to parse a new token
                            let ((), new_input) = try!(self.skip_block_comment(input));
                            input = new_input.into_inner();
                            continue;
                        } else {
                            Token::Operator(op.clone())
                        }
                    }
                };
                return Ok((tok, Consumed::Consumed(input)));
            } else if first.is_digit(10) {
                let int_or_byte = self.env.lex((self.integer(), optional(char('b'))));
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
                    .or(self.env.float().map(Token::Float))
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
                '"' => return self.env.string_literal().map(Token::String).parse_state(input),
                '\'' => return self.env.char_literal().map(Token::Char).parse_state(input),
                _ => Token::EOF,
            };
            return Ok((tok, one_char_consumed));
        }
    }

    fn skip_block_comment(&self, input: BytePositioned<I>) -> ParseResult<(), BytePositioned<I>> {
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
    fn block_doc_comment(&self, input: BytePositioned<I>) -> ParseResult<Token<Id>, BytePositioned<I>> {
        let mut block_doc_comment = parser(|input| {
            let mut input = Consumed::Empty(input);
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
}

fn layout<'a, I, Id, F>(lexer: &mut Lexer<'a, I, F>,
                        mut token: PToken<Id>)
                        -> Result<Token<Id>, Error<Id>>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug
{
    if token.token == Token::EOF {
        token.location.column = 0;
    }
    loop {
        // Retrieve the current indentation level if one exists
        let offside = match lexer.indent_levels.last().cloned() {
            Some(offside) => offside,
            None => {
                if token.token == Token::EOF {
                    return Ok(token.token);
                }
                try!(lexer.indent_levels.push(Offside {
                    context: Context::Block {
                        emit_semi: false,
                        needs_close: true,
                    },
                    location: token.location,
                }));
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
            Token::Close(Delimiter::Brace),
            Token::Close(Delimiter::Bracket),
            Token::Close(Delimiter::Paren),
            Token::Comma]
            .iter()
            .any(|t| *t == token.token) {

            if token.token == Token::Comma &&
               (offside.context == Context::Delimiter(Delimiter::Brace) ||
                offside.context == Context::Delimiter(Delimiter::Bracket)) {
                return Ok(token.token);
            }
            lexer.indent_levels.pop();
            match (&token.token, &offside.context) {
                (&Token::Else, &Context::If) => (),
                (&Token::Close(close_delim), &Context::Delimiter(context_delim))
                    if close_delim == context_delim => return Ok(token.token),
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
            Context::Block { emit_semi, needs_close } => {
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
                        match token.token {
                            _ if emit_semi => {
                                if let Some(offside) = lexer.indent_levels.last_mut() {
                                    // The enclosing block should not emit a block separator for the
                                    // next expression
                                    if let Context::Block { ref mut emit_semi, .. } =
                                           offside.context {
                                        *emit_semi = false;
                                    }
                                }
                                lexer.unprocessed_tokens.push(token);
                                return Ok(Token::Semi);
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
                   (ordering == Ordering::Equal && token.token != Token::Pipe) {
                    lexer.indent_levels.pop();
                    continue;
                }
            }
            Context::Let | Context::Type => {
                // `and` and `}` are allowed to be on the same line as the `let` or `type`
                if ordering == Ordering::Equal && token.token != Token::And &&
                   token.token != Token::Close(Delimiter::Brace) {
                    // Insert an `in` token
                    lexer.indent_levels.pop();
                    if let Some(offside) = lexer.indent_levels.last_mut() {
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut emit_semi, .. } = offside.context {
                            *emit_semi = false;
                        }
                    }
                    lexer.unprocessed_tokens.push(token);
                    return Ok(Token::In);
                }
            }
            _ => (),
        }
        // Some tokens directly inserts a new context when emitted
        let push_context = match token.token {
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
                context: context,
                location: token.location,
            };
            return lexer.indent_levels.push(offside).map(move |()| token.token);
        }
        // For other tokens we need to scan for the next token to get its position
        match token.token {
            Token::In => {
                lexer.indent_levels.pop();
                if let Context::Block { needs_close: true, .. } = offside.context {
                    lexer.unprocessed_tokens.push(token);
                    return Ok(Token::CloseBlock);
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
                let add_block = next.token != Token::If ||
                                next.location.line != token.location.line;
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
        return Ok(token.token);
    }
}

fn scan_for_next_block<'a, 's, I, Id, F>(lexer: &mut Lexer<'a, I, F>,
                                         context: Context)
                                         -> Result<(), Error<Id>>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: Clone + PartialEq + fmt::Debug,
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
    })
}

impl<'a, I, Id, F> StreamOnce for Lexer<'a, I, F>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: Clone + PartialEq + fmt::Debug,
          I::Range: fmt::Debug
{
    type Item = Token<Id>;
    type Range = Token<Id>;
    type Position = SourcePosition;

    fn uncons(&mut self) -> Result<Token<Id>, Error<Id>> {
        let token = self.next_token();
        match self.layout_independent_token(token) {
            Ok(Token::EOF) => Err(Error::end_of_input()),
            Ok(token) => {
                debug!("Lex {:?}", token);
                Ok(token)
            }
            Err(err) => {
                if let Some(input) = self.input.take() {
                    self.end_position = input.position();
                }
                Err(err)
            }
        }
    }

    fn position(&self) -> Self::Position {
        self.unprocessed_tokens
            .last()
            .map(|token| token.location.clone())
            .or_else(|| self.input.as_ref().map(|input| input.position.clone()))
            .unwrap_or_else(|| self.end_position.clone())
    }
}
