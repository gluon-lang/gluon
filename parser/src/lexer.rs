use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use base::ast::*;

use combine::primitives::{Stream, SourcePosition, Positioner};
use combine::combinator::EnvParser;
use combine::*;
use combine_language::LanguageEnv;

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
        }
    }
}

impl<Id> Positioner for Token<Id> where Id: PartialEq
{
    type Position = SourcePosition;
    fn start() -> Self::Position {
        char::start()
    }
    fn update(&self, _position: &mut Self::Position) {}
}

/// Parser passes the environment to each parser function
type LanguageParser<'a: 'b, 'b, I: 'b, F: 'b, T> = EnvParser<&'b Lexer<'a, I, F>, I, T>;

pub struct Lexer<'a, I, F>
    where I: Stream<Item = char>
{
    pub env: LanguageEnv<'a, I>,
    pub make_ident: Rc<RefCell<F>>,
    pub input: Option<State<I>>,
}

impl<'a, 's, I, Id, F> Lexer<'a, I, F>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: AstId + Clone,
          I::Range: fmt::Debug + 's
{

    pub fn skip_whitespace(&mut self) {
        if let Some(input) = self.input.take() {
            self.input = Some(spaces().parse_lazy(input).unwrap().1.into_inner());
        }
    }

    fn intern(&self, s: &str) -> Id {
        self.make_ident.borrow_mut().from_str(s)
    }

    fn parser<T>(&'s self,
                 parser: fn(&Lexer<'a, I, F>, State<I>) -> ParseResult<T, I>)
                 -> LanguageParser<'a, 's, I, F, T> {
        env_parser(self, parser)
    }

    ///Parses an operator
    fn op(&'s self) -> LanguageParser<'a, 's, I, F, Id> {
        self.parser(Lexer::parse_op)
    }

    fn parse_op(&self, input: State<I>) -> ParseResult<Id, I> {
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
    fn parse_ident(&self, input: State<I>) -> ParseResult<Token<Id>, I> {
        self.parser(Lexer::parse_ident2)
            .map(|x| Token::Identifier(x.0, x.1))
            .parse_state(input)
    }

    /// Identifier parser which returns `(id, true)` if the identifier is a constructor
    /// (Starts with an uppercase letter
    fn parse_ident2(&self, input: State<I>) -> ParseResult<(Id, bool), I> {
        try(self.env.identifier())
            .or(try(self.env.parens(self.env.op())))
            .map(|s| {
                debug!("Id: {}", s);
                (self.intern(&s), s.chars().next().unwrap().is_uppercase())
            })
            .parse_state(input)
    }
}

impl<'a, I, Id, F> Iterator for Lexer<'a, I, F>
    where I: Stream<Item = char> + 'a,
          F: IdentEnv<Ident = Id>,
          Id: AstId + Clone + fmt::Debug,
          I::Range: fmt::Debug
{
    type Item = Token<Id>;
    fn next(&mut self) -> Option<Token<Id>> {
        let input = match self.input.take() {
            Some(input) => input,
            None => return None,
        };
        let result = self.env
                         .lex(choice::<[&mut Parser<Input = I, Output = Token<Id>>; 28],
                                       _>([&mut self.env.reserved("let").map(|_| Token::Let),
                                           &mut self.env.reserved("type").map(|_| Token::Type),
                                           &mut self.env.reserved("and").map(|_| Token::And),
                                           &mut self.env.reserved("in").map(|_| Token::In),
                                           &mut self.env.reserved("case").map(|_| Token::Case),
                                           &mut self.env.reserved("of").map(|_| Token::Of),
                                           &mut self.env.reserved("if").map(|_| Token::If),
                                           &mut self.env.reserved("then").map(|_| Token::Then),
                                           &mut self.env.reserved("else").map(|_| Token::Else),
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
                                           &mut self.ident(),
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
                         .parse_state(input);
        match result {
            Ok((token, input)) => {
                debug!("TOKEN {:?}", token);
                self.input = Some(input.into_inner());
                Some(token)
            }
            Err(_err) => None,
        }
    }
}
