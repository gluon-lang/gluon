use std::fmt;

use base::pos::{self, BytePos, Column, Location, Span, Spanned};
use combine::primitives::{Error as CombineError, Info, RangeStream};

use lexer::{Error, Lexer};
use token::{Delimiter, SpannedToken, Token};

#[derive(Copy, Clone, Debug)]
struct Offside {
    location: Location,
    context: Context,
}

impl Offside {
    fn new(location: Location, context: Context) -> Offside {
        Offside {
            location: location,
            context: context,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
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

struct Contexts {
    stack: Vec<Offside>,
}

impl Contexts {
    fn new() -> Contexts {
        Contexts { stack: Vec::new() }
    }

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
        self.check_unindentation_limit(offside)?;
        self.stack.push(offside);
        Ok(())
    }

    fn check_unindentation_limit(&mut self, offside: Offside) -> Result<(), Error<'static>> {
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

pub struct Layout<'input, I>
    where I: RangeStream<Item = char, Range = &'input str>,
{
    lexer: Lexer<'input, I>,
    unprocessed_tokens: Vec<SpannedToken<'input>>,
    indent_levels: Contexts,
}

impl<'input, I> Layout<'input, I>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug + 'input,
{
    pub fn new(lexer: Lexer<'input, I>) -> Layout<'input, I> {
        Layout {
            lexer: lexer,
            unprocessed_tokens: Vec::new(),
            indent_levels: Contexts::new(),
        }
    }

    fn next_token(&mut self) -> SpannedToken<'input> {
        match self.unprocessed_tokens.pop() {
            Some(token) => token,
            None => self.lexer.next_token(),
        }
    }

    fn layout_token(&mut self,
                    token: SpannedToken<'input>,
                    layout_token: Token<'input>)
                    -> SpannedToken<'input> {
        let span = token.span;
        self.unprocessed_tokens.push(token);
        pos::spanned(span, layout_token)
    }

    fn scan_for_next_block(&mut self, context: Context) -> Result<(), Error<'input>> {
        let next = self.next_token();
        let span = next.span;
        self.unprocessed_tokens.push(next);
        if let Context::Block { .. } = context {
            self.unprocessed_tokens.push(SpannedToken {
                span: span,
                value: Token::OpenBlock,
            });
        }
        self.indent_levels.push(Offside::new(span.start, context))
    }

    fn layout_next_token(&mut self) -> Result<SpannedToken<'input>, Error<'input>> {
        use std::cmp::Ordering;

        let mut token = self.next_token();
        if token.value == Token::EOF {
            token.span.start.column = Column::from(0);
        }

        loop {
            // Retrieve the current indentation level if one exists
            let offside = match (&token.value, self.indent_levels.last().cloned()) {
                (_, Some(offside)) => offside,
                (&Token::EOF, None) => return Ok(token),
                (_, None) => {
                    let offside = Offside::new(token.span.start,
                                               Context::Block { emit_semi: false });
                    self.indent_levels.push(offside)?;
                    debug!("Default block {:?}", token);
                    return Ok(self.layout_token(token, Token::OpenBlock));
                }
            };

            debug!("--------\n{:?}\n{:?}", token, offside);

            match (&token.value, offside.context) {
                (&Token::Comma, Context::Delimiter(Delimiter::Brace)) |
                (&Token::Comma, Context::Delimiter(Delimiter::Bracket)) => return Ok(token),

                // If it is closing token we remove contexts until a context for that token is found
                (&Token::In, _) |
                (&Token::CloseBlock, _) |
                (&Token::Else, _) |
                (&Token::Close(_), _) |
                (&Token::Comma, _) => {
                    self.indent_levels.pop();

                    match (&token.value, offside.context) {
                        (&Token::Else, Context::If) => (),
                        (&Token::Close(close_delim), Context::Delimiter(context_delim))
                            if close_delim == context_delim => return Ok(token),
                        (&Token::CloseBlock, Context::Block { .. }) => {
                            if let Some(offside) = self.indent_levels.last_mut() {
                                // The enclosing block should not emit a block separator for the next
                                // expression
                                if let Context::Block { ref mut emit_semi, .. } = offside.context {
                                    *emit_semi = false;
                                }
                            }
                            return Ok(token);
                        }
                        (&Token::In, Context::Let) |
                        (&Token::In, Context::Type) => {
                            let location = {
                                let offside = self.indent_levels
                                    .last_mut()
                                    .expect("No top level block found");
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
                            let offside = Offside::new(location,
                                                       Context::Block { emit_semi: false });
                            self.indent_levels.push(offside)?;
                            self.unprocessed_tokens
                                .push(pos::spanned(token.span, Token::OpenBlock));

                            return Ok(token);
                        }
                        (_, Context::Block { .. }) => {
                            return Ok(self.layout_token(token, Token::CloseBlock));
                        }
                        (_, _) => continue,
                    }
                }
                (_, _) => (),
            }

            // Next we check offside rules for each of the contexts
            let ordering = token.span.start.column.cmp(&offside.location.column);
            match (offside.context, ordering) {
                (Context::Block { .. }, Ordering::Less) => {
                    self.unprocessed_tokens.push(token.clone());
                    token.value = Token::CloseBlock;
                    continue;
                }
                (Context::Block { emit_semi: true }, Ordering::Equal) => {
                    if let Some(offside) = self.indent_levels.last_mut() {
                        // The enclosing block should not emit a block separator for the
                        // next expression
                        if let Context::Block { ref mut emit_semi, .. } = offside.context {
                            *emit_semi = false;
                        }
                    }
                    return Ok(self.layout_token(token, Token::Semi));
                }
                (Context::Block { emit_semi: false }, Ordering::Equal) => {
                    match token.value {
                        Token::DocComment(_) |
                        Token::OpenBlock => (),
                        _ => {
                            // If it is the first token in a sequence we dont want to emit a
                            // separator
                            if let Some(offside) = self.indent_levels.last_mut() {
                                if let Context::Block { ref mut emit_semi, .. } = offside.context {
                                    *emit_semi = true;
                                }
                            }
                        }
                    }
                }
                (Context::Expr, _) |
                (Context::Lambda, _) => {
                    if ordering != Ordering::Greater {
                        self.indent_levels.pop();
                        continue;
                    }
                }
                (Context::MatchClause, _) => {
                    // Must allow `|` to be on the same line
                    if ordering == Ordering::Less ||
                       (ordering == Ordering::Equal && token.value != Token::Pipe) {
                        self.indent_levels.pop();
                        continue;
                    }
                }
                // `and` and `}` are allowed to be on the same line as the `let` or `type`
                (Context::Let, Ordering::Equal) |
                (Context::Type, Ordering::Equal) if token.value != Token::And &&
                                                    token.value !=
                                                    Token::Close(Delimiter::Brace) => {
                    // Insert an `in` token
                    self.indent_levels.pop();
                    let location = {
                        let offside =
                            self.indent_levels.last_mut().expect("No top level block found");
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut emit_semi, .. } = offside.context {
                            *emit_semi = false;
                        }
                        offside.location
                    };
                    let span = token.span;
                    let result = Ok(self.layout_token(token, Token::In));

                    // Inject a block to ensure that a sequence of expressions end up in the `let` body
                    // ```
                    // let x = 1
                    // a
                    // b
                    // ```
                    // `let x = 1 in {{ a; b }}` and not `{{ (let x = 1 in a) ; b }}`
                    let offside = Offside::new(location, Context::Block { emit_semi: false });
                    self.indent_levels.push(offside)?;
                    self.unprocessed_tokens.push(pos::spanned(span, Token::OpenBlock));

                    return result;
                }
                _ => (),
            }

            // Some tokens directly insert a new context when emitted
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
                let offside = Offside::new(token.span.start, context);
                return self.indent_levels.push(offside).map(move |()| token);
            }

            // For other tokens we need to scan for the next token to get its position
            match (&token.value, offside.context) {
                (&Token::In, context) => {
                    self.indent_levels.pop();
                    if let Context::Block { .. } = context {
                        return Ok(self.layout_token(token, Token::CloseBlock));
                    }
                }

                (&Token::Equals, Context::Let) |
                (&Token::RightArrow, Context::Lambda) |
                (&Token::RightArrow, Context::MatchClause) |
                (&Token::Then, _) => self.scan_for_next_block(Context::Block { emit_semi: false })?,
                (&Token::With, _) => self.scan_for_next_block(Context::MatchClause)?,

                (&Token::Else, _) => {
                    let next = self.next_token();
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
                    self.unprocessed_tokens.push(next);
                    if add_block {
                        self.scan_for_next_block(Context::Block { emit_semi: false })?;
                    }
                }
                (&Token::Comma, _) => {
                    // Prevent a semi to be emitted before the next token
                    if let Some(offside) = self.indent_levels.last_mut() {
                        // The enclosing block should not emit a block separator for the next
                        // expression
                        if let Context::Block { ref mut emit_semi, .. } = offside.context {
                            *emit_semi = false;
                        }
                    }
                }
                (_, _) => (),
            }

            return Ok(token);
        }
    }
}

// Converts an error into a static error by transforming any range arguments into strings
fn static_error<'input>(e: CombineError<Token<'input>, Token<'input>>)
                        -> CombineError<String, String> {
    let static_info = |i: Info<Token<'input>, Token<'input>>| {
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

impl<'input, I> Iterator for Layout<'input, I>
    where I: RangeStream<Item = char, Range = &'input str> + 'input,
          I::Range: fmt::Debug,
{
    type Item = Result<(BytePos, Token<'input>, BytePos), CombineError<String, String>>;

    fn next(&mut self)
            -> Option<Result<(BytePos, Token<'input>, BytePos), CombineError<String, String>>> {
        match self.layout_next_token() {
            Err(error) => Some(Err(static_error(error))),
            Ok(Spanned { value: Token::EOF, .. }) => None,
            Ok(token) => {
                debug!("Lex {:?}", token.value);
                let Span { start, end, .. } = token.span;
                Some(Ok((start.absolute, token.value, end.absolute)))
            }
        }
    }
}
