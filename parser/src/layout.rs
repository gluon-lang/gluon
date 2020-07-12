use crate::base::pos::{self, BytePos, Column, Line, Location, Span, Spanned};

use crate::token::{self, BorrowedToken, SpannedToken, Token};

quick_error! {
    #[derive(Debug, Eq, PartialEq, Hash, Clone)]
    pub enum Error {
        UnindentedTooFar {
            display("line was unindented too far")
        }
    }
}

type Result<T, E = Spanned<crate::Error, BytePos>> = std::result::Result<T, E>;

#[derive(Copy, Clone, Debug)]
struct Offside {
    location: Location,
    context: Context,
}

impl Offside {
    fn new(location: Location, context: Context) -> Offside {
        Offside { location, context }
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Context {
    /// Context which contains several expressions/declarations separated by semicolons
    Block { emit_semi: bool },
    /// After brace token
    Brace,
    /// After bracket token
    Bracket,
    /// After paren token
    Paren,
    /// A simple expression
    Expr,
    /// In a let expression
    Let,
    /// In a rec bloc
    Rec,
    /// In a type expression
    Type,
    /// In an if expression
    If,
    /// In a match clause
    MatchClause,
    /// In a lambda function
    Lambda,
    /// In an attribute
    Attribute,
}

#[derive(Debug)]
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

    fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    fn push(&mut self, offside: Offside) -> Result<()> {
        self.check_unindentation_limit(offside)?;
        self.stack.push(offside);
        Ok(())
    }

    fn check_unindentation_limit(&mut self, offside: Offside) -> Result<()> {
        let mut skip_block = false;
        for other_offside in self.stack.iter().rev() {
            match other_offside.context {
                Context::Lambda => {
                    skip_block = true;
                    continue;
                }
                Context::Block { .. } if skip_block => continue,
                Context::Brace | Context::Bracket | Context::Paren => return Ok(()),
                // New context should not be unindented past the closest enclosing block context
                Context::MatchClause
                | Context::Type
                | Context::Rec
                | Context::Let
                | Context::Block { .. }
                    if offside.location.column < other_offside.location.column =>
                {
                    ()
                }
                _ => continue,
            }
            debug!("Unindentation error: {:?} < {:?}", offside, other_offside);
            return Err(pos::spanned2(
                offside.location.absolute,
                offside.location.absolute,
                Error::UnindentedTooFar.into(),
            ));
        }
        Ok(())
    }
}

pub struct Layout<'input, Tokens> {
    tokens: Tokens,
    unprocessed_tokens: Vec<SpannedToken<'input>>,
    indent_levels: Contexts,
}

impl<'input, Tokens> Layout<'input, Tokens>
where
    Tokens: Iterator<Item = token::Result<SpannedToken<'input>>>,
{
    pub fn new(tokens: Tokens) -> Layout<'input, Tokens> {
        Layout {
            tokens,
            unprocessed_tokens: Vec::new(),
            indent_levels: Contexts::new(),
        }
    }

    fn continue_block(&mut self, context: Context, token: &BorrowedToken) -> Result<bool> {
        let in_rec = self.indent_levels.stack.len() >= 2
            && self.indent_levels.stack[self.indent_levels.stack.len() - 2].context == Context::Rec;

        Ok(in_rec
            && (context == Context::Attribute
                || (*token != Token::Rec && self.scan_continue_block(context, token)?)))
    }

    fn scan_continue_block(
        &mut self,
        context: Context,
        first_token: &BorrowedToken,
    ) -> Result<bool> {
        let expected_token = match context {
            Context::Let => Token::Let,
            Context::Type => Token::Type,
            _ => return Ok(false),
        };
        let mut in_attribute = false;
        for i in 0.. {
            let peek_token = if i == 0 {
                Some(first_token)
            } else {
                self.peek_token(i - 1)?.map(|t| &t.value)
            };
            if peek_token == Some(&expected_token) {
                return Ok(true);
            }
            match peek_token {
                Some(peek_token) => match peek_token {
                    Token::AttributeOpen => in_attribute = true,
                    Token::DocComment(..) => (),
                    Token::RBracket => in_attribute = false,
                    _ if !in_attribute => return Ok(false),
                    _ => (),
                },
                None => return Ok(false),
            }
        }
        Ok(false)
    }

    fn peek_token(&mut self, n: usize) -> Result<Option<&SpannedToken<'input>>> {
        for _ in self.unprocessed_tokens.len()..=n {
            let token = match self.tokens.next() {
                Some(token) => token.map_err(|err| {
                    pos::spanned2(
                        err.span.start().absolute,
                        err.span.end().absolute,
                        err.value.into(),
                    )
                })?,
                None => return Ok(None),
            };
            self.unprocessed_tokens.insert(0, token);
        }
        Ok(self.unprocessed_tokens.first())
    }

    fn next_token(&mut self) -> Result<SpannedToken<'input>> {
        self.unprocessed_tokens.pop().map(Ok).unwrap_or_else(|| {
            self.tokens
                .next()
                .unwrap_or_else(|| {
                    // Blegh
                    let location = Location {
                        line: Line::from(0),
                        column: Column::from(1),
                        absolute: BytePos::from(1),
                    };
                    Ok(pos::spanned2(location, location, Token::EOF))
                })
                .map_err(|err| {
                    pos::spanned2(
                        err.span.start().absolute,
                        err.span.end().absolute,
                        err.value.into(),
                    )
                })
        })
    }

    fn layout_token(
        &mut self,
        token: SpannedToken<'input>,
        layout_token: BorrowedToken<'input>,
    ) -> SpannedToken<'input> {
        let span = token.span;
        self.unprocessed_tokens.push(token);
        pos::spanned(span, layout_token)
    }

    fn scan_for_next_block(&mut self, context: Context) -> Result<()> {
        let next = self.next_token()?;
        let span = next.span;

        self.unprocessed_tokens.push(next);

        if let Context::Block { .. } = context {
            // If we find the next token at the same (or earlier) than the previous block we
            // can't insert a block but will instead emit an empty block
            // ```
            //     let test =
            //     1
            //  // ^~ Next token begins at or before the previous block
            // ```
            match self
                .indent_levels
                .stack
                .iter()
                .find(|last_offside| match last_offside.context {
                    Context::Block { .. } => true,
                    _ => false,
                })
                .map(|last_offside| last_offside.location.column)
            {
                Some(last_column) if span.start().column <= last_column => {
                    debug!(
                        "Inserting empty block due to {:?} <= {:?}",
                        self.indent_levels.last(),
                        span.start().column
                    );
                    self.unprocessed_tokens
                        .push(pos::spanned(span, Token::CloseBlock));
                    self.unprocessed_tokens
                        .push(pos::spanned(span, Token::OpenBlock));
                    return self.indent_levels.push(Offside::new(span.start(), context));
                }
                _ => (),
            }

            self.unprocessed_tokens
                .push(pos::spanned(span, Token::OpenBlock));
        }
        self.indent_levels.push(Offside::new(span.start(), context))
    }

    fn layout_next_token(&mut self) -> Result<SpannedToken<'input>> {
        use std::cmp::Ordering;

        let mut token = self.next_token()?;
        if token.value == Token::EOF {
            let mut start = token.span.start();
            start.column = Column::from(0);
            token.span = Span::new(start, token.span.end());

            if self.indent_levels.is_empty() {
                return Ok(token);
            }
        }

        loop {
            // Retrieve the current indentation level if one exists
            let offside = match (&token.value, self.indent_levels.last().cloned()) {
                (&Token::ShebangLine(_), _) => return Ok(token),
                (_, Some(offside)) => offside,
                (_, None) => {
                    let offside =
                        Offside::new(token.span.start(), Context::Block { emit_semi: false });
                    self.indent_levels.push(offside)?;
                    return Ok(self.layout_token(token, Token::OpenBlock));
                }
            };

            debug!("--------\n{:?}\n{:?}", token, offside);

            match (&token.value, offside.context) {
                (&Token::Comma, Context::Brace)
                | (&Token::Comma, Context::Paren)
                | (&Token::Comma, Context::Bracket) => return Ok(token),

                // If it is closing token we remove contexts until a context for that token is found
                (&Token::In, _)
                | (&Token::CloseBlock, _)
                | (&Token::Else, _)
                | (&Token::RBrace, _)
                | (&Token::RBracket, _)
                | (&Token::RParen, _)
                | (&Token::Comma, _) => {
                    self.indent_levels.pop();

                    // If none of the contexts would be closed by this token then this is likely a
                    // syntax error. Just return the token directly in that case to avoid an
                    // infinite loop caused by repeatedly inserting a default block and removing
                    // it.
                    if self
                        .indent_levels
                        .stack
                        .iter()
                        .all(|offside| !token_closes_context(&token.value, offside.context))
                    {
                        return Ok(token);
                    }

                    if token_closes_context(&token.value, offside.context) {
                        match offside.context {
                            Context::If => (),
                            Context::Brace
                            | Context::Bracket
                            | Context::Paren
                            | Context::Attribute => return Ok(token),
                            Context::Block { .. } if token.value == Token::CloseBlock => {
                                if let Some(offside) = self.indent_levels.last_mut() {
                                    // The enclosing block should not emit a block separator for the next
                                    // expression
                                    if let Context::Block {
                                        ref mut emit_semi, ..
                                    } = offside.context
                                    {
                                        *emit_semi = false;
                                    }
                                }
                                return Ok(token);
                            }
                            Context::Rec | Context::Let | Context::Type => {
                                let location = {
                                    let offside = self
                                        .indent_levels
                                        .last_mut()
                                        .expect("No top level block found");
                                    // The enclosing block should not emit a block separator for the next
                                    // expression
                                    if let Context::Block {
                                        ref mut emit_semi, ..
                                    } = offside.context
                                    {
                                        *emit_semi = false;
                                    }
                                    offside.location
                                };

                                if let Some(Context::Rec) =
                                    self.indent_levels.last().map(|offside| offside.context)
                                {
                                    self.indent_levels.pop();
                                }

                                // Inject a block to ensure that a sequence of expressions end up in the `let` body
                                // ```
                                // let x = 1
                                // a
                                // b
                                // ```
                                // `let x = 1 in {{ a; b }}` and not `{{ (let x = 1 in a) ; b }}`
                                let offside =
                                    Offside::new(location, Context::Block { emit_semi: false });
                                self.indent_levels.push(offside)?;
                                self.unprocessed_tokens
                                    .push(pos::spanned(token.span, Token::OpenBlock));

                                return Ok(token);
                            }
                            Context::Block { .. } => {
                                return Ok(self.layout_token(token, Token::CloseBlock));
                            }
                            _ => continue,
                        }
                    } else {
                        continue;
                    }
                }
                (_, _) => (),
            }

            // Next we check offside rules for each of the contexts
            let ordering = token.span.start().column.cmp(&offside.location.column);
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
                        if let Context::Block {
                            ref mut emit_semi, ..
                        } = offside.context
                        {
                            *emit_semi = false;
                        }
                    }
                    return Ok(self.layout_token(token, Token::Semi));
                }
                (Context::Block { emit_semi: false }, Ordering::Equal) => {
                    match token.value {
                        Token::AttributeOpen | Token::DocComment { .. } | Token::OpenBlock => (),
                        _ => {
                            // If it is the first token in a sequence we dont want to emit a
                            // separator
                            if let Some(offside) = self.indent_levels.last_mut() {
                                if let Context::Block {
                                    ref mut emit_semi, ..
                                } = offside.context
                                {
                                    *emit_semi = true;
                                }
                            }
                        }
                    }
                }
                (Context::Expr, _) | (Context::Lambda, _) => {
                    if ordering != Ordering::Greater {
                        self.indent_levels.pop();
                        continue;
                    }
                }
                (Context::MatchClause, _) => {
                    // Must allow `|` to be on the same line
                    if ordering == Ordering::Less
                        || (ordering == Ordering::Equal && token.value != Token::Pipe)
                    {
                        self.indent_levels.pop();
                        continue;
                    }
                }
                // `and` and `}` are allowed to be on the same line as the `let` or `type`
                (Context::Let, Ordering::Equal)
                | (Context::Let, Ordering::Less)
                | (Context::Type, Ordering::Equal)
                | (Context::Type, Ordering::Less)
                    if token.value != Token::RBrace =>
                {
                    if !self.continue_block(offside.context, &token.value)? {
                        if token.value == Token::EOF {
                            self.indent_levels.pop();
                            continue;
                        }
                        // Insert an `in` token
                        let let_location = self.indent_levels.pop().unwrap().location;
                        {
                            let offside = self
                                .indent_levels
                                .last_mut()
                                .expect("No top level block found");
                            // The enclosing block should not emit a block separator for the next
                            // expression
                            if let Context::Block {
                                ref mut emit_semi, ..
                            } = offside.context
                            {
                                *emit_semi = false;
                            }
                        }
                        if let Some(Context::Rec) =
                            self.indent_levels.last().map(|offside| offside.context)
                        {
                            self.indent_levels.pop();
                        }

                        let span = token.span;
                        let result = Ok(self.layout_token(token, Token::In));

                        // Inject a block to ensure that a sequence of expressions end up in the `let` body
                        // ```
                        // let x = 1
                        // a
                        // b
                        // ```
                        // `let x = 1 in {{ a; b }}` and not `{{ (let x = 1 in a) ; b }}`
                        let offside =
                            Offside::new(let_location, Context::Block { emit_semi: false });
                        self.indent_levels.push(offside)?;
                        self.unprocessed_tokens
                            .push(pos::spanned(span, Token::OpenBlock));

                        return result;
                    }
                }
                _ => (),
            }

            // Some tokens directly insert a new context when emitted
            let push_context = match token.value {
                Token::Rec => Some(Context::Rec),
                Token::Type => Some(Context::Type),
                Token::Let => Some(Context::Let),
                Token::Do | Token::Seq => Some(Context::Let),
                Token::If => Some(Context::If),
                Token::Match => Some(Context::Expr),
                Token::Lambda => Some(Context::Lambda),
                Token::LBrace => Some(Context::Brace),
                Token::LBracket => Some(Context::Bracket),
                Token::LParen => Some(Context::Paren),
                Token::AttributeOpen => Some(Context::Attribute),
                _ => None,
            };
            if let Some(context) = push_context {
                // When seeing `rec let` directly after each other (on the same line), use the
                // indentation level of the `rec`
                let pos = if offside.context == Context::Rec
                    && offside.location.line == token.span.start().line
                {
                    offside.location
                } else {
                    token.span.start()
                };
                if offside.context == context
                    && (offside.context == Context::Type || offside.context == Context::Let)
                    && (self.indent_levels.stack.len() >= 2
                        && self.indent_levels.stack[self.indent_levels.stack.len() - 2].context
                            == Context::Rec)
                {
                    self.indent_levels.pop();
                }

                let offside = Offside::new(pos, context);
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

                (&Token::Equals, Context::Let)
                | (&Token::RArrow, Context::Lambda)
                | (&Token::RArrow, Context::MatchClause)
                | (&Token::Then, _) => {
                    self.scan_for_next_block(Context::Block { emit_semi: false })?
                }
                (&Token::With, _) => self.scan_for_next_block(Context::MatchClause)?,

                (&Token::Else, _) => {
                    let next = self.next_token()?;
                    // Need to allow "else if" expressions so avoid inserting a block for those
                    // cases (A block would be inserted at column 5 and we would then get
                    // unindentation errors on the branches)
                    // if x then
                    //     1
                    // else if y then
                    //     2
                    // else
                    //     3
                    let add_block = next.value != Token::If
                        || next.span.start().line != token.span.start().line;
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
                        if let Context::Block {
                            ref mut emit_semi, ..
                        } = offside.context
                        {
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

fn token_closes_context(token: &BorrowedToken, context: Context) -> bool {
    match (token, context) {
        (&Token::Else, Context::If)
        | (&Token::RBrace, Context::Brace)
        | (&Token::RBracket, Context::Bracket)
        | (&Token::RParen, Context::Paren)
        | (&Token::CloseBlock, Context::Block { .. })
        | (&Token::In, Context::Rec)
        | (&Token::In, Context::Let)
        | (&Token::In, Context::Type)
        | (&Token::RBracket, Context::Attribute)
        | (_, Context::Block { .. }) => true,
        (_, _) => false,
    }
}

impl<'input, Tokens> Iterator for Layout<'input, Tokens>
where
    Tokens: Iterator<Item = token::Result<SpannedToken<'input>>>,
{
    type Item = Result<(BytePos, BorrowedToken<'input>, BytePos)>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.layout_next_token() {
            Ok(Spanned {
                value: Token::EOF, ..
            }) => None,
            token => Some(token.map(|token| {
                (
                    token.span.start().absolute,
                    token.value.into(),
                    token.span.end().absolute,
                )
            })),
        }
    }
}
