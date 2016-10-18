//! Infix expressions in gluon are initially parsed as if they were all left-
//! associative with the same precedence. Therefore we need to rebalance them
//! after the fact.

use base::ast::{Expr, IdentEnv, Literal, MutVisitor, SpannedExpr, TypedIdent, walk_mut_expr};
use base::error::Errors;
use base::fnv::FnvMap;
use base::pos::{BytePos, spanned2};
use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ops::Index;

/// The fixity (associativity) of an infix operator
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Fixity {
    /// Left operator associativity.
    ///
    /// For example, when the `(~)` operator is left-associative:
    ///
    /// ```text
    /// x ~ y ~ z ≡ (x ~ y) ~ z
    /// ```
    Left,
    /// Right operator associativity.
    ///
    /// For example, when the `(~)` operator is right-associative:
    ///
    /// ```text
    /// x ~ y ~ z ≡ x ~ (y ~ z)
    /// ```
    Right,
}

impl fmt::Display for Fixity {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Fixity::Left => write!(f, "infixl"),
            Fixity::Right => write!(f, "infixr"),
        }
    }
}

/// Metadata pertaining to an infix operator
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct OpMeta {
    /// The precedence of the operator
    pub precedence: i32,
    /// The fixity of the operator
    pub fixity: Fixity,
}

impl OpMeta {
    fn new(precedence: i32, fixity: Fixity) -> OpMeta {
        OpMeta {
            precedence: precedence,
            fixity: fixity,
        }
    }
}

impl fmt::Display for OpMeta {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self.fixity, self.precedence)
    }
}

/// A table of operator metadata
pub struct OpTable {
    pub operators: FnvMap<String, OpMeta>,
    pub default_meta: OpMeta,
}

impl OpTable {
    fn new<I>(ops: I) -> OpTable
        where I: IntoIterator<Item = (&'static str, OpMeta)>,
    {
        OpTable {
            operators: ops.into_iter().map(|(name, op)| (name.to_string(), op)).collect(),
            default_meta: OpMeta::new(9, Fixity::Left),
        }
    }
}

impl Default for OpTable {
    fn default() -> OpTable {
        OpTable::new(vec![
            ("*", OpMeta::new(7, Fixity::Left)),
            ("/", OpMeta::new(7, Fixity::Left)),
            ("%", OpMeta::new(7, Fixity::Left)),
            ("+", OpMeta::new(6, Fixity::Left)),
            ("-", OpMeta::new(6, Fixity::Left)),
            (":", OpMeta::new(5, Fixity::Right)),
            ("++", OpMeta::new(5, Fixity::Right)),
            ("&&", OpMeta::new(3, Fixity::Right)),
            ("||", OpMeta::new(2, Fixity::Right)),
            ("$", OpMeta::new(0, Fixity::Right)),
            ("==", OpMeta::new(4, Fixity::Left)),
            ("/=", OpMeta::new(4, Fixity::Left)),
            ("<", OpMeta::new(4, Fixity::Left)),
            (">", OpMeta::new(4, Fixity::Left)),
            ("<=", OpMeta::new(4, Fixity::Left)),
            (">=", OpMeta::new(4, Fixity::Left)),
            // Hack for some library operators
            ("<<", OpMeta::new(9, Fixity::Right)),
            (">>", OpMeta::new(9, Fixity::Left)),
            ("<|", OpMeta::new(0, Fixity::Right)),
            ("|>", OpMeta::new(0, Fixity::Left)),
        ])
    }
}

impl<'a> Index<&'a str> for OpTable {
    type Output = OpMeta;

    fn index(&self, name: &'a str) -> &OpMeta {
        self.operators.get(name).unwrap_or_else(|| {
            if name.starts_with("#") {
                &self[name[1..].trim_left_matches(char::is_alphanumeric)]
            } else {
                &self.default_meta
            }
        })
    }
}

pub struct Reparser<'s, Id: 's> {
    operators: OpTable,
    symbols: &'s IdentEnv<Ident = Id>,
    errors: Errors<ReparseError>,
    _marker: PhantomData<Id>,
}

impl<'s, Id> Reparser<'s, Id> {
    pub fn new(operators: OpTable, symbols: &'s IdentEnv<Ident = Id>) -> Reparser<'s, Id> {
        Reparser {
            operators: operators,
            symbols: symbols,
            errors: Errors::new(),
            _marker: PhantomData,
        }
    }

    pub fn reparse(&mut self, expr: &mut SpannedExpr<Id>) -> Result<(), Errors<ReparseError>> {
        self.visit_expr(expr);
        if self.errors.has_errors() {
            Err(mem::replace(&mut self.errors, Errors::new()))
        } else {
            Ok(())
        }
    }
}

impl<'s, Id> MutVisitor for Reparser<'s, Id> {
    type Ident = Id;

    fn visit_expr(&mut self, e: &mut SpannedExpr<Self::Ident>) {
        if let Expr::Infix(..) = e.value {
            let dummy = spanned2(BytePos::from(0),
                                 BytePos::from(0),
                                 Expr::Literal(Literal::Int(0)));
            let expr = mem::replace(e, dummy);
            match reparse(expr, self.symbols, &self.operators) {
                Ok(expr) => {
                    *e = expr;
                }
                Err(err) => self.errors.error(err),
            }
        }
        walk_mut_expr(self, e);
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ReparseError {
    ConflictingFixities((String, OpMeta), (String, OpMeta)),
}

impl fmt::Display for ReparseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::ReparseError::*;

        match *self {
            ConflictingFixities((ref lhs_name, lhs_meta), (ref rhs_name, rhs_meta)) => {
                try!(write!(f, "Conflicting fixities at the same precedence level. "));
                write!(f,
                       "left: `{} {}`, right: `{} {}`",
                       lhs_meta,
                       lhs_name,
                       rhs_meta,
                       rhs_name)
            }
        }
    }
}

impl Error for ReparseError {
    fn description(&self) -> &str {
        "Conflicting fixities at the same precedence level"
    }
}

/// Reconstruct the infix expression using the correct associativities
/// and precedences.
///
/// Inspired by [`Language.Haskell.Infix`].
///
/// [`Language.Haskell.Infix`]: https://hackage.haskell.org/package/infix-0.1.1/docs/src/Language-Haskell-Infix.html
pub fn reparse<Id>(expr: SpannedExpr<Id>,
                   symbols: &IdentEnv<Ident = Id>,
                   operators: &OpTable)
                   -> Result<SpannedExpr<Id>, ReparseError> {
    use base::pos;
    use self::ReparseError::*;

    let make_op = |lhs: Box<SpannedExpr<Id>>, op, rhs: Box<SpannedExpr<Id>>| {
        let span = pos::span(lhs.span.start, rhs.span.end);
        Box::new(pos::spanned(span, Expr::Infix(lhs, op, rhs)))
    };

    let mut infixes = Infixes::new(expr);
    let mut arg_stack = Vec::new();
    let mut op_stack = Vec::new();

    while let Some(token) = infixes.next() {
        match token {
            InfixToken::Arg(next_expr) => arg_stack.push(next_expr),
            InfixToken::Op(next_op) => {
                let stack_op = match op_stack.pop() {
                    Some(stack_op) => stack_op,
                    None => {
                        op_stack.push(next_op);
                        continue;
                    }
                };

                let next_op_meta = operators[symbols.string(&next_op.name)];
                let stack_op_meta = operators[symbols.string(&stack_op.name)];

                match i32::cmp(&next_op_meta.precedence, &stack_op_meta.precedence) {
                    // Reduce
                    Ordering::Less => {
                        let rhs = arg_stack.pop().unwrap();
                        let lhs = arg_stack.pop().unwrap();

                        infixes.next_op = Some(next_op);
                        arg_stack.push(make_op(lhs, stack_op, rhs));
                    }
                    // Shift
                    Ordering::Greater => {
                        op_stack.push(stack_op);
                        op_stack.push(next_op);
                    }
                    Ordering::Equal => {
                        match (next_op_meta.fixity, stack_op_meta.fixity) {
                            // Reduce
                            (Fixity::Left, Fixity::Left) => {
                                let rhs = arg_stack.pop().unwrap();
                                let lhs = arg_stack.pop().unwrap();

                                infixes.next_op = Some(next_op);
                                arg_stack.push(make_op(lhs, stack_op, rhs));
                            }
                            // Shift
                            (Fixity::Right, Fixity::Right) => {
                                op_stack.push(stack_op);
                                op_stack.push(next_op);
                            }
                            // Conflicting fixities at the same precedence level!
                            (Fixity::Left, Fixity::Right) |
                            (Fixity::Right, Fixity::Left) => {
                                let next_op_name = symbols.string(&next_op.name).to_string();
                                let stack_op_name = symbols.string(&stack_op.name).to_string();

                                // TODO: Return a spanned error
                                return Err(ConflictingFixities((stack_op_name, stack_op_meta),
                                                               (next_op_name, next_op_meta)));
                            }
                        }
                    }
                }
            }
        }
    }

    for op in op_stack.into_iter().rev() {
        let rhs = arg_stack.pop().unwrap();
        let lhs = arg_stack.pop().unwrap();
        arg_stack.push(make_op(lhs, op, rhs));
    }

    assert_eq!(arg_stack.len(), 1);

    Ok(*arg_stack.pop().unwrap())
}

#[derive(Debug, Clone, PartialEq)]
enum InfixToken<Id> {
    Arg(Box<SpannedExpr<Id>>),
    // TODO: Make this spanned to allow for accurate error reporting
    Op(TypedIdent<Id>),
}

/// An iterator that takes an expression that has had its operators grouped
/// with _right associativity_, and yeilds a sequence of `InfixToken`s. This
/// is useful for reparsing the operators with their correct associativies
/// and precedences.
///
/// For example, the expression:
///
/// ```text
/// (1 + (2 ^ (4 * (6 - 8))))
/// ```
///
/// Will result in the following iterations:
///
/// ```text
/// Arg:  1
/// Op:   +
/// Arg:  2
/// Op:   ^
/// Arg:  4
/// Op:   *
/// Arg:  6
/// Op:   -
/// Arg:  8
/// ```
struct Infixes<Id> {
    /// The next part of the expression that we need to flatten
    remaining_expr: Option<Box<SpannedExpr<Id>>>,
    /// Cached operator from a previous iteration
    next_op: Option<TypedIdent<Id>>,
}

impl<Id> Infixes<Id> {
    fn new(expr: SpannedExpr<Id>) -> Infixes<Id> {
        Infixes {
            remaining_expr: Some(Box::new(expr)),
            next_op: None,
        }
    }
}

impl<Id> Iterator for Infixes<Id> {
    type Item = InfixToken<Id>;

    fn next(&mut self) -> Option<InfixToken<Id>> {
        if let Some(op) = self.next_op.take() {
            return Some(InfixToken::Op(op));
        }

        self.remaining_expr.take().map(|expr| {
            let expr = *expr; // Workaround for http://stackoverflow.com/questions/28466809/
            match expr.value {
                Expr::Infix(lhs, op, rhs) => {
                    self.remaining_expr = Some(rhs);
                    self.next_op = Some(op);
                    InfixToken::Arg(lhs)
                }
                _ => InfixToken::Arg(Box::new(expr)), // FIXME: remove reallocation?
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use base::ast::{DisplayEnv, Expr, IdentEnv, Literal, SpannedExpr, TypedIdent};
    use base::pos::{self, BytePos, Spanned};
    use std::marker::PhantomData;

    use super::{Fixity, Infixes, InfixToken, OpMeta, OpTable, reparse};
    use super::ReparseError::*;

    pub struct MockEnv<T>(PhantomData<T>);

    impl<T> MockEnv<T> {
        pub fn new() -> MockEnv<T> {
            MockEnv(PhantomData)
        }
    }

    impl<T: AsRef<str>> DisplayEnv for MockEnv<T> {
        type Ident = T;

        fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
            ident.as_ref()
        }
    }

    impl<T> IdentEnv for MockEnv<T>
        where T: AsRef<str> + for<'a> From<&'a str>,
    {
        fn from_str(&mut self, s: &str) -> Self::Ident {
            T::from(s)
        }
    }


    fn no_loc<T>(value: T) -> Spanned<T, BytePos> {
        pos::spanned2(BytePos::from(0), BytePos::from(0), value)
    }

    fn ident(name: &str) -> TypedIdent<String> {
        TypedIdent::new(name.to_string())
    }

    fn op(lhs: Box<SpannedExpr<String>>,
          op_str: &str,
          rhs: Box<SpannedExpr<String>>)
          -> Box<SpannedExpr<String>> {
        Box::new(no_loc(Expr::Infix(lhs, ident(op_str), rhs)))
    }

    fn int(value: i64) -> Box<SpannedExpr<String>> {
        Box::new(no_loc(Expr::Literal(Literal::Int(value))))
    }

    #[test]
    fn infixes() {
        let expr = op(int(1),
                      "+",
                      op(int(2), "^", op(int(4), "*", op(int(6), "-", int(8)))));

        let result: Vec<_> = Infixes::new(*expr).collect();
        let expected = vec![InfixToken::Arg(int(1)),
                            InfixToken::Op(ident("+")),
                            InfixToken::Arg(int(2)),
                            InfixToken::Op(ident("^")),
                            InfixToken::Arg(int(4)),
                            InfixToken::Op(ident("*")),
                            InfixToken::Arg(int(6)),
                            InfixToken::Op(ident("-")),
                            InfixToken::Arg(int(8))];

        assert_eq!(result, expected);
    }

    #[test]
    fn reparse_single() {
        let env = MockEnv::new();
        let ops = OpTable::new(vec![]);

        let expr = *op(int(1), "+", int(2));
        let expected = Ok(expr.clone());

        assert_eq!(reparse(expr, &env, &ops), expected);
    }

    #[test]
    fn reparse_less_precedence() {
        let env = MockEnv::new();
        let ops = OpTable::new(vec![
            ("*", OpMeta::new(7, Fixity::Left)),
            ("+", OpMeta::new(6, Fixity::Left)),
        ]);

        // 1 + (2 * 8)
        let expr = *op(int(1), "+", op(int(2), "*", int(8)));
        let expected = Ok(expr.clone());

        assert_eq!(reparse(expr, &env, &ops), expected);
    }

    #[test]
    fn reparse_greater_precedence() {
        let env = MockEnv::new();
        let ops = OpTable::new(vec![
            ("*", OpMeta::new(7, Fixity::Left)),
            ("+", OpMeta::new(6, Fixity::Left)),
        ]);

        // 1 * (2 + 8)
        let expr = *op(int(1), "*", op(int(2), "+", int(8)));
        // (1 * 2) + 8
        let expected = Ok(*op(op(int(1), "*", int(2)), "+", int(8)));

        assert_eq!(reparse(expr, &env, &ops), expected);
    }

    #[test]
    fn reparse_equal_precedence_left_fixity() {
        let env = MockEnv::new();
        let ops = OpTable::new(vec![
            ("-", OpMeta::new(6, Fixity::Left)),
            ("+", OpMeta::new(6, Fixity::Left)),
        ]);

        // 1 + (2 - 8)
        let expr = *op(int(1), "+", op(int(2), "-", int(8)));
        // (1 + 2) - 8
        let expected = Ok(*op(op(int(1), "+", int(2)), "-", int(8)));

        assert_eq!(reparse(expr, &env, &ops), expected);
    }

    #[test]
    fn reparse_equal_precedence_right_fixity() {
        let env = MockEnv::new();
        let ops = OpTable::new(vec![
            ("-", OpMeta::new(6, Fixity::Right)),
            ("+", OpMeta::new(6, Fixity::Right)),
        ]);

        // 1 + (2 - 8)
        let expr = *op(int(1), "+", op(int(2), "-", int(8)));
        let expected = Ok(expr.clone());

        assert_eq!(reparse(expr, &env, &ops), expected);
    }

    #[test]
    fn reparse_mixed_precedences_mixed_fixities() {
        let env = MockEnv::new();
        let ops = OpTable::new(vec![
            ("*", OpMeta::new(7, Fixity::Left)),
            ("-", OpMeta::new(6, Fixity::Left)),
            ("+", OpMeta::new(6, Fixity::Left)),
        ]);

        //  1  + (2  * (6   -  8))
        let expr = *op(int(1), "+", op(int(2), "*", op(int(6), "-", int(8))));
        // (1  + (2  *  6)) -  8
        let expected = Ok(*op(op(int(1), "+", op(int(2), "*", int(6))), "-", int(8)));

        assert_eq!(reparse(expr, &env, &ops), expected);
    }

    #[test]
    fn reparse_equal_precedence_conflicting_fixities() {
        let env = MockEnv::new();
        let ops = OpTable::new(vec![
            ("|>", OpMeta::new(5, Fixity::Left)),
            ("<|", OpMeta::new(5, Fixity::Right)),
        ]);

        // 1 |> (2 <| 8)
        let expr = *op(int(1), "|>", op(int(2), "<|", int(8)));
        let expected = Err(ConflictingFixities(("|>".to_string(), OpMeta::new(5, Fixity::Left)),
                                               ("<|".to_string(), OpMeta::new(5, Fixity::Right))));

        assert_eq!(reparse(expr, &env, &ops), expected);
    }

    #[test]
    fn reparse_equal_precedence_conflicting_fixities_nested() {
        let env = MockEnv::new();
        let ops = OpTable::new(vec![
            ("|>", OpMeta::new(5, Fixity::Left)),
            ("<|", OpMeta::new(5, Fixity::Right)),
        ]);

        // 1 + (1 |> (2 <| 8))
        let expr = *op(int(1), "+", op(int(1), "|>", op(int(2), "<|", int(8))));
        let expected = Err(ConflictingFixities(("|>".to_string(), OpMeta::new(5, Fixity::Left)),
                                               ("<|".to_string(), OpMeta::new(5, Fixity::Right))));

        assert_eq!(reparse(expr, &env, &ops), expected);
    }
}
