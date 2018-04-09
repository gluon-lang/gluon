#![allow(unused_macros)]

use base::ast::{DisplayEnv, IdentEnv, SpannedExpr};
use base::error::InFile;
use base::kind::{ArcKind, Kind, KindEnv};
use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Symbol, SymbolModule, SymbolRef, Symbols};
use base::types::{self, Alias, ArcType, Generic, PrimitiveEnv, Type, TypeCache,
                  TypeEnv};

use check::typecheck::{self, Typecheck};
use parser::{parse_partial_expr, ParseErrors};

use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

/// Returns a reference to the interner stored in TLD
pub fn get_local_interner() -> Rc<RefCell<Symbols>> {
    thread_local!(static INTERNER: Rc<RefCell<Symbols>>
    = Rc::new(RefCell::new(Symbols::new())));

    INTERNER.with(|interner| interner.clone())
}

#[allow(dead_code)]
pub fn intern_unscoped(s: &str) -> Symbol {
    let i = get_local_interner();
    let mut i = i.borrow_mut();

    i.symbol(s)
}

pub fn intern(s: &str) -> Symbol {
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();

    if s.starts_with(char::is_lowercase) {
        interner.symbol(s)
    } else {
        SymbolModule::new("test".into(), &mut interner).scoped_symbol(s)
    }
}

pub fn parse_new(
    s: &str,
) -> Result<SpannedExpr<Symbol>, (Option<SpannedExpr<Symbol>>, ParseErrors)> {
    let symbols = get_local_interner();
    let mut symbols = symbols.borrow_mut();
    let mut module = SymbolModule::new("test".into(), &mut symbols);
    parse_partial_expr(&mut module, &TypeCache::new(), &s)
}

#[allow(dead_code)]
pub fn typecheck(text: &str) -> Result<ArcType, InFile<typecheck::HelpError<Symbol>>> {
    let (_, t) = typecheck_expr(text);
    t
}

pub struct MockEnv {
    bool: Alias<Symbol, ArcType>,
}

impl MockEnv {
    pub fn new() -> MockEnv {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();

        let bool_sym = interner.symbol("Bool");
        let bool_ty = Type::app(Type::ident(bool_sym.clone()), collect![]);

        MockEnv {
            bool: Alias::new(bool_sym, bool_ty),
        }
    }
}

impl KindEnv for MockEnv {
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        match id.definition_name() {
            "Bool" => Some(Kind::typ()),
            _ => None,
        }
    }
}

impl TypeEnv for MockEnv {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        match id.definition_name() {
            "False" | "True" => Some(&self.bool.as_type()),
            _ => None,
        }
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        match id.definition_name() {
            "Bool" => Some(&self.bool),
            _ => None,
        }
    }
}

impl PrimitiveEnv for MockEnv {
    fn get_bool(&self) -> &ArcType {
        &self.bool.as_type()
    }
}

impl MetadataEnv for MockEnv {
    fn get_metadata(&self, _id: &SymbolRef) -> Option<&Metadata> {
        None
    }
}

#[allow(dead_code)]
pub struct MockIdentEnv<T>(PhantomData<T>);

#[allow(dead_code)]
impl<T> MockIdentEnv<T> {
    pub fn new() -> MockIdentEnv<T> {
        MockIdentEnv(PhantomData)
    }
}

impl<T: AsRef<str>> DisplayEnv for MockIdentEnv<T> {
    type Ident = T;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        ident.as_ref()
    }
}

impl<T> IdentEnv for MockIdentEnv<T>
where
    T: AsRef<str> + for<'a> From<&'a str>,
{
    fn from_str(&mut self, s: &str) -> Self::Ident {
        T::from(s)
    }
}

pub fn typecheck_expr_expected(
    text: &str,
    expected: Option<&ArcType>,
) -> (
    SpannedExpr<Symbol>,
    Result<ArcType, InFile<typecheck::HelpError<Symbol>>>,
) {
    let mut expr = parse_new(text).unwrap_or_else(|(_, err)| panic!("{}", err));

    let env = MockEnv::new();
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();
    let mut tc = Typecheck::new("test".into(), &mut interner, &env, TypeCache::new());

    let result = tc.typecheck_expr_expected(&mut expr, expected);

    (expr, result.map_err(|err| InFile::new("test", text, err)))
}

pub fn typecheck_expr(
    text: &str,
) -> (
    SpannedExpr<Symbol>,
    Result<ArcType, InFile<typecheck::HelpError<Symbol>>>,
) {
    typecheck_expr_expected(text, None)
}

#[allow(dead_code)]
pub fn typecheck_partial_expr(
    text: &str,
) -> (
    SpannedExpr<Symbol>,
    Result<ArcType, InFile<typecheck::HelpError<Symbol>>>,
) {
    let mut expr = match parse_new(text) {
        Ok(e) => e,
        Err((Some(e), _)) => e,
        Err((None, err)) => panic!("{}", err),
    };

    let env = MockEnv::new();
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();
    let mut tc = Typecheck::new("test".into(), &mut interner, &env, TypeCache::new());

    let result = tc.typecheck_expr(&mut expr);

    (expr, result.map_err(|err| InFile::new("test", text, err)))
}

#[allow(dead_code)]
pub fn typ(s: &str) -> ArcType {
    assert!(s.len() != 0);
    typ_a(s, Vec::new())
}

pub fn typ_a<T>(s: &str, args: Vec<T>) -> T
where
    T: From<Type<Symbol, T>>,
{
    assert!(s.len() != 0);

    match s.parse() {
        Ok(b) => Type::builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => {
            Type::generic(Generic::new(intern(s), Kind::typ()))
        }
        Err(()) => if args.len() == 0 {
            Type::ident(intern(s))
        } else {
            Type::app(Type::ident(intern(s)), args.into_iter().collect())
        },
    }
}

#[allow(dead_code)]
pub fn alias(s: &str, args: &[&str], typ: ArcType) -> ArcType {
    assert!(s.len() != 0);
    Type::alias(
        intern(s),
        Type::forall(
            args.iter()
                .map(|id| Generic::new(intern(id), Kind::typ()))
                .collect(),
            typ,
        ),
    )
}

/// Replace the variable at the `rest` part of a record for easier equality checks
#[allow(dead_code)]
pub fn close_record(typ: ArcType) -> ArcType {
    types::walk_move_type(typ, &mut |typ| match **typ {
        Type::ExtendRow {
            ref types,
            ref fields,
            ref rest,
        } => match **rest {
            Type::ExtendRow { .. } => None,
            _ => Some(Type::extend_row(
                types.clone(),
                fields.clone(),
                Type::empty_row(),
            )),
        },
        _ => None,
    })
}

#[macro_export]
macro_rules! assert_failed {
    ($lhs:expr, $rhs:expr, $lhs_value:expr, $rhs_value:expr) => {

        panic!(
            r#"Assertion failed: `({} == {})`
        left: `{}`,
        right: `{}`"#,
            stringify!($lhs),
            stringify!($rhs),
            $lhs_value,
            $rhs_value
        )
    };
}

#[macro_export]
macro_rules! assert_req {
    ($lhs:expr, $rhs:expr) => {

        match ($lhs, $rhs) {
            (Ok(lhs), Ok(rhs)) => {
                if lhs != rhs {
                    assert_failed!($lhs, $rhs, lhs, rhs)
                }
            }
            (Err(lhs), Err(rhs)) => {
                if lhs != rhs {
                    assert_failed!($lhs, $rhs, lhs, rhs)
                }
            }
            (Ok(lhs), Err(rhs)) => assert_failed!($lhs, $rhs, lhs, rhs),
            (Err(lhs), Ok(rhs)) => assert_failed!($lhs, $rhs, lhs, rhs),
        }
    };
}

macro_rules! test_check {
    ($name:ident, $source:expr, $typ:expr) => {
        #[test]
        fn $name() {
            let _ = env_logger::try_init();

            let text = $source;
            let result = support::typecheck(text);

            assert_req!(result.map(|x| x.to_string()), Ok($typ.to_string()));
        }
    };
}

macro_rules! assert_err {
    ($e: expr, $($id: pat),+) => {{
        #[allow(unused_imports)]
        use check::typecheck::TypeError::*;
        #[allow(unused_imports)]
        use check::unify::Error::{TypeMismatch, Substitution, Other};
        #[allow(unused_imports)]
        use check::substitution::Error::Occurs;
        #[allow(unused_imports)]
        use check::unify_type::TypeError::FieldMismatch;

        match $e {
            Ok(x) => assert!(false, "Expected error, got {}", x),
            Err(err) => {
                let errors = err.errors();
                let mut iter = (&errors).into_iter();
                $(
                match iter.next() {
                    Some(&::base::pos::Spanned { value: ::base::error::Help { error: $id, .. }, .. }) => (),
                    _ => assert!(false, "Found errors:\n{}\nbut expected {}",
                                        errors, stringify!($id)),
                }
                )+
                assert!(iter.count() == 0, "Found more errors than expected\n{}", errors);
            }
        }
    }}
}

macro_rules! count {
    ($e: pat) => {
        1
    };
    ($e: pat, $($id: pat),+) => {
        1 + count!($($id),+)
    }
}

macro_rules! assert_unify_err {
    ($e: expr, $($id: pat),+) => {
        assert_multi_unify_err!($e, [$($id),+])
    }
}

macro_rules! assert_multi_unify_err {
    ($e: expr, $( [ $( $id: pat ),+ ] ),+) => {{
        use check::typecheck::TypeError::*;
        #[allow(unused_imports)]
        use check::unify::Error::{TypeMismatch, Substitution, Other};
        #[allow(unused_imports)]
        use check::substitution::Error::Occurs;
        #[allow(unused_imports)]
        use check::unify_type::TypeError::{FieldMismatch, SelfRecursiveAlias, MissingFields};

        match $e {
            Ok(x) => assert!(false, "Expected error, got {}", x),
            Err(err) => {
                let errors = err.errors();
                let mut errors_iter = (&errors).into_iter().enumerate();
                $(
                match errors_iter.next() {
                    Some((i, error)) => {
                        match error.value.error {
                            Unification(_, _, ref errors) => {
                                let mut iter = errors.iter();
                                let expected_count = count!($($id),+);
                                $(
                                match iter.next() {
                                    Some(&$id) => (),
                                    Some(error2) => {
                                        assert!(false,
                                            "Found errors at {}:\n{}\nExpected:\n{}\nFound\n:{:?}",
                                            i,
                                            error,
                                            stringify!($id),
                                            error2
                                        );
                                    }
                                    None => {
                                        assert!(false,
                                            "Found {} errors but expected {} than expected at {}.\n\
                                            Errors:\n{}\nbut expected {}",
                                            errors.len(),
                                            expected_count,
                                            i,
                                            error,
                                            stringify!($id)
                                        );
                                    }
                                }
                                )+
                                let count = iter.count();
                                assert!(count == 0,
                                        "Found {} more errors than expected at {}\n{}",
                                        count,
                                        i,
                                        error);
                            }
                            _ => assert!(false,
                                        "Found errors at {}:\n\
                                        {}\nbut expected an unification error",
                                        i,
                                        error)
                        }
                    }
                    None => ()
                }
                )+
                assert!(errors_iter.count() == 0,
                        "Found more unification errors than expected\n{}",
                        errors);
            }
        }
    }}
}
