use base::ast::{DisplayEnv, IdentEnv, SpannedExpr};
use base::symbol::{Symbols, SymbolModule, Symbol, SymbolRef};
use base::types::{Alias, Generic, Kind, Type, KindEnv};
use base::types::{ArcType, TypeEnv, PrimitiveEnv, ArcKind, walk_move_type};
use check::typecheck::{self, Typecheck};
use parser;

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

pub fn parse_new(s: &str)
                 -> Result<SpannedExpr<Symbol>, (Option<SpannedExpr<Symbol>>, ::parser::Error)> {
    let symbols = get_local_interner();
    let mut symbols = symbols.borrow_mut();
    let mut module = SymbolModule::new("test".into(), &mut symbols);
    parser::parse_expr(&mut module, &s)
}

#[allow(dead_code)]
pub fn typecheck(text: &str) -> Result<ArcType, typecheck::Error> {
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
        let bool_ty = Type::app(Type::ident(bool_sym.clone()), vec![]);

        MockEnv { bool: Alias::new(bool_sym, vec![], bool_ty) }
    }
}

impl KindEnv for MockEnv {
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        match id.as_ref() {
            "Bool" => Some(Kind::typ()),
            _ => None,
        }
    }
}

impl TypeEnv for MockEnv {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        match id.as_ref() {
            "False" | "True" => Some(&self.bool.typ.as_ref().unwrap()),
            _ => None,
        }
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        match id.as_ref() {
            "Bool" => Some(&self.bool),
            _ => None,
        }
    }

    fn find_record(&self, _fields: &[Symbol]) -> Option<(&ArcType, &ArcType)> {
        None
    }
}

impl PrimitiveEnv for MockEnv {
    fn get_bool(&self) -> &ArcType {
        self.bool.typ.as_ref().unwrap()
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
    where T: AsRef<str> + for<'a> From<&'a str>,
{
    fn from_str(&mut self, s: &str) -> Self::Ident {
        T::from(s)
    }
}

pub fn typecheck_expr(text: &str) -> (SpannedExpr<Symbol>, Result<ArcType, typecheck::Error>) {
    let mut expr = parse_new(text).unwrap_or_else(|(_, err)| panic!("{}", err));

    let env = MockEnv::new();
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();
    let mut tc = Typecheck::new("test".into(), &mut interner, &env);

    let result = tc.typecheck_expr(&mut expr);

    (expr, result)
}

#[allow(dead_code)]
pub fn typecheck_partial_expr(text: &str)
                              -> (SpannedExpr<Symbol>, Result<ArcType, typecheck::Error>) {
    let mut expr = match parse_new(text) {
        Ok(e) => e,
        Err((Some(e), _)) => e,
        Err((None, err)) => panic!("{}", err),
    };

    let env = MockEnv::new();
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();
    let mut tc = Typecheck::new("test".into(), &mut interner, &env);

    let result = tc.typecheck_expr(&mut expr);

    (expr, result)
}

#[allow(dead_code)]
pub fn typ(s: &str) -> ArcType {
    assert!(s.len() != 0);
    typ_a(s, Vec::new())
}

pub fn typ_a<T>(s: &str, args: Vec<T>) -> T
    where T: From<Type<Symbol, T>>,
{
    assert!(s.len() != 0);

    match s.parse() {
        Ok(b) => Type::builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => {
            Type::generic(Generic {
                kind: Kind::typ(),
                id: intern(s),
            })
        }
        Err(()) => {
            if args.len() == 0 {
                Type::ident(intern(s))
            } else {
                Type::app(Type::ident(intern(s)), args)
            }
        }
    }
}

#[allow(dead_code)]
pub fn alias(s: &str, args: &[&str], typ: ArcType) -> ArcType {
    assert!(s.len() != 0);
    Type::alias(intern(s),
                args.iter()
                    .map(|id| {
                        Generic {
                            kind: Kind::typ(),
                            id: intern(id),
                        }
                    })
                    .collect(),
                typ)
}


/// Replace the variable at the `rest` part of a record for easier equality checks
#[allow(dead_code)]
pub fn close_record(typ: ArcType) -> ArcType {
    walk_move_type(typ,
                   &mut |typ| {
        match *typ {
            Type::ExtendRow { ref types, ref fields, ref rest } => {
                match **rest {
                    Type::ExtendRow { .. } => None,
                    _ => Some(Type::extend_row(types.clone(), fields.clone(), Type::empty_row())),
                }
            }
            _ => None,
        }
    })
}
