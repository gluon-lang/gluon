extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;

use base::ast;
use base::symbol::{Symbols, SymbolModule, Symbol};
use base::types::{Generic, Type, TcIdent, TcType, KindEnv, TypeEnv, PrimitiveEnv, Alias, RcKind,
                  Kind};

use check::typecheck::*;

use std::cell::RefCell;
use std::rc::Rc;

///Returns a reference to the interner stored in TLD
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

#[allow(dead_code)]
pub fn intern(s: &str) -> Symbol {
    let i = get_local_interner();
    let mut i = i.borrow_mut();
    if s.chars().next().map(|c| c.is_lowercase()).unwrap_or(false) {
        i.symbol(s)
    } else {
        SymbolModule::new("test".into(), &mut i).scoped_symbol(s)
    }
}

pub fn parse_new(s: &str) -> ast::LExpr<TcIdent> {
    let symbols = get_local_interner();
    let mut symbols = symbols.borrow_mut();
    let mut module = SymbolModule::new("test".into(), &mut symbols);
    let x = ::parser::parse_tc(&mut module, s).unwrap_or_else(|err| panic!("{:?}", err));
    x
}

#[allow(dead_code)]
pub fn typecheck(text: &str) -> Result<TcType, Error> {
    let (_, t) = typecheck_expr(text);
    t
}
struct EmptyEnv(Alias<Symbol, TcType>);
impl KindEnv for EmptyEnv {
    fn find_kind(&self, id: &Symbol) -> Option<RcKind> {
        match id.as_ref() {
            "Bool" => Some(Kind::star()),
            _ => None,
        }
    }
}
impl TypeEnv for EmptyEnv {
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
        match id.as_ref() {
            "False" | "True" => Some(&self.0.typ.as_ref().unwrap()),
            _ => None,
        }
    }
    fn find_type_info(&self, id: &Symbol) -> Option<&Alias<Symbol, TcType>> {
        match id.as_ref() {
            "Bool" => Some(&self.0),
            _ => None,
        }
    }
    fn find_record(&self, _fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        None
    }
}

impl PrimitiveEnv for EmptyEnv {
    fn get_bool(&self) -> &TcType {
        self.0.typ.as_ref().unwrap()
    }
}

pub fn typecheck_expr(text: &str) -> (ast::LExpr<TcIdent>, Result<TcType, Error>) {
    let mut expr = parse_new(text);
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();
    let bool_sym = interner.symbol("Bool");
    let bool = Type::<_, TcType>::data(Type::id(bool_sym.clone()), vec![]);
    let env = EmptyEnv(Alias::new(bool_sym, vec![], bool.clone()));
    let mut tc = Typecheck::new("test".into(), &mut interner, &env);
    let result = tc.typecheck_expr(&mut expr);
    (expr, result)
}

#[allow(dead_code)]
pub fn typ(s: &str) -> TcType {
    assert!(s.len() != 0);
    typ_a(s, Vec::new())
}

#[allow(dead_code)]
pub fn typ_a<T>(s: &str, args: Vec<T>) -> T
    where T: From<Type<Symbol, T>>
{
    assert!(s.len() != 0);
    let is_var = s.chars().next().unwrap().is_lowercase();
    match s.parse() {
        Ok(b) => Type::builtin(b),
        Err(()) if is_var => {
            Type::generic(Generic {
                kind: Kind::star(),
                id: intern(s),
            })
        }
        Err(()) => {
            if args.len() == 0 {
                Type::id(intern(s))
            } else {
                Type::data(Type::id(intern(s)), args)
            }
        }
    }
}

#[allow(dead_code)]
pub fn alias(s: &str, args: &[&str], typ: TcType) -> TcType {
    assert!(s.len() != 0);
    Type::alias(intern(s),
                args.iter()
                    .map(|id| {
                        Generic {
                            kind: Kind::star(),
                            id: intern(id),
                        }
                    })
                    .collect(),
                typ)
}
