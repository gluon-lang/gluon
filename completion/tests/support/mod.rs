use base::ast::SpannedExpr;
use base::error::InFile;
use base::kind::{ArcKind, Kind, KindEnv};
use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Symbol, SymbolModule, SymbolRef, Symbols};
use base::types::{self, Alias, ArcType, Generic, PrimitiveEnv, RecordSelector, Type, TypeCache,
                  TypeEnv};
use check::typecheck::{self, Typecheck};
use parser::{parse_partial_expr, ParseErrors};

use std::cell::RefCell;
use std::rc::Rc;

/// Returns a reference to the interner stored in TLD
pub fn get_local_interner() -> Rc<RefCell<Symbols>> {
    thread_local!(static INTERNER: Rc<RefCell<Symbols>>
    = Rc::new(RefCell::new(Symbols::new())));

    INTERNER.with(|interner| interner.clone())
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
        match id.as_ref() {
            "Bool" => Some(Kind::typ()),
            _ => None,
        }
    }
}

impl TypeEnv for MockEnv {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        match id.as_ref() {
            "False" | "True" => Some(&self.bool.as_type()),
            _ => None,
        }
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        match id.as_ref() {
            "Bool" => Some(&self.bool),
            _ => None,
        }
    }

    fn find_record(
        &self,
        _fields: &[Symbol],
        _selector: RecordSelector,
    ) -> Option<(ArcType, ArcType)> {
        None
    }
}

impl PrimitiveEnv for MockEnv {
    fn get_bool(&self) -> &ArcType {
        &self.bool.as_type()
    }
}

impl MetadataEnv for MockEnv {
    fn get_metadata(&self, _id: &Symbol) -> Option<&Metadata> {
        None
    }
}


pub fn typecheck_expr_expected(
    text: &str,
    expected: Option<&ArcType>,
) -> (
    SpannedExpr<Symbol>,
    Result<ArcType, InFile<typecheck::TypeError<Symbol>>>,
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
    Result<ArcType, InFile<typecheck::TypeError<Symbol>>>,
) {
    typecheck_expr_expected(text, None)
}

pub fn typecheck_partial_expr(
    text: &str,
) -> (
    SpannedExpr<Symbol>,
    Result<ArcType, InFile<typecheck::TypeError<Symbol>>>,
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


/// Replace the variable at the `rest` part of a record for easier equality checks
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
