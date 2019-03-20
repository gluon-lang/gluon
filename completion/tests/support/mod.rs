#![allow(unused)]

extern crate codespan;

use crate::base::{
    ast::SpannedExpr,
    error::InFile,
    kind::{ArcKind, Kind, KindEnv},
    metadata::{Metadata, MetadataEnv},
    pos::BytePos,
    symbol::{Symbol, SymbolModule, SymbolRef, Symbols},
    types::{
        self, Alias, ArcType, Generic, ModType, ModTypeRef, PrimitiveEnv, Type, TypeCache, TypeEnv,
    },
};

use crate::check::{
    metadata, rename,
    typecheck::{self, Typecheck},
};

use crate::parser::{parse_partial_expr, reparse_infix, ParseErrors};

use std::{cell::RefCell, rc::Rc, sync::Arc};

pub fn loc(src: &str, row: usize, column: usize) -> BytePos {
    codespan::FileMap::new("test".into(), src.to_string())
        .byte_index((row as u32).into(), (column as u32).into())
        .expect("Position is not in source")
}

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
    parse_partial_expr(&mut module, &TypeCache::new(), s)
}

pub struct MockEnv {
    bool: Alias<Symbol, ArcType>,
    int: ArcType,
}

impl MockEnv {
    pub fn new() -> MockEnv {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();

        let bool_sym = interner.symbol("Bool");
        let bool_ty = Type::app(Type::ident(bool_sym.clone()), collect![]);

        MockEnv {
            bool: Alias::new(bool_sym, Vec::new(), bool_ty),
            int: Type::int(),
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
    type Type = ArcType;

    fn find_type(&self, id: &SymbolRef) -> Option<ModTypeRef> {
        match id.definition_name() {
            "False" | "True" => Some(ModType::rigid(self.bool.as_type())),
            // Just need a dummy type that is not `Type::hole` to verify that lookups work
            "std.prelude" => Some(ModType::rigid(&self.int)),
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
        self.bool.as_type()
    }
}

impl MetadataEnv for MockEnv {
    fn get_metadata(&self, _id: &SymbolRef) -> Option<&Arc<Metadata>> {
        None
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

    rename::rename(
        &mut SymbolModule::new("test".into(), &mut interner),
        &mut expr,
    );
    let (_, mut metadata) = metadata::metadata(&env, &expr);

    let mut tc = Typecheck::new(
        "test".into(),
        &mut interner,
        &env,
        &TypeCache::new(),
        &mut metadata,
    );

    let result = tc.typecheck_expr_expected(&mut expr, expected);

    (
        expr,
        result.map_err(|err| {
            let mut source = codespan::CodeMap::new();
            source.add_filemap(codespan::FileName::virtual_("test"), text.into());
            InFile::new(source, err)
        }),
    )
}

pub fn typecheck_expr(
    text: &str,
) -> (
    SpannedExpr<Symbol>,
    Result<ArcType, InFile<typecheck::HelpError<Symbol>>>,
) {
    typecheck_expr_expected(text, None)
}

pub fn typecheck_partial_expr(
    text: &str,
) -> (
    SpannedExpr<Symbol>,
    Result<ArcType, InFile<typecheck::HelpError<Symbol>>>,
) {
    let mut expr = match parse_new(text) {
        Ok(e) | Err((Some(e), _)) => e,
        Err((None, err)) => panic!("{}", err),
    };

    let env = MockEnv::new();
    let interner = get_local_interner();
    let mut interner = interner.borrow_mut();

    rename::rename(
        &mut SymbolModule::new("test".into(), &mut interner),
        &mut expr,
    );
    let (_, mut metadata) = metadata::metadata(&env, &expr);
    reparse_infix(&metadata, &*interner, &mut expr).unwrap_or_else(|err| panic!("{}", err));

    let mut tc = Typecheck::new(
        "test".into(),
        &mut interner,
        &env,
        &TypeCache::new(),
        &mut metadata,
    );

    let result = tc.typecheck_expr(&mut expr);

    (
        expr,
        result.map_err(|err| {
            let mut source = codespan::CodeMap::new();
            source.add_filemap("test".into(), text.into());
            InFile::new(source, err)
        }),
    )
}

pub fn typ(s: &str) -> ArcType {
    assert!(!s.is_empty());
    typ_a(s, Vec::new())
}

pub fn typ_a<T>(s: &str, args: Vec<T>) -> T
where
    T: From<Type<Symbol, T>>,
{
    assert!(!s.is_empty());

    match s.parse() {
        Ok(b) => Type::builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => {
            Type::generic(Generic::new(intern(s), Kind::typ()))
        }
        Err(()) => {
            if args.is_empty() {
                Type::ident(intern(s))
            } else {
                Type::app(Type::ident(intern(s)), args.into_iter().collect())
            }
        }
    }
}

/// Replace the variable at the `rest` part of a record for easier equality checks
pub fn close_record(typ: ArcType) -> ArcType {
    types::walk_move_type(typ, &mut |typ: &ArcType| match **typ {
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
