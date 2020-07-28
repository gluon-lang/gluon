#![allow(unused)]

use std::{fmt, iter::FromIterator};

use crate::base::{
    ast::RootExpr,
    error::{Errors, InFile},
    kind::{ArcKind, Kind, KindEnv},
    metadata::{Metadata, MetadataEnv},
    pos::{BytePos, Spanned},
    source::{self, Source},
    symbol::{Name, Symbol, SymbolData, SymbolModule, SymbolRef, Symbols},
    types::{
        self, Alias, ArcType, Generic, KindedIdent, PrimitiveEnv, Type, TypeCache, TypeEnv,
        TypeExt, TypePtr,
    },
};

use crate::check::{
    metadata, rename,
    typecheck::{self, Typecheck},
};

use crate::parser::{parse_partial_root_expr, reparse_infix, ParseErrors};

use std::{cell::RefCell, rc::Rc, sync::Arc};

#[path = "../../../check/tests/support/mod.rs"]
mod check_support;

pub use self::check_support::*;

pub fn loc(src: &str, row: usize, column: usize) -> BytePos {
    source::FileMap::new("test".into(), src.to_string())
        .byte_index((row as u32).into(), (column as u32).into())
        .expect("Position is not in source")
}

pub(crate) fn in_file_error<E>(text: &str, errors: Errors<Spanned<E, BytePos>>) -> InFile<E>
where
    E: fmt::Display,
{
    let mut source = source::CodeMap::new();
    source.add_filemap("test".into(), text.into());
    InFile::new(source, errors)
}

pub fn parse_new(s: &str) -> Result<RootExpr<Symbol>, (Option<RootExpr<Symbol>>, ParseErrors)> {
    let symbols = get_local_interner();
    let mut symbols = symbols.borrow_mut();
    let mut module = SymbolModule::new("test".into(), &mut symbols);
    parse_partial_root_expr(&mut module, &TypeCache::new(), s)
}

pub struct MockEnv {
    bool: Alias<Symbol, ArcType>,
    int: ArcType,
}

impl MockEnv {
    pub fn new() -> MockEnv {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();

        let bool_sym = interner.simple_symbol("Bool");
        let bool_ty = Type::app(Type::ident(KindedIdent::new(bool_sym.clone())), collect![]);

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

    fn find_type(&self, id: &SymbolRef) -> Option<ArcType> {
        match id.definition_name() {
            "False" | "True" => Some(self.bool.as_type().clone()),
            // Just need a dummy type that is not `Type::hole` to verify that lookups work
            "std.prelude" => Some(self.int.clone()),
            _ => None,
        }
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        match id.definition_name() {
            "Bool" => Some(self.bool.clone()),
            _ => None,
        }
    }
}

impl PrimitiveEnv for MockEnv {
    fn get_bool(&self) -> ArcType {
        self.bool.as_type().clone()
    }
}

impl MetadataEnv for MockEnv {
    fn get_metadata(&self, _id: &SymbolRef) -> Option<Arc<Metadata>> {
        None
    }
}

pub fn typ(s: &str) -> ArcType {
    assert!(!s.is_empty());
    typ_a(s, Vec::new())
}

pub fn typ_a<T>(s: &str, args: Vec<T>) -> T
where
    T: TypeExt<Id = Symbol, SpannedId = Symbol> + From<Type<Symbol, T>>,
    T::Types: FromIterator<T> + Default + Extend<T>,
{
    assert!(!s.is_empty());

    match s.parse() {
        Ok(b) => Type::builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => {
            Type::generic(Generic::new(intern(s), Kind::typ()))
        }
        Err(()) => {
            if args.is_empty() {
                Type::ident(KindedIdent::new(intern(s)))
            } else {
                Type::app(
                    Type::ident(KindedIdent::new(intern(s))),
                    args.into_iter().collect(),
                )
            }
        }
    }
}

/// Replace the variable at the `rest` part of a record for easier equality checks
pub fn close_record(typ: ArcType) -> ArcType {
    types::walk_move_type(typ, &mut |typ: &ArcType| match **typ {
        Type::ExtendRow {
            ref fields,
            ref rest,
        } => match **rest {
            Type::ExtendRow { .. } => None,
            _ => Some(Type::extend_row(fields.clone(), Type::empty_row())),
        },
        _ => None,
    })
}
