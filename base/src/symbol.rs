//! Module which contains types working with symbols
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::fmt;
use std::sync::Arc;
use std::borrow::Borrow;
use std::ops::Deref;

use ast::{AstId, DisplayEnv, IdentEnv, AstType};
use fnv::FnvMap;

// FIXME Don't have a double indirection (Arc + String)
#[derive(Clone, Eq)]
pub struct Symbol(Arc<NameBuf>);

impl Deref for Symbol {
    type Target = SymbolRef;
    fn deref(&self) -> &SymbolRef {
        let s: &str = self.0.as_str();
        unsafe { ::std::mem::transmute::<&str, &SymbolRef>(s) }
    }
}

impl Borrow<SymbolRef> for Symbol {
    fn borrow(&self) -> &SymbolRef {
        &**self
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.0.as_str()
    }
}


impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", &**self)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &**self)
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Symbol) -> bool {
        &**self == &**other
    }
}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Symbol) -> Option<Ordering> {
        (**self).partial_cmp(other)
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Symbol) -> Ordering {
        (**self).cmp(other)
    }
}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (**self).hash(h)
    }
}

impl Symbol {
    pub fn new(name: &str) -> Symbol {
        Symbol(Arc::new(NameBuf(String::from(name))))
    }
}

#[derive(Eq)]
pub struct SymbolRef(str);

impl fmt::Debug for SymbolRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:p}:{}", self, &self.0)
    }
}

impl fmt::Display for SymbolRef {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.0)
    }
}

impl PartialEq for SymbolRef {
    fn eq(&self, other: &SymbolRef) -> bool {
        self.ptr() == other.ptr()
    }
}

impl PartialOrd for SymbolRef {
    fn partial_cmp(&self, other: &SymbolRef) -> Option<Ordering> {
        self.ptr().partial_cmp(&other.ptr())
    }
}

impl Ord for SymbolRef {
    fn cmp(&self, other: &SymbolRef) -> Ordering {
        self.ptr().cmp(&other.ptr())
    }
}

impl Hash for SymbolRef {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.ptr().hash(h)
    }
}

impl AsRef<str> for SymbolRef {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl SymbolRef {
    /// Checks whether the names of two symbols are equal
    pub fn name_eq(&self, other: &SymbolRef) -> bool {
        self == other || self.0 == other.0
    }

    /// Returns the name of this symbol as it was originally declared (strips location information)
    pub fn declared_name(&self) -> &str {
        let name = self.as_ref();
        name.split(':').next().unwrap_or(name)
    }

    fn ptr(&self) -> *const () {
        self.0.as_bytes().as_ptr() as *const ()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct NameBuf(String);

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct Name(str);

pub struct Components<'a>(::std::str::Split<'a, char>);

impl<'a> Iterator for Components<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        self.0.next()
    }
}

impl Name {
    #[inline]
    pub fn new<N: ?Sized + AsRef<str>>(n: &N) -> &Name {
        unsafe { ::std::mem::transmute::<&str, &Name>(n.as_ref()) }
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn components(&self) -> Components {
        Components(self.0.split('.'))
    }

    pub fn module(&self) -> &Name {
        let s = self.0.trim_right_matches(|c| c != '.');
        Name::new(s.trim_right_matches('.'))
    }

    pub fn name(&self) -> &Name {
        self.0
            .rfind('.')
            .map_or(self, |i| Name::new(&self.0[i + 1..]))
    }
}

impl NameBuf {
    #[inline]
    pub fn new<T>(name: T) -> NameBuf
        where T: Into<String>
    {
        NameBuf(name.into())
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.0)
    }
}

impl fmt::Display for NameBuf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl AsRef<Name> for str {
    fn as_ref(&self) -> &Name {
        Name::new(self)
    }
}
impl AsRef<Name> for String {
    fn as_ref(&self) -> &Name {
        Name::new(self)
    }
}
impl AsRef<Name> for Name {
    fn as_ref(&self) -> &Name {
        self
    }
}

impl AsRef<str> for NameBuf {
    fn as_ref(&self) -> &str {
        &*self.0
    }
}

impl AsRef<Name> for NameBuf {
    fn as_ref(&self) -> &Name {
        self
    }
}

impl Borrow<Name> for NameBuf {
    fn borrow(&self) -> &Name {
        self
    }
}

impl Deref for NameBuf {
    type Target = Name;
    fn deref(&self) -> &Name {
        Name::new(self)
    }
}

impl<'a> From<&'a str> for NameBuf {
    fn from(name: &'a str) -> NameBuf {
        NameBuf(String::from(name))
    }
}

impl From<String> for NameBuf {
    fn from(name: String) -> NameBuf {
        NameBuf(name)
    }
}

impl<'a> From<&'a Name> for NameBuf {
    fn from(name: &'a Name) -> NameBuf {
        NameBuf::from(&name.0)
    }
}

#[derive(Debug, Default)]
pub struct Symbols {
    strings: FnvMap<Symbol, NameBuf>,
    indexes: FnvMap<NameBuf, Symbol>,
}

impl Symbols {
    pub fn new() -> Symbols {
        Symbols {
            strings: FnvMap::default(),
            indexes: FnvMap::default(),
        }
    }

    fn make_symbol(&mut self, name: NameBuf) -> Symbol {
        let s = Symbol(Arc::new(name.clone()));
        self.indexes.insert(name.clone(), s.clone());
        self.strings.insert(s.clone(), name);
        s
    }

    pub fn symbol<N>(&mut self, name: N) -> Symbol
        where N: Into<NameBuf> + AsRef<Name>
    {
        if let Some(symbol) = self.indexes.get(name.as_ref()) {
            return symbol.clone();
        }
        self.make_symbol(name.into())
    }
}

#[derive(Debug)]
pub struct SymbolModule<'a> {
    symbols: &'a mut Symbols,
    module: NameBuf,
}

impl<'a> SymbolModule<'a> {
    pub fn new(module: String, symbols: &'a mut Symbols) -> SymbolModule<'a> {
        SymbolModule {
            symbols: symbols,
            module: NameBuf(module),
        }
    }

    pub fn symbol<N>(&mut self, name: N) -> Symbol
        where N: Into<NameBuf> + AsRef<Name>
    {
        self.symbols.symbol(name)
    }

    pub fn scoped_symbol(&mut self, name: &str) -> Symbol {
        let len = self.module.0.len();
        self.module.0.push('.');
        self.module.0.push_str(name);
        let symbol = self.symbols.symbol(&*self.module);
        self.module.0.truncate(len);
        symbol
    }
}

impl DisplayEnv for Symbols {
    type Ident = Symbol;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        self.strings
            .get(ident)
            .map_or(ident.as_ref(), |name| &*name.0)
    }
}

impl<'s> DisplayEnv for SymbolModule<'s> {
    type Ident = Symbol;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        self.symbols.string(ident)
    }
}

impl<'a> IdentEnv for SymbolModule<'a> {
    fn from_str(&mut self, s: &str) -> Symbol {
        self.symbol(s)
    }
}

impl AstId for Symbol {
    type Untyped = Symbol;

    fn to_id(self) -> Symbol {
        self
    }
    fn set_type(&mut self, _: AstType<Self::Untyped>) {}
}
