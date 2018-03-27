//! Module which contains types working with symbols
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::fmt;
use std::sync::Arc;
use std::borrow::Borrow;
use std::ops::Deref;

use ast::{DisplayEnv, IdentEnv};
use fnv::FnvMap;

// FIXME Don't have a double indirection (Arc + String)
/// A symbol uniquely identifies something regardless of its name and which module it originated
/// from
#[derive(Clone, Eq)]
pub struct Symbol(Arc<NameBuf>);

#[cfg(feature = "serde")]
mod serialization {
    use super::*;

    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use serde::de::DeserializeState;
    use serde::ser::SerializeState;
    use serialization::SeSeed;

    impl<'de> Deserialize<'de> for Symbol {
        fn deserialize<D>(deserializer: D) -> Result<Symbol, D::Error>
        where
            D: Deserializer<'de>,
        {
            use std::borrow::Cow;
            Cow::<str>::deserialize(deserializer).map(Symbol::from)
        }
    }

    impl<'de, Id, T> DeserializeState<'de, ::serialization::Seed<Id, T>> for Symbol {
        fn deserialize_state<D>(
            seed: &mut ::serialization::Seed<Id, T>,
            deserializer: D,
        ) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            use serde::de::DeserializeSeed;
            use serialization::SharedSeed;

            let seed = SharedSeed::new(seed);
            seed.deserialize(deserializer).map(Symbol)
        }
    }

    impl Serialize for Symbol {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let s: &str = self.as_ref();
            s.serialize(serializer)
        }
    }

    impl SerializeState<SeSeed> for Symbol {
        fn serialize_state<S>(&self, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            {
                ::serialization::shared::serialize(self, serializer, seed)
            }
        }
    }
}

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

impl<S> From<S> for Symbol
where
    S: Into<String>,
{
    fn from(name: S) -> Symbol {
        Symbol(Arc::new(NameBuf(name.into())))
    }
}

#[derive(Eq)]
#[cfg_attr(feature = "serde_derive", derive(SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
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

impl Symbol {
    pub fn strong_count(sym: &Symbol) -> usize {
        Arc::strong_count(&sym.0)
    }
}

impl SymbolRef {
    #[inline]
    pub fn new<N: ?Sized + AsRef<str>>(n: &N) -> &SymbolRef {
        unsafe { ::std::mem::transmute::<&Name, &SymbolRef>(Name::new(n)) }
    }

    /// Checks whether the names of two symbols are equal
    pub fn name_eq(&self, other: &SymbolRef) -> bool {
        self.name() == other.name()
    }

    pub fn name(&self) -> &Name {
        Name::new(&self.0)
    }

    /// Returns the name of this symbol as it was originally declared (strips location information
    /// and module information)
    pub fn declared_name(&self) -> &str {
        self.name().declared_name()
    }

    pub fn definition_name(&self) -> &str {
        self.name().definition_name()
    }

    pub fn is_global(&self) -> bool {
        self.0.chars().next() == Some('@')
    }

    fn ptr(&self) -> *const () {
        self.0.as_bytes().as_ptr() as *const ()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "S"))]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "S"))]
pub struct NameBuf(String);

#[derive(Debug, Eq, Hash)]
pub struct Name(str);

impl PartialEq for Name {
    fn eq(&self, other: &Name) -> bool {
        self.0.as_ptr() == other.0.as_ptr() || self.0 == other.0
    }
}

pub struct Components<'a>(&'a str);

impl<'a> Iterator for Components<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        if self.0.is_empty() {
            None
        } else {
            Some(match self.0.find('.') {
                Some(i) => {
                    let (before, after) = self.0.split_at(i);
                    self.0 = &after[1..];
                    before
                }
                None => {
                    let s = self.0;
                    self.0 = "";
                    s
                }
            })
        }
    }
}

impl Name {
    #[inline]
    pub fn new<N: ?Sized + AsRef<str>>(n: &N) -> &Name {
        unsafe { ::std::mem::transmute::<&str, &Name>(n.as_ref()) }
    }

    pub fn as_str(&self) -> &str {
        let name = &self.0;
        name.split(':').next().unwrap_or(name)
    }

    pub fn components(&self) -> Components {
        Components(&self.0)
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

    pub fn declared_name(&self) -> &str {
        let name = self.definition_name();
        name.rsplit('.').next().unwrap_or(name)
    }

    pub fn definition_name(&self) -> &str {
        let name = self.as_str().trim_left_matches('@');
        name.split(':').next().unwrap_or(name)
    }
}

impl NameBuf {
    #[inline]
    pub fn new<T>(name: T) -> NameBuf
    where
        T: Into<String>,
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

/// `Symbols` is a bidirectional mapping between `Symbol`s and their name as represented in a
/// source file.
/// Used to make identifiers within a single module point to the same symbol
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

    /// Looks up the symbol for `name` or creates a new symbol if it does not exist
    pub fn symbol<N>(&mut self, name: N) -> Symbol
    where
        N: Into<NameBuf> + AsRef<Name>,
    {
        if let Some(symbol) = self.indexes.get(name.as_ref()) {
            return symbol.clone();
        }
        self.make_symbol(name.into())
    }

    pub fn contains_name<N>(&mut self, name: N) -> bool
    where
        N: AsRef<Name>,
    {
        self.indexes.contains_key(name.as_ref())
    }

    pub fn len(&self) -> usize {
        self.strings.len()
    }
}

/// `SymbolModule` wraps a `Symbols` struct and adds a prefix to all symbols created by the
/// `symbol` method.
/// While this prefix does not affect the uniques of a `Symbol` in any way, it does make the origin
/// of a symbol clearer when pretty printing it
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

    /// Creates an unprefixed symbol, same as `Symbols::symbol`
    pub fn symbol<N>(&mut self, name: N) -> Symbol
    where
        N: Into<NameBuf> + AsRef<Name>,
    {
        self.symbols.symbol(name)
    }

    pub fn contains_name<N>(&mut self, name: N) -> bool
    where
        N: AsRef<Name>,
    {
        self.symbols.contains_name(name.as_ref())
    }

    /// Creates a symbol which is prefixed by the `module` argument passed in `new`
    ///
    /// ```
    /// # use gluon_base::symbol::{Symbols, SymbolModule};
    /// let mut symbols = Symbols::new();
    /// let mut symbols = SymbolModule::new(String::from("test"), &mut symbols);
    /// assert_eq!(symbols.symbol("a").as_ref(), "a");
    /// assert_eq!(symbols.scoped_symbol("a").as_ref(), "test.a");
    /// ```
    pub fn scoped_symbol(&mut self, name: &str) -> Symbol {
        let len = self.module.0.len();
        self.module.0.push('.');
        self.module.0.push_str(name);
        let symbol = self.symbols.symbol(&*self.module);
        self.module.0.truncate(len);
        symbol
    }

    pub fn module(&self) -> &Name {
        &self.module
    }

    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    pub fn symbols(&mut self) -> &mut Symbols {
        self.symbols
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

impl IdentEnv for Symbols {
    fn from_str(&mut self, s: &str) -> Symbol {
        self.symbol(s)
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
