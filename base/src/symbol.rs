use std::collections::HashMap;
use std::fmt;
use ast::{AstId, DisplayEnv, IdentEnv, ASTType};

use std::borrow::Borrow;
use std::ops::Deref;


#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Symbol(u32);

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
        Name::new(s.trim_right_matches("."))
    }

    pub fn name(&self) -> &Name {
        self.0.rfind('.')
            .map(|i| Name::new(&self.0[i+1..]))
            .unwrap_or(self)
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

impl <'a> From<&'a str> for NameBuf {
    fn from(name: &'a str) -> NameBuf {
        NameBuf(String::from(name))
    }
}

impl <'a> From<&'a Name> for NameBuf {
    fn from(name: &'a Name) -> NameBuf {
        NameBuf::from(&name.0)
    }
}

#[derive(Debug)]
pub struct Symbols {
    strings: Vec<NameBuf>,
    indexes: HashMap<NameBuf, Symbol>,
}

impl Symbols {
    pub fn new() -> Symbols {
        Symbols {
            strings: Vec::new(),
            indexes: HashMap::new(),
        }
    }

    pub fn make_symbol(&mut self, name: NameBuf) -> Symbol {
        let s = Symbol(self.strings.len() as u32);
        self.indexes.insert(name.clone(), s);
        self.strings.push(name);
        s
    }

    pub fn symbol<N>(&mut self, name: N) -> Symbol
        where N: Into<NameBuf> + AsRef<Name>
    {
        match self.indexes.get(name.as_ref()) {
            Some(symbol) => return *symbol,
            None => (),
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

    pub fn make_symbol(&mut self, name: String) -> Symbol {
        self.symbols.make_symbol(NameBuf::new(name))
    }

    pub fn symbol(&mut self, name: &str) -> Symbol {
        self.symbols.symbol(name)
    }

    pub fn make_scoped_symbol(&mut self, mut name: String) -> Symbol {
        let len = self.module.0.len();
        self.module.0.push('.');
        self.module.0.push_str(&name);
        name.clear();
        name.push_str(&self.module.0[..len]);
        ::std::mem::swap(&mut name, &mut self.module.0);
        self.symbols.make_symbol(NameBuf::new(name))
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
            .get(ident.0 as usize)
            .map(|name| &*name.0)
            .unwrap_or("<UNDEFINED>")
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
    fn set_type(&mut self, _: ASTType<Self::Untyped>) {}
}
