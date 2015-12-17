use std::collections::HashMap;
use ast::{AstId, DisplayEnv, IdentEnv, ASTType};


#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct Symbol(u32);

#[derive(Debug)]
pub struct Symbols {
    strings: Vec<String>,
    indexes: HashMap<String, Symbol>,
}

impl Symbols {
    pub fn new() -> Symbols {
        Symbols {
            strings: Vec::new(),
            indexes: HashMap::new(),
        }
    }

    pub fn make_symbol(&mut self, string: String) -> Symbol {
        let s = Symbol(self.strings.len() as u32);
        self.indexes.insert(string.clone(), s);
        self.strings.push(string);
        s
    }

    pub fn symbol(&mut self, s: &str) -> Symbol {
        match self.indexes.get(s) {
            Some(symbol) => return *symbol,
            None => (),
        }
        self.make_symbol(String::from(s))
    }
}

impl DisplayEnv for Symbols {
    type Ident = Symbol;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        self.strings
            .get(ident.0 as usize)
            .map(|x| &**x)
            .unwrap_or("<UNDEFINED>")
    }
}

impl IdentEnv for Symbols {
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
