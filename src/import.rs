//! Implementation of the `import` macro.
use std::any::Any;
use std::collections::HashMap;
use std::sync::{Arc, RwLock, Mutex};
use std::fs::File;
use std::io;
use std::io::Read;
use std::path::{Path, PathBuf};

use base::ast;
use base::metadata::Metadata;
use base::symbol::Symbol;
use vm::macros::{Macro, Error as MacroError};
use vm::thread::{Thread, ThreadInternal};
use vm::internal::Value;
use super::{filename_to_module, Compiler};
use base::types::TcIdent;


quick_error! {
    /// Error type for the import macro
    #[derive(Debug)]
    pub enum Error {
        /// The importer found a cyclic dependency when loading files
        CyclicDependency(module: String) {
            description("Cyclic dependency")
            display("Module '{}' occurs in a cyclic dependency", module)
        }
        /// Generic message error
        String(message: String) {
            description(message)
            display("{}", message)
        }
        /// The importer could not load the imported file
        IO(err: io::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
    }
}

macro_rules! std_libs {
    ($($file: expr),*) => {
        [$((concat!("std/", $file, ".glu"), include_str!(concat!("../std/", $file, ".glu")))),*]
    }
}
// Include the standard library distribution in the binary
static STD_LIBS: [(&'static str, &'static str); 8] = std_libs!("prelude",
                                                               "types",
                                                               "map",
                                                               "repl",
                                                               "string",
                                                               "state",
                                                               "test",
                                                               "writer");

pub trait Importer: Any + Clone + Sync + Send {
    fn import(&self, vm: &Thread, modulename: &str, input: &str) -> Result<(), MacroError>;
}

#[derive(Clone)]
pub struct DefaultImporter;
impl Importer for DefaultImporter {
    fn import(&self, vm: &Thread, modulename: &str, input: &str) -> Result<(), MacroError> {
        let mut compiler = Compiler::new().implicit_prelude(modulename != "std.types");
        try!(compiler.load_script(vm, &modulename, input));
        Ok(())
    }
}

#[derive(Clone)]
pub struct CheckImporter(pub Arc<Mutex<HashMap<String, ast::LExpr<ast::TcIdent<Symbol>>>>>);
impl CheckImporter {
    pub fn new() -> CheckImporter {
        CheckImporter(Arc::new(Mutex::new(HashMap::new())))
    }
}
impl Importer for CheckImporter {
    fn import(&self, vm: &Thread, modulename: &str, input: &str) -> Result<(), MacroError> {
        use compiler_pipeline::*;
        let mut compiler = Compiler::new().implicit_prelude(modulename != "std.types");
        let TypecheckValue(expr, typ) = try!(input.typecheck(&mut compiler, vm, modulename, input));
        self.0.lock().unwrap().insert(modulename.into(), expr);
        let metadata = Metadata::default();
        // Insert a global to ensure the globals type can be looked up
        try!(vm.global_env().set_global(Symbol::new(modulename), typ, metadata, Value::Int(0)));
        Ok(())
    }
}

/// Macro which rewrites occurances of `import "filename"` to a load of that file if it is not
/// already loaded and then a global access to the loaded module
pub struct Import<I = DefaultImporter> {
    visited: RwLock<Vec<String>>,
    paths: RwLock<Vec<PathBuf>>,
    pub importer: I,
}

impl<I> Import<I> {
    /// Creates a new import macro
    pub fn new(importer: I) -> Import<I> {
        Import {
            visited: RwLock::new(Vec::new()),
            paths: RwLock::new(vec![PathBuf::from(".")]),
            importer: importer,
        }
    }

    /// Adds a path to the list of paths which the importer uses to find files
    pub fn add_path<P: Into<PathBuf>>(&self, path: P) {
        self.paths.write().unwrap().push(path.into());
    }
}

impl<I> Macro for Import<I>
    where I: Importer
{
    fn expand(&self,
              vm: &Thread,
              arguments: &mut [ast::LExpr<TcIdent>])
              -> Result<ast::LExpr<TcIdent>, MacroError> {
        if arguments.len() != 1 {
            return Err(Error::String("Expected import to get 1 argument".into()).into());
        }
        match *arguments[0] {
            ast::Expr::Literal(ast::LiteralEnum::String(ref filename)) => {
                let modulename = filename_to_module(filename);
                let path = Path::new(&filename[..]);
                // Only load the script if it is not already loaded
                let name = Symbol::new(&*modulename);
                debug!("Import '{}' {:?}", modulename, self.visited);
                if !vm.global_env().global_exists(&modulename) {
                    if self.visited.read().unwrap().iter().any(|m| **m == **filename) {
                        return Err(Error::CyclicDependency(filename.clone()).into());
                    }
                    self.visited.write().unwrap().push(filename.clone());
                    let mut buffer = String::new();
                    let file_contents = match STD_LIBS.iter().find(|tup| tup.0 == filename) {
                        Some(tup) => tup.1,
                        None => {
                            let file = self.paths
                                           .read()
                                           .unwrap()
                                           .iter()
                                           .filter_map(|p| {
                                               let mut base = p.clone();
                                               base.push(path);
                                               match File::open(&base) {
                                                   Ok(file) => Some(file),
                                                   Err(_) => None,
                                               }
                                           })
                                           .next();
                            let mut file = try!(file.ok_or_else(|| {
                                Error::String(format!("Could not find file '{}'", filename))
                            }));
                            try!(file.read_to_string(&mut buffer));
                            &*buffer
                        }
                    };
                    // FIXME Remove this hack
                    self.visited.write().unwrap().pop();
                    try!(self.importer.import(vm, &modulename, file_contents));
                }
                // FIXME Does not handle shadowing
                Ok(ast::located(arguments[0].location,
                                ast::Expr::Identifier(TcIdent::new(name))))
            }
            _ => return Err(Error::String("Expected a string literal to import".into()).into()),
        }
    }

    fn clone(&self) -> Box<Macro> {
        Box::new(Import {
            visited: RwLock::new(Vec::new()),
            paths: RwLock::new(self.paths.read().unwrap().clone()),
            importer: self.importer.clone(),
        })
    }
}
