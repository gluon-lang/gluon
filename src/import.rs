use std::cell::RefCell;
use std::error::Error as StdError;
use std::fs::File;
use std::io;
use std::io::Read;
use std::path::{Path, PathBuf};

use base::ast;
use vm::vm::VM;
use super::{filename_to_module, load_script};
use base::macros::{Macro, Error as MacroError};
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
        String(message: &'static str) {
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

/// Macro which rewrites occurances of `import "filename"` to a load of that file if it is not
/// already loaded and then a global access to the loaded module
pub struct Import {
    visited: RefCell<Vec<String>>,
    paths: RefCell<Vec<PathBuf>>,
}

impl Import {
    /// Creates a new import macro
    pub fn new() -> Import {
        Import {
            visited: RefCell::new(Vec::new()),
            paths: RefCell::new(vec![PathBuf::from(".")]),
        }
    }

    /// Adds a path to the list of paths which the importer uses to find files
    pub fn add_path<P: Into<PathBuf>>(&self, path: P) {
        self.paths.borrow_mut().push(path.into());
    }
}

impl<'a> Macro<VM<'a>> for Import {
    fn expand(&self,
              vm: &VM<'a>,
              arguments: &mut [ast::LExpr<TcIdent>])
              -> Result<ast::LExpr<TcIdent>, MacroError> {
        if arguments.len() != 1 {
            return Err(Error::String("Expected import to get 1 argument").into());
        }
        match *arguments[0] {
            ast::Expr::Literal(ast::LiteralEnum::String(ref filename)) => {
                let modulename = filename_to_module(filename);
                let path = Path::new(&filename[..]);
                // Only load the script if it is not already loaded
                let name = vm.symbol(&*modulename);
                debug!("Import '{}' {:?}", modulename, self.visited);
                if !vm.global_exists(&modulename) {
                    if self.visited.borrow().iter().any(|m| **m == **filename) {
                        return Err(Error::CyclicDependency(filename.clone()).into());
                    }
                    self.visited.borrow_mut().push(filename.clone());
                    let file = self.paths
                                   .borrow()
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
                    let mut file = try!(file.ok_or_else(|| Error::String("Could not find file")));
                    let mut buffer = String::new();
                    try!(file.read_to_string(&mut buffer));
                    try!(load_script(vm, &modulename, &buffer));
                    self.visited.borrow_mut().pop();
                }
                // FIXME Does not handle shadowing
                Ok(ast::located(arguments[0].location,
                                ast::Expr::Identifier(TcIdent::new(name))))
            }
            _ => return Err(Error::String("Expected a string literal to import").into()),
        }
    }
}
