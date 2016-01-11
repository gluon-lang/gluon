use std::cell::RefCell;
use std::error::Error as StdError;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};

use base::ast;
use vm::{VM, load_script};
use check::macros::Macro;
use check::macros::Error as MacroError;
use check::typecheck::TcIdent;

#[derive(Debug)]
pub enum Error {
    CyclicDependency(String),
    String(&'static str),
    Other(Box<StdError>),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::CyclicDependency(ref s) => {
                write!(f, "Module '{}' occurs in a cyclic dependency", s)
            }
            Error::String(s) => s.fmt(f),
            Error::Other(ref e) => e.fmt(f),
        }
    }
}

fn error<E: StdError + 'static>(e: E) -> Error {
    Error::Other(Box::new(e))
}

impl StdError for Error {
    fn description(&self) -> &str {
        "import error"
    }
}

pub struct Import {
    visited: RefCell<Vec<String>>,
    paths: RefCell<Vec<PathBuf>>,
}

impl Import {
    pub fn new() -> Import {
        Import {
            visited: RefCell::new(Vec::new()),
            paths: RefCell::new(vec![PathBuf::from(".")]),
        }
    }

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
                let path = Path::new(&filename[..]);
                let name = path.file_stem().and_then(|f| f.to_str()).expect("filename");
                // Only load the script if it is not already loaded
                if vm.get_global(&name).is_none() {
                    if self.visited.borrow().iter().any(|m| **m == **filename) {
                        return Err(Error::CyclicDependency(filename.clone()).into());
                    }
                    self.visited.borrow_mut().push(filename.clone());
                    let file = self.paths.borrow().iter()
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
                    try!(file.read_to_string(&mut buffer).map_err(error));
                    try!(load_script(vm, &name, &buffer));
                    self.visited.borrow_mut().pop();
                }
                // FIXME Does not handle shadowing
                Ok(ast::located(arguments[0].location,
                                ast::Expr::Identifier(TcIdent::new(vm.symbol(&name)))))
            }
            _ => return Err(Error::String("Expected a string literal to import").into()),
        }
    }
}
