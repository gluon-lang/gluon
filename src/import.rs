//! Implementation of the `import` macro.

use std::any::Any;
use std::sync::{Arc, RwLock, Mutex};
use std::fs::File;
use std::io;
use std::io::Read;
use std::path::{Path, PathBuf};

use base::ast::{Expr, Literal, SpannedExpr, TypedIdent};
use base::metadata::Metadata;
use base::pos;
use base::symbol::Symbol;
use vm::macros::{Macro, MacroExpander, Error as MacroError};
use vm::thread::{Thread, ThreadInternal};
use vm::internal::Value;
use super::{filename_to_module, Compiler};
use base::fnv::FnvMap;

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
    fn import(&self,
              compiler: &mut Compiler,
              vm: &Thread,
              modulename: &str,
              input: &str,
              expr: SpannedExpr<Symbol>)
              -> Result<(), MacroError>;
}

#[derive(Clone)]
pub struct DefaultImporter;
impl Importer for DefaultImporter {
    fn import(&self,
              compiler: &mut Compiler,
              vm: &Thread,
              modulename: &str,
              input: &str,
              expr: SpannedExpr<Symbol>)
              -> Result<(), MacroError> {
        use compiler_pipeline::*;
        try!(MacroValue { expr: expr }.load_script(compiler, vm, &modulename, (input, None)));
        Ok(())
    }
}

#[derive(Clone)]
pub struct CheckImporter(pub Arc<Mutex<FnvMap<String, SpannedExpr<Symbol>>>>);
impl CheckImporter {
    pub fn new() -> CheckImporter {
        CheckImporter(Arc::new(Mutex::new(FnvMap::default())))
    }
}
impl Importer for CheckImporter {
    fn import(&self,
              compiler: &mut Compiler,
              vm: &Thread,
              modulename: &str,
              input: &str,
              expr: SpannedExpr<Symbol>)
              -> Result<(), MacroError> {
        use compiler_pipeline::*;
        let TypecheckValue { expr, typ } = try!(MacroValue { expr: expr }
            .typecheck(compiler, vm, modulename, input));
        self.0.lock().unwrap().insert(modulename.into(), expr);
        let metadata = Metadata::default();
        // Insert a global to ensure the globals type can be looked up
        try!(vm.global_env().set_global(Symbol::from(modulename), typ, metadata, Value::Int(0)));
        Ok(())
    }
}

/// Macro which rewrites occurances of `import "filename"` to a load of that file if it is not
/// already loaded and then a global access to the loaded module
pub struct Import<I = DefaultImporter> {
    pub paths: RwLock<Vec<PathBuf>>,
    pub importer: I,
}

impl<I> Import<I> {
    /// Creates a new import macro
    pub fn new(importer: I) -> Import<I> {
        Import {
            paths: RwLock::new(vec![PathBuf::from(".")]),
            importer: importer,
        }
    }

    /// Adds a path to the list of paths which the importer uses to find files
    pub fn add_path<P: Into<PathBuf>>(&self, path: P) {
        self.paths.write().unwrap().push(path.into());
    }
}

fn get_state<'m>(macros: &'m mut MacroExpander) -> &'m mut State {
    macros.state
        .entry(String::from("import"))
        .or_insert_with(|| Box::new(State { visited: Vec::new() }))
        .downcast_mut::<State>()
        .unwrap()
}


struct State {
    visited: Vec<String>,
}

impl<I> Macro for Import<I>
    where I: Importer,
{
    fn expand(&self,
              macros: &mut MacroExpander,
              args: &mut [SpannedExpr<Symbol>])
              -> Result<SpannedExpr<Symbol>, MacroError> {
        use compiler_pipeline::*;

        if args.len() != 1 {
            return Err(Error::String("Expected import to get 1 argument".into()).into());
        }
        match args[0].value {
            Expr::Literal(Literal::String(ref filename)) => {
                let vm = macros.vm;

                let modulename = filename_to_module(filename);
                let path = Path::new(&filename[..]);
                // Only load the script if it is not already loaded
                let name = Symbol::from(&*modulename);
                debug!("Import '{}' {:?}", modulename, get_state(macros).visited);
                if !vm.global_env().global_exists(&modulename) {
                    {
                        let state = get_state(macros);
                        if state.visited.iter().any(|m| **m == **filename) {
                            return Err(Error::CyclicDependency(filename.clone()).into());
                        }
                        state.visited.push(filename.clone());
                    }
                    let mut buffer = String::new();

                    // Retrieve the source, first looking in the standard library included in the
                    // binary
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

                    let mut compiler = Compiler::new().implicit_prelude(modulename != "std.types");
                    let errors = macros.errors.errors.len();
                    let macro_result =
                        try!(file_contents.expand_macro_with(&mut compiler, macros, &modulename));
                    if errors != macros.errors.errors.len() {
                        // If macro expansion of the imported module fails we need to stop
                        // compilation of that module. To return an error we return one of the
                        // already emitted errors (which will be pushed back after this function
                        // returns)
                        if let Some(err) = macros.errors.errors.pop() {
                            return Err(err);
                        }
                    }
                    get_state(macros).visited.pop();
                    try!(self.importer
                        .import(&mut compiler,
                                vm,
                                &modulename,
                                &file_contents,
                                macro_result.expr));
                }
                // FIXME Does not handle shadowing
                Ok(pos::spanned(args[0].span, Expr::Ident(TypedIdent::new(name))))
            }
            _ => return Err(Error::String("Expected a string literal to import".into()).into()),
        }
    }
}
