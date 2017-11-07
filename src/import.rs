//! Implementation of the `import!` macro.

use std::any::Any;
use std::borrow::Cow;
use std::sync::{Arc, Mutex, RwLock};
use std::fs::File;
use std::io;
use std::io::Read;
use std::path::PathBuf;

use itertools::Itertools;

use base::ast::{Expr, Literal, SpannedExpr, TypedIdent};
use base::metadata::Metadata;
use base::pos;
use base::symbol::Symbol;

use vm::{ExternLoader, ExternModule};
use vm::macros::{Error as MacroError, Macro, MacroExpander};
use vm::thread::{Thread, ThreadInternal};
use vm::internal::Value;

use super::{filename_to_module, Compiler};
use base::fnv::FnvMap;

quick_error! {
    /// Error type for the import macro
    #[derive(Debug)]
    pub enum Error {
        /// The importer found a cyclic dependency when loading files
        CyclicDependency(module: String, cycle: Vec<String>) {
            description("Cyclic dependency")
            display(
                "Module '{}' occurs in a cyclic dependency: `{}`",
                module,
                cycle.iter().chain(Some(module)).format(" -> ")
            )
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
        [$((concat!("std.", $file), include_str!(concat!("../std/", $file, ".glu")))),*]
    }
}
// Include the standard library distribution in the binary
static STD_LIBS: [(&str, &str); 19] = std_libs!(
    "prelude",
    "types",
    "function",
    "bool",
    "float",
    "int",
    "char",
    "io",
    "list",
    "map",
    "option",
    "parser",
    "result",
    "state",
    "stream",
    "string",
    "test",
    "unit",
    "writer"
);

pub trait Importer: Any + Clone + Sync + Send {
    fn import(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        modulename: &str,
        input: &str,
        expr: SpannedExpr<Symbol>,
    ) -> Result<(), MacroError>;
}

#[derive(Clone)]
pub struct DefaultImporter;
impl Importer for DefaultImporter {
    fn import(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        modulename: &str,
        input: &str,
        expr: SpannedExpr<Symbol>,
    ) -> Result<(), MacroError> {
        use compiler_pipeline::*;

        MacroValue { expr: expr }
            .load_script(compiler, vm, modulename, input, None)
            .sync_or_error()?;
        Ok(())
    }
}

#[derive(Clone, Default)]
pub struct CheckImporter(pub Arc<Mutex<FnvMap<String, SpannedExpr<Symbol>>>>);
impl CheckImporter {
    pub fn new() -> CheckImporter {
        CheckImporter::default()
    }
}
impl Importer for CheckImporter {
    fn import(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        module_name: &str,
        input: &str,
        expr: SpannedExpr<Symbol>,
    ) -> Result<(), MacroError> {
        use compiler_pipeline::*;

        let macro_value = MacroValue { expr: expr };
        let TypecheckValue { expr, typ } = macro_value.typecheck(compiler, vm, module_name, input)?;
        self.0.lock().unwrap().insert(module_name.into(), expr);
        let metadata = Metadata::default();
        // Insert a global to ensure the globals type can be looked up
        vm.global_env()
            .set_global(Symbol::from(module_name), typ, metadata, Value::Int(0))?;
        Ok(())
    }
}

enum UnloadedModule {
    Source(Cow<'static, str>),
    Extern(ExternModule),
}

/// Macro which rewrites occurances of `import! "filename"` to a load of that file if it is not
/// already loaded and then a global access to the loaded module
pub struct Import<I = DefaultImporter> {
    pub paths: RwLock<Vec<PathBuf>>,
    loaders: RwLock<FnvMap<String, ExternLoader>>,
    pub importer: I,
}

impl<I> Import<I> {
    /// Creates a new import macro
    pub fn new(importer: I) -> Import<I> {
        Import {
            paths: RwLock::new(vec![PathBuf::from(".")]),
            loaders: RwLock::default(),
            importer: importer,
        }
    }

    /// Adds a path to the list of paths which the importer uses to find files
    pub fn add_path<P: Into<PathBuf>>(&self, path: P) {
        self.paths.write().unwrap().push(path.into());
    }

    pub fn add_loader(&self, module: &str, loader: ExternLoader) {
        self.loaders
            .write()
            .unwrap()
            .insert(String::from(module), loader);
    }

    fn get_unloaded_module(
        &self,
        vm: &Thread,
        module: &str,
        filename: &str,
    ) -> Result<UnloadedModule, MacroError> {
        let mut buffer = String::new();

        // Retrieve the source, first looking in the standard library included in the
        // binary
        let std_file = STD_LIBS.iter().find(|tup| tup.0 == module);
        if let Some(tup) = std_file {
            return Ok(UnloadedModule::Source(Cow::Borrowed(tup.1)));
        }
        Ok(match std_file {
            Some(tup) => UnloadedModule::Source(Cow::Borrowed(tup.1)),
            None => {
                {
                    let loaders = self.loaders.read().unwrap();
                    if let Some(loader) = loaders.get(module) {
                        let value = loader(vm)?;
                        return Ok(UnloadedModule::Extern(value));
                    }
                }
                let file = self.paths
                    .read()
                    .unwrap()
                    .iter()
                    .filter_map(|p| {
                        let base = p.join(filename);
                        match File::open(&base) {
                            Ok(file) => Some(file),
                            Err(_) => None,
                        }
                    })
                    .next();
                let mut file = file.ok_or_else(|| {
                    Error::String(format!("Could not find module '{}'", module))
                })?;
                file.read_to_string(&mut buffer)?;
                UnloadedModule::Source(Cow::Owned(buffer))
            }
        })
    }

    pub fn load_module(
        &self,
        compiler: &mut Compiler,
        vm: &Thread,
        macros: &mut MacroExpander,
        module_id: &Symbol,
    ) -> Result<(), MacroError>
    where
        I: Importer,
    {
        let modulename = module_id.declared_name();
        use compiler_pipeline::*;
        let mut filename = modulename.replace(".", "/");
        filename.push_str(".glu");

        {
            let state = get_state(macros);
            if state.visited.iter().any(|m| **m == *filename) {
                let cycle = state
                    .visited
                    .iter()
                    .skip_while(|m| **m != *filename)
                    .cloned()
                    .collect();
                return Err(Error::CyclicDependency(filename.clone(), cycle).into());
            }
            state.visited.push(filename.clone());
        }

        // Retrieve the source, first looking in the standard library included in the
        // binary
        let unloaded_module = self.get_unloaded_module(vm, &modulename, &filename)?;

        match unloaded_module {
            UnloadedModule::Extern(ExternModule {
                value,
                typ,
                metadata,
            }) => {
                vm.set_global(module_id.clone(), typ, metadata, *value)?;
            }
            UnloadedModule::Source(file_contents) => {
                // Modules marked as this would create a cyclic dependency if they included the implicit
                // prelude
                let implicit_prelude = !file_contents.starts_with("//@NO-IMPLICIT-PRELUDE");
                compiler.set_implicit_prelude(implicit_prelude);
                let errors = macros.errors.len();
                let macro_result =
                    file_contents.expand_macro_with(compiler, macros, &modulename)?;
                if errors != macros.errors.len() {
                    // If macro expansion of the imported module fails we need to stop
                    // compilation of that module. To return an error we return one of the
                    // already emitted errors (which will be pushed back after this function
                    // returns)
                    if let Some(err) = macros.errors.pop() {
                        return Err(err);
                    }
                }
                get_state(macros).visited.pop();
                self.importer.import(
                    compiler,
                    vm,
                    &modulename,
                    &file_contents,
                    macro_result.expr,
                )?;
            }
        }
        Ok(())
    }
}

/// Adds an extern module to `thread`, letting it be loaded with `import! name` from gluon code.
/// 
/// ```
/// extern crate gluon;
/// #[macro_use]
/// extern crate gluon_vm;
/// 
/// use gluon::vm::{self, ExternModule};
/// use gluon::{Compiler, Thread};
/// use gluon::import::add_extern_module;
/// 
/// fn yell(s: &str) -> String {
///     s.to_uppercase()
/// }
/// 
/// fn my_module(thread: &Thread) -> vm::Result<ExternModule> {
///     ExternModule::new(
///         thread,
///         record!{
///             message => "Hello World!",
///             yell => primitive!(1 yell)
///         }
///     )
/// }
/// 
/// fn main_() -> gluon::Result<()> {
///     let thread = gluon::new_vm();
///     add_extern_module(&thread, "my_module", my_module);
///     let script = r#"
///         let module = import! "my_module"
///         module.yell module.message
///     "#;
///     let (result, _) = Compiler::new().run_expr::<String>(&thread, "example", script)?;
///     assert_eq!(result, "HELLO WORLD!");
///     Ok(())
/// }
/// fn main() {
///     if let Err(err) = main_() {
///         panic!("{}", err)
///     }
/// }
/// ```
pub fn add_extern_module(thread: &Thread, name: &str, loader: ExternLoader) {
    let opt_macro = thread.get_macros().get("import");
    let import = opt_macro
        .as_ref()
        .and_then(|mac| mac.downcast_ref::<Import>())
        .unwrap_or_else(|| ice!("Can't add an extern module with a import macro. Did you mean to create this `Thread` with `gluon::new_vm`"));
    import.add_loader(name, loader);
}

fn get_state<'m>(macros: &'m mut MacroExpander) -> &'m mut State {
    macros
        .state
        .entry(String::from("import"))
        .or_insert_with(|| {
            Box::new(State {
                visited: Vec::new(),
            })
        })
        .downcast_mut::<State>()
        .unwrap()
}


struct State {
    visited: Vec<String>,
}

impl<I> Macro for Import<I>
where
    I: Importer,
{
    fn expand(
        &self,
        macros: &mut MacroExpander,
        args: &mut [SpannedExpr<Symbol>],
    ) -> Result<SpannedExpr<Symbol>, MacroError> {
        if args.len() != 1 {
            return Err(Error::String("Expected import to get 1 argument".into()).into());
        }
        match args[0].value {
            Expr::Literal(Literal::String(ref filename)) => {
                let vm = macros.vm;

                let modulename = filename_to_module(filename);
                // Only load the script if it is not already loaded
                let name = Symbol::from(&*modulename);
                debug!("Import '{}' {:?}", modulename, get_state(macros).visited);
                if !vm.global_env().global_exists(&modulename) {
                    self.load_module(&mut Compiler::new(), vm, macros, &name)?;
                }
                // FIXME Does not handle shadowing
                Ok(pos::spanned(
                    args[0].span,
                    Expr::Ident(TypedIdent::new(name)),
                ))
            }
            _ => Err(Error::String("Expected a string literal to import".into()).into()),
        }
    }
}
