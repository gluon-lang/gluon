extern crate rustyline;

extern crate gluon_completion as completion;

use std::error::Error as StdError;
use std::fmt;
use std::sync::Mutex;

use futures::Future;

use self::rustyline::error::ReadlineError;


use base::ast::{Expr, Pattern, SpannedPattern, Typed};
use base::error::InFile;
use base::kind::Kind;
use base::pos;
use base::symbol::{Symbol, SymbolModule};
use base::types::ArcType;
use parser::parse_partial_let_or_expr;
use vm::{self, Error as VMError};
use vm::api::{OwnedFunction, Userdata, VmType, WithVM, IO};
use vm::gc::{Gc, Traverseable};
use vm::internal::ValuePrinter;
use vm::thread::{RootStr, RootedValue, Thread, ThreadInternal};

use gluon::{new_vm, Compiler, Result as GluonResult, RootedThread};
use gluon::import::add_extern_module;
use gluon::compiler_pipeline::{Executable, ExecuteValue};

fn type_of_expr(args: WithVM<RootStr>) -> IO<Result<String, String>> {
    let WithVM { vm, value: args } = args;
    let mut compiler = Compiler::new();
    IO::Value(match compiler.typecheck_str(vm, "<repl>", &args, None) {
        Ok((expr, _)) => {
            let env = vm.get_env();
            Ok(format!("{}", expr.env_type_of(&*env)))
        }
        Err(msg) => Err(format!("{}", msg)),
    })
}

fn find_kind(args: WithVM<RootStr>) -> IO<Result<String, String>> {
    let vm = args.vm;
    let args = args.value.trim();
    IO::Value(match vm.find_type_info(args) {
        Ok(ref alias) => {
            let kind = alias.params().iter().rev().fold(Kind::typ(), |acc, arg| {
                Kind::function(arg.kind.clone(), acc)
            });
            Ok(format!("{}", kind))
        }
        Err(err) => Err(format!("{}", err)),
    })
}

fn find_info(args: WithVM<RootStr>) -> IO<Result<String, String>> {
    use std::fmt::Write;
    let vm = args.vm;
    let args = args.value.trim();
    let env = vm.get_env();
    let mut buffer = String::new();
    match env.find_type_info(args) {
        Ok(alias) => {
            // Found a type alias
            let mut fmt = || -> Result<(), ::std::fmt::Error> {
                write!(&mut buffer, "type {}", args)?;
                for g in alias.params() {
                    write!(&mut buffer, " {}", g.id)?;
                }
                write!(&mut buffer, " = {}", alias.unresolved_type())
            };
            fmt().unwrap();
        }
        Err(err) => {
            // Try to find a value at `args` to print its type and documentation comment (if any)
            match env.get_binding(args) {
                Ok((_, typ)) => {
                    write!(&mut buffer, "{}: {}", args, typ).unwrap();
                }
                Err(_) => return IO::Value(Err(format!("{}", err))),
            }
        }
    }
    let maybe_comment = env.get_metadata(args)
        .ok()
        .and_then(|metadata| metadata.comment.as_ref());
    if let Some(comment) = maybe_comment {
        for line in comment.lines() {
            write!(&mut buffer, "\n/// {}", line).unwrap();
        }
    }
    IO::Value(Ok(buffer))
}

fn complete(thread: &Thread, name: &str, fileinput: &str, pos: usize) -> GluonResult<Vec<String>> {
    use base::pos::BytePos;
    use gluon::compiler_pipeline::*;

    let mut compiler = Compiler::new();

    // The parser may find parse errors but still produce an expression
    // For that case still typecheck the expression but return the parse error afterwards
    let (mut expr, _parse_result): (_, GluonResult<()>) =
        match compiler.parse_partial_expr(thread.global_env().type_cache(), &name, fileinput) {
            Ok(expr) => (expr, Ok(())),
            Err((None, err)) => return Err(err.into()),
            Err((Some(expr), err)) => (expr, Err(err.into())),
        };

    // Only need the typechecker to fill infer the types as best it can regardless of errors
    let _ = expr.typecheck(&mut compiler, thread, &name, fileinput);
    let suggestions = completion::suggest(&*thread.get_env(), &expr, BytePos::from(pos));
    Ok(suggestions
        .into_iter()
        .map(|ident| {
            let s: &str = ident.name.as_ref();
            s.to_string()
        })
        .collect())
}

struct Completer(RootedThread);

impl rustyline::completion::Completer for Completer {
    fn complete(&self, line: &str, pos: usize) -> rustyline::Result<(usize, Vec<String>)> {
        let result = complete(&self.0, "<repl>", line, pos);

        // Get the start of the completed identifier
        let ident_start = line[..pos]
            .rfind(|c: char| c.is_whitespace() || c == '.')
            .map_or(0, |i| i + 1);
        Ok((ident_start, result.unwrap_or(Vec::new())))
    }
}

struct Editor(Mutex<rustyline::Editor<Completer>>);

impl Userdata for Editor {}

impl fmt::Debug for Editor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Editor(..)")
    }
}

impl VmType for Editor {
    type Type = Editor;
}

impl Traverseable for Editor {
    fn traverse(&self, _: &mut Gc) {}
}

fn new_editor(vm: WithVM<()>) -> Editor {
    let mut editor = rustyline::Editor::new();
    editor.set_completer(Some(Completer(vm.vm.root_thread())));
    Editor(Mutex::new(editor))
}

fn readline(editor: &Editor, prompt: &str) -> IO<Option<String>> {
    let mut editor = editor.0.lock().unwrap();
    let input = match editor.readline(prompt) {
        Ok(input) => input,
        Err(ReadlineError::Eof) | Err(ReadlineError::Interrupted) => return IO::Value(None),
        Err(err) => return IO::Exception(format!("{}", err)),
    };
    if !input.trim().is_empty() {
        editor.add_history_entry(&input);
    }

    IO::Value(Some(input))
}

fn eval_line(WithVM { vm, value: line }: WithVM<&str>) -> IO<String> {
    IO::Value(match eval_line_(vm, line) {
        Ok(x) => x,
        Err(x) => x.to_string(),
    })
}

fn eval_line_(vm: &Thread, line: &str) -> GluonResult<String> {
    let mut compiler = Compiler::new();
    let let_or_expr = {
        let mut module = SymbolModule::new("<line>".into(), compiler.mut_symbols());
        match parse_partial_let_or_expr(&mut module, line) {
            Ok(x) => x,
            Err((_, err)) => return Err(InFile::new("<line>", line, err).into()),
        }
    };
    let mut eval_expr;
    let ExecuteValue { value, typ, .. } = match let_or_expr {
        Ok(expr) => {
            eval_expr = expr;
            compiler = compiler.run_io(true);
            eval_expr
                .run_expr(&mut compiler, vm, "<line>", line, None)
                .wait()?
        }
        Err(let_binding) => {
            let unpack_pattern = let_binding.name.clone();
            eval_expr = match unpack_pattern.value {
                Pattern::Ident(ref id) if !let_binding.args.is_empty() => {
                    // We can't compile function bindings by only looking at `let_binding.expr`
                    // so rewrite `let f x y = <expr>` into `let f x y = <expr> in f`
                    let id = pos::spanned2(0.into(), 0.into(), Expr::Ident(id.clone()));
                    let expr = Expr::LetBindings(vec![let_binding], Box::new(id));
                    pos::spanned2(0.into(), 0.into(), expr)
                }
                _ => let_binding.expr,
            };
            let value = eval_expr
                .run_expr(&mut compiler, vm, "<line>", line, None)
                .wait()?;
            set_globals(vm, &unpack_pattern, &value.typ, &value.value)?;
            value
        }
    };

    let env = vm.global_env().get_env();
    Ok(ValuePrinter::new(&*env, &typ, *value).width(80).to_string())
}

fn set_globals(
    vm: &Thread,
    pattern: &SpannedPattern<Symbol>,
    typ: &ArcType,
    value: &RootedValue<&Thread>,
) -> GluonResult<()> {
    match pattern.value {
        Pattern::Ident(ref id) => {
            vm.set_global(
                Symbol::from(format!("@{}", id.name.declared_name())),
                typ.clone(),
                Default::default(),
                **value,
            )?;
            Ok(())
        }
        Pattern::Tuple { ref elems, .. } => {
            let iter = elems.iter().zip(::vm::dynamic::field_iter(&value, typ, vm));
            for (elem_pattern, (elem_value, elem_type)) in iter {
                set_globals(vm, elem_pattern, &elem_type, &elem_value)?;
            }
            Ok(())
        }
        Pattern::Record { ref fields, .. } => {
            let iter = fields
                .iter()
                .zip(::vm::dynamic::field_iter(&value, typ, vm));
            for (field, (field_value, field_type)) in iter {
                match field.value {
                    Some(ref field_pattern) => {
                        set_globals(vm, field_pattern, &field_type, &field_value)?
                    }
                    None => vm.set_global(
                        field.name.value.clone(),
                        field_type,
                        Default::default(),
                        *field_value,
                    )?,
                }
            }
            Ok(())
        }
        _ => {
            Err(VMError::Message("The repl cannot bind variables from this pattern".into()).into())
        }
    }
}

fn load_rustyline(vm: &Thread) -> vm::Result<vm::ExternModule> {
    vm.register_type::<Editor>("Editor", &[])?;

    vm::ExternModule::new(
        vm,
        record!(
            new_editor => primitive!(1 new_editor),
            readline => primitive!(2 readline)
        ),
    )
}

fn load_repl(vm: &Thread) -> vm::Result<vm::ExternModule> {
    vm::ExternModule::new(
        vm,
        record!(
            type_of_expr => primitive!(1 type_of_expr),
            find_info => primitive!(1 find_info),
            find_kind => primitive!(1 find_kind),
            eval_line => primitive!(1 eval_line)
        ),
    )
}

fn compile_repl(vm: &Thread) -> Result<(), Box<StdError + Send + Sync>> {
    add_extern_module(vm, "repl.prim", load_repl);
    add_extern_module(vm, "rustyline", load_rustyline);

    const REPL_SOURCE: &'static str =
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/repl.glu"));

    let mut compiler = Compiler::new();
    compiler
        .load_script_async(vm, "repl", REPL_SOURCE)
        .sync_or_error()?;
    Ok(())
}

#[allow(dead_code)]
pub fn run() -> Result<(), Box<StdError + Send + Sync>> {
    let vm = new_vm();
    compile_repl(&vm)?;
    let mut repl: OwnedFunction<fn(()) -> IO<()>> = vm.get_global("repl")?;
    debug!("Starting repl");

    let mut core = ::tokio_core::reactor::Core::new()?;
    core.run(repl.call_async(()))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    use vm::api::{FunctionRef, IO};
    use gluon::{self, RootedThread};
    use gluon::import::Import;

    fn new_vm() -> RootedThread {
        let vm = gluon::new_vm();
        let import = vm.get_macros().get("import");
        import
            .as_ref()
            .and_then(|import| import.downcast_ref::<Import>())
            .expect("Import macro")
            .add_path("..");
        vm
    }

    #[test]
    fn compile_repl_test() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let repl: Result<FunctionRef<fn(()) -> IO<()>>, _> = vm.get_global("repl");
        assert!(repl.is_ok(), "{}", repl.err().unwrap());
    }

    type QueryFn = fn(&'static str) -> IO<Result<String, String>>;

    #[test]
    fn type_of_expr() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut type_of: FunctionRef<QueryFn> = vm.get_global("repl.prim.type_of_expr").unwrap();
        assert_eq!(type_of.call("123"), Ok(IO::Value(Ok("Int".into()))));
    }

    #[test]
    fn find_kind() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut find_kind: FunctionRef<QueryFn> = vm.get_global("repl.prim.find_kind").unwrap();
        assert_eq!(
            find_kind.call("std.prelude.Semigroup"),
            Ok(IO::Value(Ok("Type -> Type".into())))
        );
    }

    #[test]
    fn find_info() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut find_info: FunctionRef<QueryFn> = vm.get_global("repl.prim.find_info").unwrap();
        match find_info.call("std.prelude.Semigroup") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call("std.prelude.make_Semigroup") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call("std.float.prim") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
    }

    #[test]
    fn complete_repl_empty() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        complete(&vm, "<repl>", "", 0).unwrap_or_else(|err| panic!("{}", err));
    }
}
