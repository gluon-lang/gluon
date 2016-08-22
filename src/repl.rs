extern crate rustyline;

use std::error::Error as StdError;
use std::fmt;
use std::sync::Mutex;

use self::rustyline::error::ReadlineError;

use base::ast::Typed;
use base::types::Kind;
use vm::api::{IO, Function, WithVM, VmType, Userdata};
use vm::gc::{Gc, Traverseable};
use vm::thread::{Thread, RootStr};

use gluon::{Compiler, new_vm, RootedThread, Result as GluonResult};

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
            let kind = alias.args.iter().rev().fold(Kind::typ(), |acc, arg| {
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
                try!(write!(&mut buffer, "type {}", args));
                for g in &alias.args {
                    try!(write!(&mut buffer, " {}", g.id))
                }
                try!(write!(&mut buffer, " = "));
                match alias.typ {
                    Some(ref typ) => try!(write!(&mut buffer, "{}", typ)),
                    None => try!(write!(&mut buffer, "<abstract>")),
                }
                Ok(())
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
    use check::completion;
    use gluon::compiler_pipeline::*;

    let mut compiler = Compiler::new();

    // The parser may find parse errors but still produce an expression
    // For that case still typecheck the expression but return the parse error afterwards
    let (expr, _parse_result): (_, GluonResult<()>) =
        match compiler.parse_partial_expr(&name, fileinput) {
            Ok(expr) => (expr, Ok(())),
            Err((None, err)) => return Err(err.into()),
            Err((Some(expr), err)) => (expr, Err(err.into())),
        };

    let MacroValue(mut expr) = try!(expr.expand_macro(&mut compiler, thread, &name));

    // Only need the typechecker to fill infer the types as best it can regardless of errors
    let _ = compiler.typecheck_expr(thread, &name, fileinput, &mut expr);
    let suggestions = completion::suggest(&*thread.get_env(), &expr, BytePos(pos as u32));
    Ok(suggestions.into_iter()
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
        let ident_start =
            line[..pos].rfind(|c: char| c.is_whitespace() || c == '.').map_or(0, |i| i + 1);
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
        Err(ReadlineError::Eof) |
        Err(ReadlineError::Interrupted) => return IO::Value(None),
        Err(err) => return IO::Exception(format!("{}", err)),
    };
    if !input.trim().is_empty() {
        editor.add_history_entry(&input);
    }

    IO::Value(Some(input))
}

fn compile_repl(vm: &Thread) -> Result<(), Box<StdError + Send + Sync>> {

    try!(vm.register_type::<Editor>("Editor", &[]));

    try!(vm.define_global("rustyline",
                          record!(
        new_editor => primitive!(1 new_editor),
        readline => primitive!(2 readline)
    )));
    try!(vm.define_global("repl_prim",
                          record!(
        type_of_expr => primitive!(1 type_of_expr),
        find_info => primitive!(1 find_info),
        find_kind => primitive!(1 find_kind)
    )));
    let mut compiler = Compiler::new();
    try!(compiler.load_file(vm, "std/prelude.glu"));
    try!(compiler.load_file(vm, "std/repl.glu"));
    Ok(())
}

#[allow(dead_code)]
pub fn run() -> Result<(), Box<StdError + Send + Sync>> {
    let vm = new_vm();
    try!(compile_repl(&vm));
    let mut repl: Function<&Thread, fn(()) -> IO<()>> = try!(vm.get_global("std.repl"));
    try!(repl.call(()));
    Ok(())
}

#[cfg(test)]
mod tests {
    use gluon::new_vm;
    use super::compile_repl;
    use vm::api::{IO, FunctionRef};

    #[test]
    fn compile_repl_test() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let repl: Result<FunctionRef<fn(()) -> IO<()>>, _> = vm.get_global("std.repl");
        assert!(repl.is_ok(), "{}", repl.err().unwrap());
    }

    type QueryFn = fn(&'static str) -> IO<Result<String, String>>;

    #[test]
    fn type_of_expr() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut type_of: FunctionRef<QueryFn> = vm.get_global("repl_prim.type_of_expr").unwrap();
        assert!(type_of.call("std.prelude.Option").is_ok());
    }

    #[test]
    fn find_kind() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut find_kind: FunctionRef<QueryFn> = vm.get_global("repl_prim.find_kind").unwrap();
        assert_eq!(find_kind.call("std.prelude.Option"),
                   Ok(IO::Value(Ok("Type -> Type".into()))));
    }

    #[test]
    fn find_info() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut find_info: FunctionRef<QueryFn> = vm.get_global("repl_prim.find_info").unwrap();
        match find_info.call("std.prelude.Option") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call("std.prelude.id") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call("float") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
    }
}
