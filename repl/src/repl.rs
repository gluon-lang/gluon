extern crate codespan_reporting;
extern crate futures_cpupool;
extern crate rustyline;

extern crate gluon_completion as completion;

use std::{error::Error as StdError, path::PathBuf, str::FromStr, sync::Mutex};

use futures::{
    future::{self, Either},
    sync::mpsc,
    {Future, Sink, Stream},
};

use base::{
    ast::{Expr, Pattern, SpannedPattern, Typed, TypedIdent},
    error::InFile,
    kind::Kind,
    pos, resolve,
    symbol::{Symbol, SymbolModule},
    types::ArcType,
    DebugLevel,
};
use parser::{parse_partial_repl_line, ReplLine};
use vm::{
    api::{
        de::De,
        generic::A,
        {Generic, Getable, OpaqueValue, OwnedFunction, Pushable, VmType, WithVM, IO},
    },
    internal::ValuePrinter,
    thread::{ActiveThread, RootedValue, Thread, ThreadInternal},
    {self, Error as VMError, Result as VMResult},
};

use gluon::{
    compiler_pipeline::{Executable, ExecuteValue},
    import::add_extern_module,
    {Compiler, Error as GluonError, Result as GluonResult, RootedThread},
};

use codespan_reporting::termcolor;

use Color;

macro_rules! try_future {
    ($e:expr, $f:expr) => {
        match $e {
            Ok(ok) => ok,
            Err(err) => return $f(::futures::future::err(err.into())),
        }
    };
}

fn type_of_expr(args: WithVM<&str>) -> IO<Result<String, String>> {
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

fn find_kind(args: WithVM<&str>) -> IO<Result<String, String>> {
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

fn find_info(args: WithVM<&str>) -> IO<Result<String, String>> {
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
    let maybe_comment = env
        .get_metadata(args)
        .ok()
        .and_then(|metadata| metadata.comment.as_ref());
    if let Some(comment) = maybe_comment {
        for line in comment.content.lines() {
            write!(&mut buffer, "\n/// {}", line).unwrap();
        }
    }
    IO::Value(Ok(buffer))
}

fn switch_debug_level(args: WithVM<&str>) -> IO<Result<String, String>> {
    let vm = args.vm;
    let args = args.value.trim();
    if args != "" {
        let debug_level = match DebugLevel::from_str(args) {
            Ok(debug_level) => debug_level,
            Err(e) => return IO::Value(Err(e.to_string())),
        };
        vm.global_env().set_debug_level(debug_level);
    }
    IO::Value(Ok(vm.global_env().get_debug_level().to_string()))
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
    let _ = (&mut expr).typecheck(&mut compiler, thread, &name, fileinput);
    let file_map = compiler
        .get_filemap(&name)
        .ok_or_else(|| VMError::from("FileMap is missing for completion".to_string()))?;
    let suggestions = completion::suggest(
        &*thread.get_env(),
        file_map.span(),
        &expr,
        BytePos::from(pos as u32),
    );
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

macro_rules! impl_userdata {
    ($name:ident) => {
        impl ::std::fmt::Debug for $name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                write!(f, concat!(stringify!($name), "(..)"))
            }
        }
    };
}

#[derive(Userdata)]
struct Editor {
    editor: Mutex<rustyline::Editor<Completer>>,
}

impl_userdata! { Editor }

#[derive(Userdata)]
struct CpuPool(self::futures_cpupool::CpuPool);

impl_userdata! { CpuPool }

#[derive(Serialize, Deserialize)]
pub enum ReadlineError {
    Eof,
    Interrupted,
}

macro_rules! define_vmtype {
    ($name:ident) => {
        impl VmType for $name {
            type Type = $name;
            fn make_type(vm: &Thread) -> ArcType {
                let typ = concat!("rustyline_types.", stringify!($name));
                (*vm.global_env().get_env().find_type_info(typ).unwrap())
                    .clone()
                    .into_type()
            }
        }
    };
}

define_vmtype! { ReadlineError }

impl<'vm> Pushable<'vm> for ReadlineError {
    fn push(self, context: &mut ActiveThread<'vm>) -> VMResult<()> {
        ::gluon::vm::api::ser::Ser(self).push(context)
    }
}

fn app_dir_root() -> Result<PathBuf, Box<StdError>> {
    Ok(::app_dirs::app_root(
        ::app_dirs::AppDataType::UserData,
        &::APP_INFO,
    )?)
}

fn new_editor(vm: WithVM<()>) -> IO<Editor> {
    let mut editor = rustyline::Editor::new();

    let history_result =
        app_dir_root().and_then(|path| Ok(editor.load_history(&*path.join("history"))?));

    if let Err(err) = history_result {
        warn!("Unable to load history: {}", err);
    }
    editor.set_completer(Some(Completer(vm.vm.root_thread())));
    IO::Value(Editor {
        editor: Mutex::new(editor),
    })
}

fn readline(editor: &Editor, prompt: &str) -> IO<Result<String, ReadlineError>> {
    let mut editor = editor.editor.lock().unwrap();
    let input = match editor.readline(prompt) {
        Ok(input) => input,
        Err(rustyline::error::ReadlineError::Eof) => return IO::Value(Err(ReadlineError::Eof)),
        Err(rustyline::error::ReadlineError::Interrupted) => {
            return IO::Value(Err(ReadlineError::Interrupted));
        }
        Err(err) => return IO::Exception(format!("{}", err)),
    };
    if !input.trim().is_empty() {
        editor.add_history_entry(&input);
    }

    IO::Value(Ok(input))
}

fn new_cpu_pool(size: usize) -> IO<CpuPool> {
    IO::Value(CpuPool(self::futures_cpupool::CpuPool::new(size)))
}

fn eval_line(
    De(color): De<::Color>,
    WithVM { vm, value: line }: WithVM<&str>,
) -> impl Future<Item = IO<()>, Error = vm::Error> {
    eval_line_(vm.root_thread(), line).then(move |result| {
        Ok(match result {
            Ok(x) => IO::Value(x),
            Err((compiler, err)) => {
                let mut stderr = termcolor::StandardStream::stderr(color.into());
                if let Err(err) = err.emit(&mut stderr, compiler.code_map()) {
                    eprintln!("{}", err);
                }
                IO::Value(())
            }
        })
    })
}

fn eval_line_(
    vm: RootedThread,
    line: &str,
) -> impl Future<Item = (), Error = (Compiler, GluonError)> {
    let mut compiler = Compiler::new();
    let repl_line = {
        let result = {
            let filemap = compiler.add_filemap("line", line);
            let mut module = SymbolModule::new("line".into(), compiler.mut_symbols());
            parse_partial_repl_line(&mut module, &*filemap)
        };
        match result {
            Ok(x) => x,
            Err((_, err)) => {
                let code_map = compiler.code_map().clone();
                return Either::A(future::err((compiler, InFile::new(code_map, err).into())));
            }
        }
    };
    let future = match repl_line {
        None => return Either::A(future::ok(())),
        Some(ReplLine::Expr(expr)) => {
            compiler = compiler.run_io(true);
            Either::A(expr.run_expr(&mut compiler, vm, "line", line, None))
        }
        Some(ReplLine::Let(mut let_binding)) => {
            let unpack_pattern = let_binding.name.clone();
            // We can't compile function bindings by only looking at `let_binding.expr`
            // so rewrite `let f x y = <expr>` into `let f x y = <expr> in f`
            // and `let { x } = <expr>` into `let repl_temp @ { x } = <expr> in repl_temp`
            let id = match unpack_pattern.value {
                Pattern::Ident(ref id) if !let_binding.args.is_empty() => id.clone(),
                _ => {
                    let id = Symbol::from("repl_temp");
                    let_binding.name = pos::spanned(
                        let_binding.name.span,
                        Pattern::As(
                            pos::spanned(let_binding.name.span, id.clone()),
                            Box::new(let_binding.name),
                        ),
                    );
                    TypedIdent::new(id)
                }
            };
            let id = pos::spanned2(0.into(), 0.into(), Expr::Ident(id.clone()));
            let expr = Expr::let_binding(let_binding, id);
            let eval_expr = pos::spanned2(0.into(), 0.into(), expr);
            Either::B(
                eval_expr
                    .run_expr(&mut compiler, vm.clone(), "line", line, None)
                    .and_then(move |value| {
                        // Hack to get around borrow-checker. Method-chaining didn't work,
                        // even with #[feature(nll)]. Seems like a bug
                        let temp =
                            set_globals(&vm, &unpack_pattern, &value.typ, &value.value.as_ref());
                        temp.and(Ok(value))
                    }),
            )
        }
    };
    Either::B(
        future
            .map_err(|x| (compiler, x))
            .map(move |ExecuteValue { value, typ, .. }| {
                let vm = value.vm();
                let env = vm.global_env().get_env();
                let debug_level = vm.global_env().get_debug_level();
                println!(
                    "{}",
                    ValuePrinter::new(&*env, &typ, value.get_variant(), &debug_level)
                        .width(80)
                        .max_level(5)
                );
            }),
    )
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
                value.get_value(),
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
            let resolved_type = resolve::remove_aliases_cow(&*vm.global_env().get_env(), typ);

            for pattern_field in fields.iter() {
                let field_name: &Symbol = &pattern_field.name.value;
                // if the record didn't have a field with this name,
                // there should have already been a type error. So we can just panic here
                let field_value: RootedValue<&Thread> = value
                    .get_field(field_name.declared_name())
                    .unwrap_or_else(|| {
                        panic!("record doesn't have field `{}`", field_name.declared_name())
                    });
                let field_type = resolved_type
                    .row_iter()
                    .find(|f| f.name.name_eq(field_name))
                    .unwrap_or_else(|| {
                        panic!(
                            "record type `{}` doesn't have field `{}`",
                            resolved_type,
                            field_name.declared_name()
                        )
                    })
                    .typ
                    .clone();
                match pattern_field.value {
                    Some(ref sub_pattern) => {
                        set_globals(vm, sub_pattern, &field_type, &field_value)?
                    }
                    None => vm.set_global(
                        Symbol::from(format!("@{}", pattern_field.name.value.declared_name())),
                        field_type.to_owned(),
                        Default::default(),
                        field_value.get_value(),
                    )?,
                }
            }
            Ok(())
        }
        Pattern::As(ref id, ref pattern) => {
            vm.set_global(
                Symbol::from(format!("@{}", id.value.declared_name())),
                typ.clone(),
                Default::default(),
                value.get_value(),
            )?;
            set_globals(vm, pattern, typ, value)
        }
        Pattern::Constructor(..) | Pattern::Literal(_) | Pattern::Error => {
            Err(VMError::Message("The repl cannot bind variables from this pattern".into()).into())
        }
    }
}

fn finish_or_interrupt(
    cpu_pool: &CpuPool,
    thread: RootedThread,
    action: OpaqueValue<&Thread, IO<Generic<A>>>,
) -> impl Future<Item = IO<OpaqueValue<RootedThread, A>>, Error = VMError> {
    let (sender, receiver) = mpsc::channel(1);

    ::tokio::spawn(
        ::tokio_signal::ctrl_c()
            .map(|x| {
                info!("Installed Ctrl-C handler");
                x
            })
            .flatten_stream()
            .map_err(|err| {
                panic!("Error installing signal handler: {}", err);
            })
            .forward(sender.sink_map_err(|_| ()))
            .map(|_| ()),
    );

    let mut action = OwnedFunction::<fn() -> IO<OpaqueValue<RootedThread, A>>>::from_value(
        &thread,
        action.get_variant(),
    );
    let action_future = cpu_pool.0.spawn_fn(move || action.call_async());

    let ctrl_c_future = receiver
        .into_future()
        .map(move |(next, _)| {
            next.unwrap();
            thread.interrupt();
            IO::Exception("Interrupted".to_string())
        })
        .map_err(|_| panic!("Error in Ctrl-C handling"));

    ctrl_c_future
        .select(action_future)
        .map(|(value, _)| value)
        .map_err(|(err, _)| err)
}

fn save_history(editor: &Editor) -> IO<()> {
    let history_result = app_dir_root().and_then(|path| {
        editor
            .editor
            .lock()
            .unwrap()
            .save_history(&*path.join("history"))
            .map_err(|err| {
                let err: Box<StdError> = Box::new(err);
                err
            })
    });

    if let Err(err) = history_result {
        warn!("Unable to load history: {}", err);
    }
    IO::Value(())
}

fn load_rustyline(vm: &Thread) -> vm::Result<vm::ExternModule> {
    vm.register_type::<Editor>("Editor", &[])?;
    vm.register_type::<CpuPool>("CpuPool", &[])?;

    vm::ExternModule::new(
        vm,
        record!(
            type Editor => Editor,
            type CpuPool => CpuPool,
            new_editor => primitive!(1, new_editor),
            readline => primitive!(2, readline),
            save_history => primitive!(1, save_history)
        ),
    )
}

#[derive(VmType, Pushable, Getable)]
struct Settings<'a> {
    color: Color,
    prompt: &'a str,
}

fn load_repl(vm: &Thread) -> vm::Result<vm::ExternModule> {
    vm::ExternModule::new(
        vm,
        record!(
            type Color => Color,
            type Settings => Settings<'static>,
            type_of_expr => primitive!(1, type_of_expr),
            find_info => primitive!(1, find_info),
            find_kind => primitive!(1, find_kind),
            parse_color => primitive!(1, "parse_color", |s: &str| s.parse::<Color>()),
            switch_debug_level => primitive!(1, switch_debug_level),
            eval_line => primitive!(2, async fn eval_line),
            finish_or_interrupt => primitive!(3, async fn finish_or_interrupt),
            new_cpu_pool => primitive!(1, new_cpu_pool)
        ),
    )
}

fn compile_repl(compiler: &mut Compiler, vm: &Thread) -> Result<(), GluonError> {
    let rustyline_types_source = ::gluon::vm::api::typ::make_source::<ReadlineError>(vm)?;
    compiler.load_script(vm, "rustyline_types", &rustyline_types_source)?;

    add_extern_module(vm, "repl.prim", load_repl);
    add_extern_module(vm, "rustyline", load_rustyline);

    const REPL_SOURCE: &'static str =
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/repl.glu"));

    compiler.load_script(vm, "repl", REPL_SOURCE)?;
    Ok(())
}

#[allow(dead_code)]
pub fn run(
    color: Color,
    prompt: &str,
    debug_level: DebugLevel,
) -> impl Future<Item = (), Error = Box<StdError + Send + Sync + 'static>> {
    let vm = ::gluon::VmBuilder::new().build();
    vm.global_env().set_debug_level(debug_level);

    let mut compiler = Compiler::new();
    try_future!(
        compile_repl(&mut compiler, &vm)
            .map_err(|err| err.emit_string(compiler.code_map()).unwrap()),
        Either::A
    );

    let mut repl: OwnedFunction<fn(_) -> _> = try_future!(vm.get_global("repl"), Either::A);
    debug!("Starting repl");
    Either::B(
        repl.call_async(Settings { color, prompt })
            .map(|_: IO<()>| ())
            .map_err(|err| err.into()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    use gluon::import::Import;
    use gluon::{self, RootedThread};
    use vm::api::{FunctionRef, IO};

    fn new_vm() -> RootedThread {
        if ::std::env::var("GLUON_PATH").is_err() {
            ::std::env::set_var("GLUON_PATH", "..");
        }
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
        let _ = ::env_logger::try_init();
        let vm = new_vm();
        compile_repl(&mut Compiler::new(), &vm).unwrap_or_else(|err| panic!("{}", err));
        let repl: Result<FunctionRef<fn(Color, String) -> IO<()>>, _> = vm.get_global("repl");
        assert!(repl.is_ok(), "{}", repl.err().unwrap());
    }

    #[test]
    fn record_patterns() {
        let _ = ::env_logger::try_init();
        let vm = new_vm();
        compile_repl(&mut Compiler::new(), &vm).unwrap_or_else(|err| panic!("{}", err));

        // pattern with field names out of order
        eval_line_(vm.clone(), r#"let {y, x} = {x = "x", y = "y"}"#)
            .wait()
            .map_err(|(_, err)| err)
            .expect("Error evaluating let binding");
        let x: String = vm.get_global("x").expect("Error getting x");
        assert_eq!(x, "x");
        let y: String = vm.get_global("y").expect("Error getting y");
        assert_eq!(y, "y");

        // pattern with field names out of order and different field types
        eval_line_(vm.clone(), r#"let {y} = {x = "x", y = ()}"#)
            .wait()
            .map_err(|(_, err)| err)
            .expect("Error evaluating let binding 2");
        let () = vm.get_global("y").expect("Error getting y");
    }

    type QueryFn = fn(&'static str) -> IO<Result<String, String>>;

    #[test]
    fn type_of_expr() {
        let _ = ::env_logger::try_init();
        let vm = new_vm();
        compile_repl(&mut Compiler::new(), &vm).unwrap_or_else(|err| panic!("{}", err));
        let mut type_of: FunctionRef<QueryFn> = vm.get_global("repl.prim.type_of_expr").unwrap();
        assert_eq!(type_of.call("123"), Ok(IO::Value(Ok("Int".into()))));
    }

    #[test]
    fn find_kind() {
        let _ = ::env_logger::try_init();
        let vm = new_vm();
        compile_repl(&mut Compiler::new(), &vm).unwrap_or_else(|err| panic!("{}", err));
        let mut find_kind: FunctionRef<QueryFn> = vm.get_global("repl.prim.find_kind").unwrap();
        assert_eq!(
            find_kind.call("std.prelude.Semigroup"),
            Ok(IO::Value(Ok("Type -> Type".into())))
        );
    }

    #[test]
    fn find_info() {
        let _ = ::env_logger::try_init();
        let vm = new_vm();
        compile_repl(&mut Compiler::new(), &vm).unwrap_or_else(|err| panic!("{}", err));
        let mut find_info: FunctionRef<QueryFn> = vm.get_global("repl.prim.find_info").unwrap();
        match find_info.call("std.prelude.Semigroup") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call("std.prelude.empty") {
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
        let _ = ::env_logger::try_init();
        let vm = new_vm();
        compile_repl(&mut Compiler::new(), &vm).unwrap_or_else(|err| panic!("{}", err));
        complete(&vm, "<repl>", "", 0).unwrap_or_else(|err| panic!("{}", err));
    }
}
