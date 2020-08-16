extern crate gluon_completion as completion;

use std::{borrow::Cow, error::Error as StdError, path::PathBuf, str::FromStr, sync::Mutex};

use futures::{channel::oneshot, future, prelude::*};

use crate::base::{
    ast::{self, AstClone, Expr, Pattern, RootExpr, SpannedPattern, Typed, TypedIdent},
    error::InFile,
    kind::Kind,
    mk_ast_arena, pos, resolve,
    symbol::{Symbol, SymbolModule},
    types::{ArcType, TypeExt},
    DebugLevel,
};
use crate::parser::{parse_partial_repl_line, ReplLine};
use crate::vm::{
    api::{
        de::De, generic::A, Generic, Getable, OpaqueValue, OwnedFunction, Pushable, VmType, WithVM,
        IO,
    },
    internal::ValuePrinter,
    thread::{ActiveThread, RootedValue, Thread},
    {self, Error as VMError, Result as VMResult},
};

use gluon::{
    compiler_pipeline::{Executable, ExecuteValue},
    import::add_extern_module,
    query::CompilerDatabase,
    Error as GluonError, Result as GluonResult, RootedThread, ThreadExt,
};

use codespan_reporting::term::termcolor;

use crate::Color;

fn type_of_expr(args: WithVM<&str>) -> impl Future<Output = IO<Result<String, String>>> {
    let WithVM { vm, value: args } = args;
    let args = args.to_string();
    let vm = vm.new_thread().unwrap(); // TODO Run on the same thread once that works

    async move {
        IO::Value(match vm.typecheck_str_async("<repl>", &args, None).await {
            Ok((expr, _)) => {
                let env = vm.get_env();
                Ok(format!("{}", expr.env_type_of(&env)))
            }
            Err(msg) => Err(format!("{}", msg)),
        })
    }
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
            let mut fmt = || -> Result<(), std::fmt::Error> {
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
    let maybe_metadata = env.get_metadata(args).ok();
    if let Some(comment) = maybe_metadata
        .as_ref()
        .and_then(|metadata| metadata.comment.as_ref())
    {
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
    use gluon::compiler_pipeline::*;

    let mut db = thread.get_database();
    let mut module_compiler = thread.module_compiler(&mut db);

    // The parser may find parse errors but still produce an expression
    // For that case still typecheck the expression but return the parse error afterwards
    let mut expr = match parse_expr(
        &mut module_compiler,
        thread.global_env().type_cache(),
        &name,
        fileinput,
    ) {
        Ok(expr) => expr,
        Err(err) => err.get_value()?,
    };

    // Only need the typechecker to fill infer the types as best it can regardless of errors
    let _ = (&mut expr).typecheck(&mut module_compiler, thread, &name, fileinput);
    let file_map = module_compiler
        .get_filemap(&name)
        .ok_or_else(|| VMError::from("FileMap is missing for completion".to_string()))?;
    let suggestions = completion::suggest(
        &thread.get_env(),
        file_map.span(),
        &expr.expr(),
        file_map.span().start() + pos::ByteOffset::from(pos as i64),
    );
    Ok(suggestions
        .into_iter()
        .map(|ident| {
            let s: &str = ident.name.as_ref();
            s.to_string()
        })
        .collect())
}

struct Completer {
    thread: RootedThread,
    hinter: rustyline::hint::HistoryHinter,
    highlighter: rustyline::highlight::MatchingBracketHighlighter,
}

impl rustyline::Helper for Completer {}

impl rustyline::validate::Validator for Completer {
    fn validate(
        &self,
        ctx: &mut rustyline::validate::ValidationContext,
    ) -> rustyline::Result<rustyline::validate::ValidationResult> {
        let line = ctx.input();

        let is_incomplete = |err: &gluon::parser::ParseErrors| {
            use gluon::parser::Token;

            err.iter().any(|err| match &err.value {
                gluon::parser::Error::UnexpectedToken(Token::CloseBlock, _) => true,
                _ => false,
            })
        };

        let mut db = self.thread.get_database();
        let mut module_compiler = self.thread.module_compiler(&mut db);
        mk_ast_arena!(arena);
        let filemap = self.thread.get_database().add_filemap("line", line);
        let mut module = SymbolModule::new("line".into(), module_compiler.mut_symbols());
        match parse_partial_repl_line((*arena).borrow(), &mut module, &*filemap) {
            Err((_, err)) if is_incomplete(&err) => {
                Ok(rustyline::validate::ValidationResult::Incomplete)
            }
            Ok(_) | Err(_) => Ok(rustyline::validate::ValidationResult::Valid(None)),
        }
    }
}

impl rustyline::hint::Hinter for Completer {
    fn hint(&self, line: &str, pos: usize, ctx: &rustyline::Context) -> Option<String> {
        self.hinter.hint(line, pos, ctx)
    }
}

impl rustyline::highlight::Highlighter for Completer {
    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }

    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        self.highlighter.highlight_prompt(prompt, default)
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        // TODO Detect when windows supports ANSI escapes
        #[cfg(windows)]
        {
            Cow::Borrowed(hint)
        }
        #[cfg(not(windows))]
        {
            use ansi_term::Style;
            Cow::Owned(Style::new().dimmed().paint(hint).to_string())
        }
    }

    fn highlight_candidate<'c>(
        &self,
        candidate: &'c str,
        completion: rustyline::CompletionType,
    ) -> Cow<'c, str> {
        self.highlighter.highlight_candidate(candidate, completion)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}

impl rustyline::completion::Completer for Completer {
    type Candidate = String;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _: &rustyline::Context,
    ) -> rustyline::Result<(usize, Vec<String>)> {
        let result = complete(&self.thread, "<repl>", line, pos);

        // Get the start of the completed identifier
        let ident_start = line[..pos]
            .rfind(|c: char| c.is_whitespace() || c == '.')
            .map_or(0, |i| i + 1);
        Ok((ident_start, result.unwrap_or(Vec::new())))
    }
}

macro_rules! impl_userdata {
    ($name:ident) => {
        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, concat!(stringify!($name), "(..)"))
            }
        }
    };
}

#[derive(Userdata, Trace, VmType)]
#[gluon(vm_type = "Editor")]
#[gluon_trace(skip)]
struct Editor {
    editor: Mutex<rustyline::Editor<Completer>>,
}

impl_userdata! { Editor }

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
                vm.get_env()
                    .find_type_info(typ)
                    .unwrap()
                    .clone()
                    .into_type()
            }
        }
    };
}

define_vmtype! { ReadlineError }

impl<'vm> Pushable<'vm> for ReadlineError {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> VMResult<()> {
        gluon::vm::api::ser::Ser(self).vm_push(context)
    }
}

fn app_dir_root() -> Result<PathBuf, Box<dyn StdError>> {
    Ok(::app_dirs::app_root(
        app_dirs::AppDataType::UserData,
        &crate::APP_INFO,
    )?)
}

fn new_editor(vm: WithVM<()>) -> IO<Editor> {
    let mut editor = rustyline::Editor::new();

    let history_result =
        app_dir_root().and_then(|path| Ok(editor.load_history(&*path.join("history"))?));

    if let Err(err) = history_result {
        warn!("Unable to load history: {}", err);
    }
    editor.set_helper(Some(Completer {
        thread: vm.vm.root_thread(),
        hinter: rustyline::hint::HistoryHinter {},
        highlighter: rustyline::highlight::MatchingBracketHighlighter::default(),
    }));
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

fn eval_line(
    De(color): De<crate::Color>,
    WithVM { vm, value: line }: WithVM<&str>,
) -> impl Future<Output = IO<()>> {
    let vm = vm.new_thread().unwrap(); // TODO Reuse the current thread
    let line = line.to_string();
    async move {
        eval_line_(vm.root_thread(), &line)
            .map(move |result| match result {
                Ok(x) => IO::Value(x),
                Err(err) => {
                    let mut stderr = termcolor::StandardStream::stderr(color.into());
                    if let Err(err) = err.emit(&mut stderr) {
                        eprintln!("{}", err);
                    }
                    IO::Value(())
                }
            })
            .await
    }
}

async fn eval_line_(vm: RootedThread, line: &str) -> gluon::Result<()> {
    let mut is_let_binding = false;
    let mut eval_expr;
    let value = {
        let mut db = vm.get_database();
        let mut module_compiler = vm.module_compiler(&mut db);
        eval_expr = {
            let eval_expr = {
                mk_ast_arena!(arena);
                let repl_line = {
                    let result = {
                        let filemap = vm.get_database().add_filemap("line", line);
                        let mut module =
                            SymbolModule::new("line".into(), module_compiler.mut_symbols());
                        parse_partial_repl_line((*arena).borrow(), &mut module, &*filemap)
                    };
                    match result {
                        Ok(x) => x,
                        Err((_, err)) => {
                            let code_map = db.code_map();
                            return Err(InFile::new(code_map, err).into());
                        }
                    }
                };
                match repl_line {
                    None => return Ok(()),
                    Some(ReplLine::Expr(expr)) => RootExpr::new(arena.clone(), arena.alloc(expr)),
                    Some(ReplLine::Let(let_binding)) => {
                        is_let_binding = true;
                        // We can't compile function bindings by only looking at `let_binding.expr`
                        // so rewrite `let f x y = <expr>` into `let f x y = <expr> in f`
                        // and `let { x } = <expr>` into `let repl_temp @ { x } = <expr> in repl_temp`
                        let id = match let_binding.name.value {
                            Pattern::Ident(ref id) if !let_binding.args.is_empty() => id.clone(),
                            _ => {
                                let id = Symbol::from("repl_temp");
                                let_binding.name = pos::spanned(
                                    let_binding.name.span,
                                    Pattern::As(
                                        pos::spanned(let_binding.name.span, id.clone()),
                                        arena.alloc(let_binding.name.ast_clone(arena.borrow())),
                                    ),
                                );
                                TypedIdent {
                                    name: id,
                                    typ: let_binding.resolved_type.clone(),
                                }
                            }
                        };
                        let id = pos::spanned2(0.into(), 0.into(), Expr::Ident(id.clone()));
                        let expr = Expr::LetBindings(
                            ast::ValueBindings::Plain(let_binding),
                            arena.alloc(id),
                        );
                        let eval_expr = RootExpr::new(
                            arena.clone(),
                            arena.alloc(pos::spanned2(0.into(), 0.into(), expr)),
                        );
                        eval_expr
                    }
                }
            };
            eval_expr.try_into_send().unwrap()
        };

        (&mut eval_expr)
            .run_expr(&mut module_compiler, vm.clone(), "line", line, None)
            .await?
    };
    let ExecuteValue { value, typ, .. } = value;

    if is_let_binding {
        let mut expr = eval_expr.expr();
        let mut last_bind = None;
        loop {
            match &expr.value {
                Expr::LetBindings(binds, body) => {
                    last_bind = Some(&binds[0]);
                    expr = body;
                }
                _ => break,
            }
        }
        set_globals(
            &vm,
            &mut vm.get_database_mut(),
            &last_bind.unwrap().name,
            &typ,
            &value.as_ref(),
        )?;
    }
    let vm = value.vm();
    let env = vm.get_env();
    let debug_level = vm.global_env().get_debug_level();
    println!(
        "{}",
        ValuePrinter::new(&env, &typ, value.get_variant(), &debug_level)
            .width(80)
            .max_level(5)
    );
    Ok(())
}

fn set_globals(
    vm: &Thread,
    db: &mut CompilerDatabase,
    pattern: &SpannedPattern<Symbol>,
    typ: &ArcType,
    value: &RootedValue<&Thread>,
) -> GluonResult<()> {
    match pattern.value {
        Pattern::Ident(ref id) => {
            db.set_global(
                id.name.declared_name(),
                typ.clone(),
                Default::default(),
                value.get_value(),
            );
            Ok(())
        }
        Pattern::Tuple { ref elems, .. } => {
            let iter = elems
                .iter()
                .zip(crate::vm::dynamic::field_iter(&value, typ, vm));
            for (elem_pattern, (elem_value, elem_type)) in iter {
                set_globals(vm, db, elem_pattern, &elem_type, &elem_value)?;
            }
            Ok(())
        }
        Pattern::Record { ref fields, .. } => {
            let resolved_type = {
                let mut type_cache = vm.global_env().type_cache();
                let env = db.as_env();
                resolve::remove_aliases_cow(&env, &mut type_cache, typ)
            };

            for (name, pattern_value) in ast::pattern_values(fields) {
                let field_name: &Symbol = &name.value;
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
                match pattern_value {
                    Some(ref sub_pattern) => {
                        set_globals(vm, db, sub_pattern, &field_type, &field_value)?
                    }
                    None => db.set_global(
                        name.value.declared_name(),
                        field_type.to_owned(),
                        Default::default(),
                        field_value.get_value(),
                    ),
                }
            }
            Ok(())
        }
        Pattern::As(ref id, ref pattern) => {
            db.set_global(
                id.value.declared_name(),
                typ.clone(),
                Default::default(),
                value.get_value(),
            );
            set_globals(vm, db, pattern, typ, value)
        }
        Pattern::Constructor(..) | Pattern::Literal(_) | Pattern::Error => {
            Err(VMError::Message("The repl cannot bind variables from this pattern".into()).into())
        }
    }
}

fn finish_or_interrupt(
    thread: RootedThread,
    action: OpaqueValue<&Thread, IO<Generic<A>>>,
) -> impl Future<Output = IO<OpaqueValue<RootedThread, A>>> {
    let (sender, receiver) = oneshot::channel();

    tokio::spawn(async move {
        info!("Installed Ctrl-C handler");
        tokio::signal::ctrl_c()
            .await
            .unwrap_or_else(|err| panic!("Error installing signal handler: {}", err));
        let _ = sender.send(());
    });

    let mut action = OwnedFunction::<fn() -> IO<OpaqueValue<RootedThread, A>>>::from_value(
        &thread,
        action.get_variant(),
    );
    let action_future = tokio::spawn(async move {
        action
            .call_async()
            .await
            .unwrap_or_else(|err| IO::Exception(err.to_string()))
    })
    .map(|r| r.unwrap());

    let ctrl_c_future = receiver.map(move |next| {
        next.unwrap();
        thread.interrupt();
        IO::Exception("Interrupted".to_string())
    });

    future::select(ctrl_c_future, action_future).map(|either| either.factor_first().0)
}

fn save_history(editor: &Editor) -> IO<()> {
    let history_result = app_dir_root().and_then(|path| {
        editor
            .editor
            .lock()
            .unwrap()
            .save_history(&*path.join("history"))
            .map_err(|err| {
                let err: Box<dyn StdError> = Box::new(err);
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

    vm::ExternModule::new(
        vm,
        record!(
            type Editor => Editor,
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
            type_of_expr => primitive!(1, async fn type_of_expr),
            find_info => primitive!(1, find_info),
            find_kind => primitive!(1, find_kind),
            parse_color => primitive!(1, "parse_color", |s: &str| s.parse::<Color>()),
            switch_debug_level => primitive!(1, switch_debug_level),
            eval_line => primitive!(2, async fn eval_line),
            finish_or_interrupt => primitive!(2, async fn finish_or_interrupt),
        ),
    )
}

async fn compile_repl(vm: &Thread) -> Result<(), GluonError> {
    let rustyline_types_source = gluon::vm::api::typ::make_source::<ReadlineError>(vm)?;
    vm.load_script_async("rustyline_types", &rustyline_types_source)
        .await?;

    add_extern_module(vm, "repl.prim", load_repl);
    add_extern_module(vm, "rustyline", load_rustyline);

    const REPL_SOURCE: &'static str =
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/repl.glu"));

    vm.load_script_async("repl", REPL_SOURCE).await?;
    Ok(())
}

#[allow(dead_code)]
pub async fn run(
    color: Color,
    prompt: &str,
    debug_level: DebugLevel,
    use_std_lib: bool,
) -> gluon::Result<()> {
    let vm = gluon::VmBuilder::new().build_async().await;
    vm.global_env().set_debug_level(debug_level);
    vm.get_database_mut()
        .use_standard_lib(use_std_lib)
        .run_io(true);

    compile_repl(&vm).await?;

    let mut repl: OwnedFunction<fn(_) -> _> = vm.get_global("repl")?;
    debug!("Starting repl");
    repl.call_async(Settings { color, prompt })
        .await
        .map(|_: IO<()>| ())
        .map_err(|err| err.into())
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::vm::api::{FunctionRef, IO};
    use gluon::import::Import;
    use gluon::{self, RootedThread};

    async fn new_vm() -> RootedThread {
        if std::env::var("GLUON_PATH").is_err() {
            std::env::set_var("GLUON_PATH", "..");
        }
        let vm = gluon::new_vm_async().await;
        let import = vm.get_macros().get("import");
        import
            .as_ref()
            .and_then(|import| import.downcast_ref::<Import>())
            .expect("Import macro")
            .add_path("..");
        vm
    }

    #[tokio::test]
    async fn compile_repl_test() {
        let _ = env_logger::try_init();
        let vm = new_vm().await;
        compile_repl(&vm)
            .await
            .unwrap_or_else(|err| panic!("{}", err));
        let repl: Result<FunctionRef<fn(Settings<'static>) -> IO<()>>, _> = vm.get_global("repl");
        assert!(repl.is_ok(), "{}", repl.err().unwrap());
    }

    #[tokio::test]
    async fn record_patterns() {
        let _ = env_logger::try_init();
        let vm = new_vm().await;
        compile_repl(&vm)
            .await
            .unwrap_or_else(|err| panic!("{}", err));

        // pattern with field names out of order
        eval_line_(vm.clone(), r#"let {y, x} = {x = "x", y = "y"}"#)
            .await
            .expect("Error evaluating let binding");
        let x: String = vm.get_global("x").expect("Error getting x");
        assert_eq!(x, "x");
        let y: String = vm.get_global("y").expect("Error getting y");
        assert_eq!(y, "y");

        // pattern with field names out of order and different field types
        eval_line_(vm.clone(), r#"let {y} = {x = "x", y = ()}"#)
            .await
            .expect("Error evaluating let binding 2");
        let () = vm.get_global("y").expect("Error getting y");
    }

    type QueryFn = fn(&'static str) -> IO<Result<String, String>>;

    #[tokio::test]
    async fn type_of_expr() {
        let _ = env_logger::try_init();
        let vm = new_vm().await;
        compile_repl(&vm)
            .await
            .unwrap_or_else(|err| panic!("{}", err));
        let mut type_of: FunctionRef<QueryFn> = vm.get_global("repl.prim.type_of_expr").unwrap();
        assert_eq!(
            type_of.call_async("123").await,
            Ok(IO::Value(Ok("Int".into())))
        );
    }

    #[tokio::test]
    async fn find_kind() {
        let _ = env_logger::try_init();
        let vm = new_vm().await;
        compile_repl(&vm)
            .await
            .unwrap_or_else(|err| panic!("{}", err));
        let mut find_kind: FunctionRef<QueryFn> = vm.get_global("repl.prim.find_kind").unwrap();
        assert_eq!(
            find_kind.call_async("std.prelude.Semigroup").await,
            Ok(IO::Value(Ok("Type -> Type".into())))
        );
    }

    #[tokio::test]
    async fn find_info() {
        let _ = env_logger::try_init();
        let vm = new_vm().await;
        compile_repl(&vm)
            .await
            .unwrap_or_else(|err| panic!("{}", err));
        let mut find_info: FunctionRef<QueryFn> = vm.get_global("repl.prim.find_info").unwrap();
        match find_info.call_async("std.prelude.Semigroup").await {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call_async("std.prelude.empty").await {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call_async("std.float.prim").await {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
    }

    #[tokio::test]
    async fn complete_repl_empty() {
        let _ = env_logger::try_init();
        let vm = new_vm().await;
        compile_repl(&vm)
            .await
            .unwrap_or_else(|err| panic!("{}", err));
        complete(&vm, "<repl>", "", 0).unwrap_or_else(|err| panic!("{}", err));
    }
}
