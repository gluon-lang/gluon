use std::fmt;
use std::fs::File;
use std::io::{self, Read, Write};
use std::sync::Mutex;

use futures::{
    future::{self, Either},
    Future,
};

use vm::api::generic::{A, B};
use vm::api::{self, Array, Getable, OpaqueValue, OwnedFunction, TypedBytecode, WithVM, IO};
use vm::internal::ValuePrinter;
use vm::stack::{self, StackFrame};
use vm::thread::{RootedThread, Thread, ThreadInternal};
use vm::types::*;
use vm::{self, ExternModule, Result};

use compiler_pipeline::*;

use super::{Compiler, Error};

fn print(s: &str) -> IO<()> {
    print!("{}", s);
    IO::Value(())
}

fn println(s: &str) -> IO<()> {
    println!("{}", s);
    IO::Value(())
}

fn flush_stdout() -> IO<()> {
    match io::stdout().flush() {
        Ok(_) => IO::Value(()),
        Err(err) => IO::Exception(err.to_string()),
    }
}

fn eprint(s: &str) -> IO<()> {
    eprint!("{}", s);
    IO::Value(())
}

fn eprintln(s: &str) -> IO<()> {
    eprintln!("{}", s);
    IO::Value(())
}

#[derive(Userdata)]
#[gluon(crate_name = "::vm")]
struct GluonFile(Mutex<File>);

impl fmt::Debug for GluonFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "File")
    }
}

fn open_file(s: &str) -> IO<GluonFile> {
    match File::open(s) {
        Ok(f) => IO::Value(GluonFile(Mutex::new(f))),
        Err(err) => IO::Exception(format!("{}", err)),
    }
}

fn read_file<'vm>(file: WithVM<'vm, &GluonFile>, count: usize) -> IO<Array<'vm, u8>> {
    let WithVM { vm, value: file } = file;
    let mut file = file.0.lock().unwrap();
    let mut buffer = Vec::with_capacity(count);
    unsafe {
        buffer.set_len(count);
        match file.read(&mut *buffer) {
            Ok(bytes_read) => match api::convert::<_, Array<u8>>(vm, &buffer[..bytes_read]) {
                Ok(v) => IO::Value(v),
                Err(err) => IO::Exception(format!("{}", err)),
            },
            Err(err) => IO::Exception(format!("{}", err)),
        }
    }
}

fn read_file_to_array(s: &str) -> IO<Vec<u8>> {
    let mut buffer = Vec::new();
    match File::open(s).and_then(|mut file| file.read_to_end(&mut buffer)) {
        Ok(_) => IO::Value(buffer),
        Err(err) => IO::Exception(err.to_string()),
    }
}

fn read_file_to_string(s: &str) -> IO<String> {
    let mut buffer = String::new();
    match File::open(s).and_then(|mut file| file.read_to_string(&mut buffer)) {
        Ok(_) => IO::Value(buffer),
        Err(err) => {
            use std::fmt::Write;
            buffer.clear();
            let _ = write!(&mut buffer, "{}", err);
            IO::Exception(buffer)
        }
    }
}

fn read_char() -> IO<char> {
    match io::stdin().bytes().next() {
        Some(result) => match result {
            Ok(b) => ::std::char::from_u32(b as u32)
                .map(IO::Value)
                .unwrap_or_else(|| IO::Exception("Not a valid char".into())),
            Err(err) => IO::Exception(format!("{}", err)),
        },
        None => IO::Exception("No read".into()),
    }
}

fn read_line() -> IO<String> {
    let mut buffer = String::new();
    match io::stdin().read_line(&mut buffer) {
        Ok(_) => IO::Value(buffer),
        Err(err) => {
            use std::fmt::Write;
            buffer.clear();
            let _ = write!(&mut buffer, "{}", err);
            IO::Exception(buffer)
        }
    }
}

/// IO a -> (String -> IO a) -> IO a
fn catch<'vm>(
    action: OpaqueValue<&'vm Thread, IO<A>>,
    mut catch: OwnedFunction<fn(String) -> IO<OpaqueValue<RootedThread, A>>>,
) -> impl Future<Item = IO<OpaqueValue<RootedThread, A>>, Error = vm::Error> {
    let vm = action.vm().root_thread();
    let frame_level = vm.context().frame_level();
    let mut action: OwnedFunction<fn(()) -> OpaqueValue<RootedThread, A>> =
        Getable::from_value(&vm, action.get_variant());

    action.call_fast_async(()).then(move |result| match result {
        Ok(value) => Either::A(future::ok(IO::Value(value))),
        Err(err) => {
            {
                let mut context = vm.context();
                {
                    let mut stack = context.stack_frame::<stack::State>();

                    if let Err(err) = ::vm::thread::reset_stack(stack, frame_level) {
                        return Either::A(future::ok(IO::Exception(err.to_string().into())));
                    }
                }

                let mut stack = context.stack_frame::<stack::State>();
                let len = stack.len();
                stack.pop_many(len - 2);
            }
            Either::B(catch.call_fast_async(format!("{}", err)).then(|result| {
                Ok(match result {
                    Ok(value) => value,
                    Err(err) => IO::Exception(format!("{}", err)),
                })
            }))
        }
    })
}

fn clear_frames<T>(mut err: Error, stack: StackFrame) -> IO<T> {
    let new_trace = match ::vm::thread::reset_stack(stack, 1) {
        Ok(x) => x,
        Err(err) => return IO::Exception(err.to_string()),
    };
    match err {
        // Ignore the stacktrace as we take a more specific range of the stack here
        Error::VM(vm::Error::Panic(_, ref mut trace)) => *trace = Some(new_trace),
        _ => (),
    }
    IO::Exception(err.to_string())
}

field_decl! { value, typ }

// Can't create a minimal reproduction for why this reports as being unused...
#[allow(dead_code)]
type RunExpr = record_type!{ value => String, typ => String };

fn run_expr(
    WithVM { vm, value: expr }: WithVM<&str>,
) -> impl Future<Item = IO<RunExpr>, Error = vm::Error> {
    let vm = vm.root_thread();

    let vm1 = vm.clone();
    expr.run_expr(&mut Compiler::new().run_io(true), vm1, "<top>", expr, None)
        .then(move |run_result| {
            let mut context = vm.context();
            let stack = context.stack_frame::<stack::State>();
            Ok(match run_result {
                Ok(execute_value) => {
                    let env = vm.global_env().get_env();
                    let typ = execute_value.typ;
                    IO::Value(record_no_decl!{
                        value => ValuePrinter::new(&*env, &typ, execute_value.value.get_variant()).width(80).to_string(),
                        typ => typ.to_string()
                    })
                }
                Err(err) => clear_frames(err, stack),
            })
        })
}

fn load_script(
    WithVM { vm, value: name }: WithVM<&str>,
    expr: &str,
) -> impl Future<Item = IO<String>, Error = vm::Error> {
    let vm1 = vm.root_thread();
    let vm = vm.root_thread();
    let name = name.to_string();
    expr.load_script(&mut Compiler::new(), vm1, &name, expr, None)
        .then(move |run_result| {
            let mut context = vm.context();
            let stack = context.stack_frame::<stack::State>();
            let io = match run_result {
                Ok(()) => IO::Value(format!("Loaded {}", name)),
                Err(err) => clear_frames(err, stack),
            };
            Ok(io)
        })
}

mod std {
    pub mod io {
        pub use io as prim;
    }
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    vm.register_type::<GluonFile>("File", &[])?;

    // flat_map f m : (a -> IO b) -> IO a -> IO b
    //     = f (m ())
    let flat_map = vec![
        // [f, m, ()]       Initial stack
        Call(1),     // [f, m_ret]       Call m ()
        PushInt(0),  // [f, m_ret, ()]   Add a dummy argument ()
        TailCall(2), /* [f_ret]          Call f m_ret () */
    ];

    type FlatMap = fn(fn(A) -> IO<B>, IO<A>) -> IO<B>;
    type Wrap = fn(A) -> IO<A>;

    let wrap = vec![Pop(1)];

    use self::std;

    // IO functions
    ExternModule::new(
        vm,
        record! {
            type File => GluonFile,
            flat_map => TypedBytecode::<FlatMap>::new("std.io.prim.flat_map", 3, flat_map),
            wrap => TypedBytecode::<Wrap>::new("std.io.prim.wrap", 2, wrap),
            open_file => primitive!(1, std::io::prim::open_file),
            read_file => primitive!(2, std::io::prim::read_file),
            read_file_to_string => primitive!(1, std::io::prim::read_file_to_string),
            read_file_to_array => primitive!(1, std::io::prim::read_file_to_array),
            read_char => primitive!(0, std::io::prim::read_char),
            read_line => primitive!(0, std::io::prim::read_line),
            print => primitive!(1, std::io::prim::print),
            println => primitive!(1, std::io::prim::println),
            flush_stdout => primitive!(0, std::io::prim::flush_stdout),
            eprint => primitive!(1, std::io::prim::eprint),
            eprintln => primitive!(1, std::io::prim::eprintln),
            catch => primitive!(2, async fn std::io::prim::catch),
            run_expr => primitive!(1, async fn std::io::prim::run_expr),
            load_script => primitive!(2, async fn std::io::prim::load_script),
        },
    )
}
