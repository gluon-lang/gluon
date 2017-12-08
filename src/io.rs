use std::io::{stdin, Read};
use std::fmt;
use std::fs::File;
use std::sync::Mutex;

use futures::{Future, IntoFuture};
use futures::future::Either;

use vm::{self, ExternModule, Result, Variants};
use vm::future::FutureValue;
use vm::gc::{Gc, Traverseable};
use vm::types::*;
use vm::thread::{RootedThread, Thread, ThreadInternal};
use vm::api::{Array, FutureResult, Generic, Getable, OpaqueValue, OwnedFunction, TypedBytecode,
              Userdata, VmType, WithVM, IO};
use vm::api::generic::{A, B};
use vm::stack::StackFrame;
use vm::internal::ValuePrinter;

use vm::internal::Value;

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

struct GluonFile(Mutex<File>);

impl Userdata for GluonFile {}

impl fmt::Debug for GluonFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "File")
    }
}

impl VmType for GluonFile {
    type Type = GluonFile;
}

impl Traverseable for GluonFile {
    fn traverse(&self, _: &mut Gc) {}
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
            Ok(bytes_read) => {
                let value = {
                    let mut context = vm.context();
                    match context.alloc(&buffer[..bytes_read]) {
                        Ok(value) => value,
                        Err(err) => return IO::Exception(format!("{}", err)),
                    }
                };
                IO::Value(
                    Getable::from_value(vm, Variants::new(&Value::Array(value))).expect("Array"),
                )
            }
            Err(err) => IO::Exception(format!("{}", err)),
        }
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
    match stdin().bytes().next() {
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
    match stdin().read_line(&mut buffer) {
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
    mut catch: OwnedFunction<fn(String) -> IO<Generic<A>>>,
) -> FutureResult<Box<Future<Item = IO<Generic<A>>, Error = vm::Error> + Send>> {
    let vm = action.vm().root_thread();
    let frame_level = vm.context().stack.get_frames().len();
    let mut action: OwnedFunction<fn(()) -> Generic<A>> =
        unsafe { Getable::from_value(&vm, Variants::new(&action.get_value())).unwrap() };

    let future = action.call_async(()).then(move |result| match result {
        Ok(value) => Either::A(Ok(IO::Value(value)).into_future()),
        Err(err) => {
            {
                let mut context = vm.context();
                let mut stack = StackFrame::current(&mut context.stack);
                while stack.stack.get_frames().len() > frame_level {
                    if stack.exit_scope().is_err() {
                        return Either::A(Ok(IO::Exception("Unknown error".into())).into_future());
                    }
                }
            }
            Either::B(catch.call_async(format!("{}", err)).then(|result| {
                Ok(match result {
                    Ok(value) => value,
                    Err(err) => IO::Exception(format!("{}", err)),
                })
            }))
        }
    });

    FutureResult(Box::new(future))
}

fn clear_frames(err: Error, frame_level: usize, mut stack: StackFrame) -> IO<String> {
    let fmt = match err {
        Error::VM(vm::Error::Panic(_)) => {
            let trace = stack.stack.stacktrace(frame_level);
            format!("{}\n{}", err, trace)
        }
        _ => format!("{}", err),
    };
    while stack.stack.get_frames().len() > frame_level {
        if stack.exit_scope().is_err() {
            return IO::Exception(fmt);
        }
    }
    IO::Exception(fmt)
}

fn run_expr(
    WithVM { vm, value: expr }: WithVM<&str>,
) -> FutureValue<Box<Future<Item = IO<String>, Error = vm::Error> + Send>> {
    let vm = vm.root_thread();
    let frame_level = vm.context().stack.get_frames().len();

    let vm1 = vm.clone();
    let future = expr.run_expr(&mut Compiler::new(), vm1, "<top>", expr, None)
        .then(move |run_result| {
            let mut context = vm.context();
            let stack = StackFrame::current(&mut context.stack);
            FutureValue::sync(Ok(match run_result {
                Ok(execute_value) => {
                    let env = vm.global_env().get_env();
                    let typ = execute_value.typ;
                    IO::Value(format!(
                        "{} : {}",
                        ValuePrinter::new(&*env, &typ, *execute_value.value).width(80),
                        typ
                    ))
                }
                Err(err) => clear_frames(err, frame_level, stack),
            }))
        });

    future.boxed()
}

fn load_script(
    WithVM { vm, value: name }: WithVM<&str>,
    expr: &str,
) -> FutureValue<Box<Future<Item = IO<String>, Error = vm::Error> + Send>> {
    let frame_level = vm.context().stack.get_frames().len();

    let vm1 = vm.root_thread();
    let vm = vm.root_thread();
    let name = name.to_string();
    let future = expr.load_script(&mut Compiler::new(), vm1, &name, expr, None)
        .then(move |run_result| {
            let mut context = vm.context();
            let stack = StackFrame::current(&mut context.stack);
            let io = match run_result {
                Ok(()) => IO::Value(format!("Loaded {}", name)),
                Err(err) => clear_frames(err, frame_level, stack),
            };
            Ok(io).into()
        });
    future.boxed()
}

fn new_thread(WithVM { vm, .. }: WithVM<()>) -> IO<RootedThread> {
    match vm.new_thread() {
        Ok(thread) => IO::Value(thread),
        Err(err) => IO::Exception(err.to_string()),
    }
}

fn new_interruptible_thread(WithVM { vm, .. }: WithVM<()>) -> IO<RootedThread> {
    use vm::thread::HookFlags;
    use futures::Async;

    match vm.new_thread() {
        Ok(thread) => {
            {
                let mut context = thread.context();

                let mut i = 0;
                context.set_hook(Some(Box::new(move |_, _| {
                    i += 1;
                    if i == 100 {
                        i = 0;
                        Ok(Async::NotReady)
                    } else {
                        Ok(Async::Ready(()))
                    }
                })));
                context.set_hook_mask(HookFlags::CALL_FLAG);
            }

            IO::Value(thread)
        }
        Err(err) => IO::Exception(err.to_string()),
    }
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
            flat_map => TypedBytecode::<FlatMap>::new("std.io.prim.flat_map", 3, flat_map),
            wrap => TypedBytecode::<Wrap>::new("std.io.prim.wrap", 2, wrap),
            open_file => primitive!(1 std::io::prim::open_file),
            read_file => primitive!(2 std::io::prim::read_file),
            read_file_to_string => primitive!(1 std::io::prim::read_file_to_string),
            read_char => primitive!(0 std::io::prim::read_char),
            read_line => primitive!(0 std::io::prim::read_line),
            print => primitive!(1 std::io::prim::print),
            println => primitive!(1 std::io::prim::println),
            catch => primitive!(2 std::io::prim::catch),
            run_expr => primitive!(1 std::io::prim::run_expr),
            load_script => primitive!(2 std::io::prim::load_script),
            new_thread => primitive!(1 std::io::prim::new_thread),
            new_interruptible_thread => primitive!(1 std::io::prim::new_interruptible_thread)
        },
    )
}
