use crate::real_std::{
    fmt,
    fs::{self, File},
    io::{self, Read, Write},
    sync::Mutex,
};

use futures::prelude::*;

use futures::Future;

use crate::vm::{
    self,
    api::{
        generic::{A, B},
        Getable, OpaqueValue, OwnedFunction, RuntimeResult, TypedBytecode, WithVM, IO,
    },
    internal::ValuePrinter,
    stack::{self, StackFrame},
    thread::{RootedThread, Thread, ThreadInternal},
    types::*,
    ExternModule, Result,
};

use crate::{compiler_pipeline::*, Error, ModuleCompiler, ThreadExt};

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

#[derive(Userdata, Trace, VmType)]
#[gluon(vm_type = "std.io.File")]
#[gluon(crate_name = "::vm")]
#[gluon_trace(skip)]
struct GluonFile(Mutex<Option<File>>);

macro_rules! unwrap_file {
    ($file: expr) => {{
        match *$file {
            Some(ref mut file) => file,
            None => return IO::Value(RuntimeResult::Panic("the file has been closed".to_owned())),
        }
    }};
}

impl fmt::Debug for GluonFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "File")
    }
}

#[derive(Getable, VmType, Clone, Copy)]
#[gluon(crate_name = "::vm")]
enum OpenOptions {
    Read,
    Write,
    Append,
    Truncate,
    Create,
    CreateNew,
}

fn open_file_with(path: &str, opts: Vec<OpenOptions>) -> IO<GluonFile> {
    let mut open_with = fs::OpenOptions::new();

    for opt in opts {
        match opt {
            OpenOptions::Read => open_with.read(true),
            OpenOptions::Write => open_with.write(true),
            OpenOptions::Append => open_with.append(true),
            OpenOptions::Truncate => open_with.truncate(true),
            OpenOptions::Create => open_with.create(true),
            OpenOptions::CreateNew => open_with.create_new(true),
        };
    }

    open_with
        .open(path)
        .map(|file| GluonFile(Mutex::new(Some(file))))
        .into()
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
            use crate::real_std::fmt::Write;
            buffer.clear();
            let _ = write!(&mut buffer, "{}", err);
            IO::Exception(buffer)
        }
    }
}

fn read_file(file: &GluonFile, count: usize) -> IO<RuntimeResult<Option<Vec<u8>>, String>> {
    let mut file = file.0.lock().unwrap();
    let file = unwrap_file!(file);
    let mut buffer = Vec::with_capacity(count);

    unsafe {
        buffer.set_len(count);
        match file.read(&mut *buffer) {
            Ok(bytes_read) if bytes_read == 0 => IO::Value(RuntimeResult::Return(None)),
            Ok(bytes_read) => {
                buffer.truncate(bytes_read);
                IO::Value(RuntimeResult::Return(Some(buffer)))
            }
            Err(err) => IO::Exception(format!("{}", err)),
        }
    }
}

fn read_file_to_end(file: &GluonFile) -> IO<RuntimeResult<Vec<u8>, String>> {
    let mut file = file.0.lock().unwrap();
    let file = unwrap_file!(file);
    let mut buf = Vec::new();

    match file.read_to_end(&mut buf) {
        Ok(_) => IO::Value(RuntimeResult::Return(buf)),
        Err(err) => IO::Exception(err.to_string()),
    }
}

fn write_slice_file(
    file: &GluonFile,
    buf: &[u8],
    start: usize,
    end: usize,
) -> IO<RuntimeResult<usize, String>> {
    if start > end {
        return IO::Value(RuntimeResult::Panic(format!(
            "slice index starts at {} but ends at {}",
            start, end
        )));
    }

    if end > buf.len() {
        return IO::Value(RuntimeResult::Panic(format!(
            "index {} is out of range for array of length {}",
            end,
            buf.len()
        )));
    }

    let mut file = file.0.lock().unwrap();
    let file = unwrap_file!(file);

    match file.write(&buf[start..end]) {
        Ok(bytes_written) => IO::Value(RuntimeResult::Return(bytes_written)),
        Err(why) => IO::Exception(why.to_string()),
    }
}

fn flush_file(file: &GluonFile) -> IO<RuntimeResult<(), String>> {
    let mut file = file.0.lock().unwrap();

    match unwrap_file!(file).flush() {
        Ok(_) => IO::Value(RuntimeResult::Return(())),
        Err(why) => IO::Exception(why.to_string()),
    }
}

fn close_file(file: &GluonFile) -> IO<()> {
    let mut file = file.0.lock().unwrap();

    match file.take() {
        Some(mut file) => file.flush().into(),
        None => IO::Value(()),
    }
}

fn is_file_closed(file: &GluonFile) -> bool {
    file.0.lock().unwrap().is_none()
}

fn read_char() -> IO<char> {
    match io::stdin().bytes().next() {
        Some(result) => match result {
            Ok(b) => crate::real_std::char::from_u32(b as u32)
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
            use crate::real_std::fmt::Write;
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
) -> impl Future<Output = IO<OpaqueValue<RootedThread, A>>> + Send {
    let vm = action.vm().root_thread();
    let frame_level = vm.context().frame_level();
    let mut action: OwnedFunction<fn(()) -> OpaqueValue<RootedThread, A>> =
        Getable::from_value(&vm, action.get_variant());

    async move {
        match action.call_async(()).await {
            Ok(value) => IO::Value(value),
            Err(err) => {
                {
                    let mut context = vm.context();
                    {
                        let stack = context.stack_frame::<stack::State>();

                        if let Err(err) = crate::vm::thread::reset_stack(stack, frame_level) {
                            return IO::Exception(err.to_string().into());
                        }
                    }

                    let mut stack = context.stack_frame::<stack::State>();
                    let len = stack.len();
                    stack.pop_many(len - 3);
                }

                let err = format!("{}", err);
                match catch.call_async(err).await {
                    Ok(value) => value,
                    Err(err) => IO::Exception(format!("{}", err)),
                }
            }
        }
    }
}

fn throw(msg: String) -> IO<OpaqueValue<RootedThread, A>> {
    IO::Exception(msg)
}

fn clear_frames<T>(mut err: Error, stack: StackFrame) -> IO<T> {
    let new_trace = match crate::vm::thread::reset_stack(stack, 1) {
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
type RunExpr = record_type! { value => String, typ => String };

fn run_expr(WithVM { vm, value: expr }: WithVM<&str>) -> impl Future<Output = IO<RunExpr>> {
    let vm = vm.root_thread();
    let vm1 = vm.clone();
    let expr = expr.to_owned(); // FIXME
    async move {
        let mut db = vm.get_database();
        expr.run_expr(&mut ModuleCompiler::new(&mut db), vm1, "<top>", &expr, None)
            .map(|run_result| {
                let mut context = vm.context();
                let stack = context.stack_frame::<stack::State>();
                match run_result {
                    Ok(execute_value) => {
                        let env = vm.get_env();
                        let typ = execute_value.typ;
                        let debug_level = vm.global_env().get_debug_level();
                        IO::Value(record_no_decl!{
                            value => ValuePrinter::new(&env, &typ, execute_value.value.get_variant(), &debug_level).width(80).to_string(),
                            typ => typ.to_string()
                        })
                    }
                    Err(err) => clear_frames(err, stack),
                }
            }).await
    }
}

fn load_script(
    WithVM { vm, value: name }: WithVM<&str>,
    expr: &str,
) -> impl Future<Output = IO<String>> {
    let vm1 = vm.root_thread();
    let vm = vm.root_thread();
    let name = name.to_string();
    let expr = expr.to_owned(); // FIXME

    async move {
        let mut db = vm.get_database();
        expr.load_script(&mut ModuleCompiler::new(&mut db), vm1, &name, &expr, None)
            .map(|run_result| {
                let mut context = vm.context();
                let stack = context.stack_frame::<stack::State>();
                let io = match run_result {
                    Ok(()) => IO::Value(format!("Loaded {}", name)),
                    Err(err) => clear_frames(err, stack),
                };
                io
            })
            .await
    }
}

mod std {
    pub mod io {
        pub use crate::std_lib::io as prim;
    }
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    vm.register_type::<GluonFile>("std.io.File", &[])?;

    // flat_map f m : (a -> IO b) -> IO a -> IO b
    //     = f (m ())
    let flat_map = vec![
        // [f, m, ()]       Initial stack
        Call(1),     // [f, m_ret]       Call m ()
        PushInt(0),  // [f, m_ret, ()]   Add a dummy argument ()
        TailCall(2), /* [f_ret]          Call f m_ret () */
        Return,
    ];

    type FlatMap = fn(fn(A) -> IO<B>, IO<A>) -> IO<B>;
    type Wrap = fn(A) -> IO<A>;

    let wrap = vec![Pop(1), Return];

    // IO functions
    ExternModule::new(
        vm,
        record! {
            type std::io::File => GluonFile,
            type OpenOptions => OpenOptions,
            type std::io::IO a => IO<A>,
            flat_map => TypedBytecode::<FlatMap>::new("std.io.prim.flat_map", 3, flat_map),
            wrap => TypedBytecode::<Wrap>::new("std.io.prim.wrap", 2, wrap),
            open_file_with => primitive!(2, std::io::prim::open_file_with),
            read_file_to_string => primitive!(1, std::io::prim::read_file_to_string),
            read_file_to_array => primitive!(1, std::io::prim::read_file_to_array),
            read_file => primitive!(2, std::io::prim::read_file),
            read_file_to_end => primitive!(1, std::io::prim::read_file_to_end),
            write_slice_file => primitive!(4, std::io::prim::write_slice_file),
            flush_file => primitive!(1, std::io::prim::flush_file),
            close_file => primitive!(1, std::io::prim::close_file),
            is_file_closed => primitive!(1, std::io::prim::is_file_closed),
            read_char => primitive!(0, std::io::prim::read_char),
            read_line => primitive!(0, std::io::prim::read_line),
            print => primitive!(1, std::io::prim::print),
            println => primitive!(1, std::io::prim::println),
            flush_stdout => primitive!(0, std::io::prim::flush_stdout),
            eprint => primitive!(1, std::io::prim::eprint),
            eprintln => primitive!(1, std::io::prim::eprintln),
            catch => primitive!(2, async fn std::io::prim::catch),
            throw => primitive!(1, std::io::prim::throw),
            run_expr => primitive!(1, async fn std::io::prim::run_expr),
            load_script => primitive!(2, async fn std::io::prim::load_script),
            default_buf_len => 8192,
        },
    )
}
