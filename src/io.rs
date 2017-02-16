use std::string::String as StdString;
use std::io::{Read, stdin};
use std::fmt;
use std::fs::File;
use std::sync::Mutex;

use vm::{self, Result, Variants};
use vm::gc::{Gc, Traverseable};
use vm::types::*;
use vm::thread::ThreadInternal;
use vm::thread::{Thread, Status};
use vm::api::{Array, Hole, VmType, Getable, OpaqueValue, Pushable, IO, WithVM, Userdata, primitive};
use vm::api::generic::{A, B};
use vm::stack::StackFrame;
use vm::internal::ValuePrinter;

use vm::internal::Value;

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
                IO::Value(Getable::from_value(vm, Variants::new(&Value::Array(value)))
                    .expect("Array"))
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
        Some(result) => {
            match result {
                Ok(b) => {
                    ::std::char::from_u32(b as u32)
                        .map(IO::Value)
                        .unwrap_or_else(|| IO::Exception("Not a valid char".into()))
                }
                Err(err) => IO::Exception(format!("{}", err)),
            }
        }
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
extern "C" fn catch_io(vm: &Thread) -> Status {
    let mut context = vm.context();
    let frame_level = context.stack.get_frames().len();
    let action = StackFrame::current(&mut context.stack)[0];
    context.stack.push(action);
    0.push(vm, &mut context).unwrap();
    match vm.call_function(context, 1) {
        Ok(_) => Status::Ok,
        Err(err) => {
            let mut context = vm.context();
            {
                let mut stack = StackFrame::current(&mut context.stack);
                while stack.stack.get_frames().len() > frame_level {
                    if stack.exit_scope().is_err() {
                        return Status::Error;
                    }
                }
                let callback = stack[1];
                stack.push(callback);
            }
            let fmt = format!("{}", err);
            let _ = fmt.push(vm, &mut context);
            0.push(vm, &mut context).unwrap();
            match vm.call_function(context, 2) {
                Ok(_) => Status::Ok,
                Err(err) => {
                    context = vm.context();
                    let fmt = format!("{}", err);
                    let _ = fmt.push(vm, &mut context);
                    Status::Error
                }
            }
        }
    }
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

fn run_expr(WithVM { vm, value: expr }: WithVM<&str>) -> IO<String> {
    let frame_level = vm.context().stack.get_frames().len();
    let run_result = Compiler::new().run_expr::<OpaqueValue<&Thread, Hole>>(vm, "<top>", expr);
    let mut context = vm.context();
    let stack = StackFrame::current(&mut context.stack);
    match run_result {
        Ok((value, typ)) => {
            let env = vm.global_env().get_env();
            unsafe {
                IO::Value(format!("{} : {}",
                                  ValuePrinter::new(&*env, &typ, value.get_value()).width(80),
                                  typ))
            }
        }
        Err(err) => clear_frames(err, frame_level, stack),
    }
}

fn load_script(WithVM { vm, value: name }: WithVM<&str>, expr: &str) -> IO<String> {
    let frame_level = vm.context().stack.get_frames().len();
    let run_result = Compiler::new().load_script_async(vm, name, expr).sync_or_error();
    let mut context = vm.context();
    let stack = StackFrame::current(&mut context.stack);
    match run_result {
        Ok(()) => IO::Value(format!("Loaded {}", name)),
        Err(err) => clear_frames(err, frame_level, stack),
    }
}

pub fn load(vm: &Thread) -> Result<()> {

    vm.register_type::<GluonFile>("File", &[])?;

    // io_flat_map f m : (a -> IO b) -> IO a -> IO b
    //     = f (m ())
    let io_flat_map = vec![// [f, m, ()]       Initial stack
                           Call(1), // [f, m_ret]       Call m ()
                           PushInt(0), // [f, m_ret, ()]   Add a dummy argument ()
                           TailCall(2) /* [f_ret]          Call f m_ret () */];
    let io_flat_map_type = <fn (fn (A) -> IO<B>, IO<A>) -> IO<B> as VmType>::make_type(vm);
    vm.add_bytecode("io_flat_map", io_flat_map_type, 3, io_flat_map)?;


    vm.add_bytecode("io_pure",
                      <fn(A) -> IO<A> as VmType>::make_type(vm),
                      2,
                      vec![Pop(1)])?;
    // IO functions
    vm.define_global("io",
                       record!(
        open_file => primitive!(1 open_file),
        read_file => primitive!(2 read_file),
        read_file_to_string => primitive!(1 read_file_to_string),
        read_char => primitive!(0 read_char),
        read_line => primitive!(0 read_line),
        print => primitive!(1 print),
        println => primitive!(1 println),
        catch =>
            primitive::<fn (IO<A>, fn (StdString) -> IO<A>) -> IO<A>>("io.catch", catch_io),
        run_expr => primitive!(1 run_expr),
        load_script => primitive!(2 load_script)
    ))?;
    Ok(())
}
