use std::string::String as StdString;
use std::result::Result as StdResult;
use std::io::{Read, stdin};
use std::fmt;
use std::fs::File;
use std::sync::Mutex;

use vm::{Result, Variants};
use vm::gc::{Gc, Traverseable};
use vm::types::*;
use vm::thread::ThreadInternal;
use vm::thread::{Thread, Status};
use vm::api::{Array, Generic, VMType, Getable, Pushable, MaybeError, WithVM, Userdata, primitive};
use vm::api::generic::A;

use vm::internal::Value;

use super::Compiler;

fn print_int(i: VMInt) {
    print!("{}", i);
}

fn print(s: &str) {
    println!("{}", &*s);
}

struct GluonFile(Mutex<File>);

impl fmt::Debug for GluonFile {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "File")
    }
}

impl VMType for GluonFile {
    type Type = GluonFile;
}

impl Traverseable for GluonFile {
    fn traverse(&self, _: &mut Gc) {}
}

fn open_file(s: &str) -> MaybeError<Userdata<GluonFile>, String> {
    match File::open(s) {
        Ok(f) => MaybeError::Ok(Userdata(GluonFile(Mutex::new(f)))),
        Err(err) => MaybeError::Err(format!("{}", err)),
    }
}

fn read_file<'vm>(file: WithVM<'vm, &GluonFile>, count: usize) -> MaybeError<Array<'vm, u8>, String> {
    let WithVM { vm, value: file } = file;
    let mut file = file.0.lock().unwrap();
    let mut buffer = Vec::with_capacity(count);
    unsafe {
        buffer.set_len(count);
        match file.read(&mut *buffer) {
            Ok(bytes_read) => {
                let value = {
                    let stack = vm.get_stack();
                    vm.alloc(&stack, &buffer[..bytes_read])
                };
                MaybeError::Ok(Getable::from_value(vm, Variants::new(&Value::Array(value)))
                              .expect("Array"))
            }
            Err(err) => MaybeError::Err(format!("{}", err)),
        }
    }
}

fn read_file_to_string(s: &str) -> MaybeError<String, String> {
    let mut buffer = String::new();
    match File::open(s).and_then(|mut file| file.read_to_string(&mut buffer)) {
        Ok(_) => MaybeError::Ok(buffer),
        Err(err) => {
            use std::fmt::Write;
            buffer.clear();
            let _ = write!(&mut buffer, "{}", err);
            MaybeError::Err(buffer)
        }
    }
}

fn read_char() -> MaybeError<char, String> {
    match stdin().bytes().next() {
        Some(result) => {
            match result {
                Ok(b) => ::std::char::from_u32(b as u32).map(MaybeError::Ok)
                        .unwrap_or_else(|| MaybeError::Err("Not a valid char".into())),
                Err(err) => MaybeError::Err(format!("{}", err)),
            }
        }
        None => MaybeError::Err("No read".into()),
    }
}

fn read_line() -> MaybeError<String, String> {
    let mut buffer = String::new();
    match stdin().read_line(&mut buffer) {
        Ok(_) => MaybeError::Ok(buffer),
        Err(err) => {
            use std::fmt::Write;
            buffer.clear();
            let _ = write!(&mut buffer, "{}", err);
            MaybeError::Err(buffer)
        }
    }
}

/// (() -> a) -> (String -> a) -> a
fn catch_io(vm: &Thread) -> Status {
    let mut stack = vm.current_frame();
    let frame_level = stack.stack.get_frames().len();
    let action = stack[0];
    stack.push(action);
    0.push(vm, &mut stack.stack);
    match vm.call_function(stack, 1) {
        Ok(_) => Status::Ok,
        Err(err) => {
            stack = vm.current_frame();
            while stack.stack.get_frames().len() > frame_level {
                match stack.exit_scope() {
                    Some(new_stack) => stack = new_stack,
                    None => return Status::Error,
                }
            }
            let callback = stack[1];
            stack.push(callback);
            let fmt = format!("{}", err);
            fmt.push(vm, &mut stack.stack);
            0.push(vm, &mut stack.stack);
            match vm.call_function(stack, 1) {
                Ok(_) => Status::Ok,
                Err(err) => {
                    stack = vm.current_frame();
                    let fmt = format!("{}", err);
                    fmt.push(vm, &mut stack.stack);
                    Status::Error
                }
            }
        }
    }
}

fn run_expr(expr: WithVM<&str>) -> MaybeError<String, String> {
    let WithVM { vm, value: expr } = expr;
    let mut stack = vm.current_frame();
    let frame_level = stack.stack.get_frames().len();
    drop(stack);
    let run_result: StdResult<Generic<A>, _> = Compiler::new().run_expr(vm, "<top>", &expr);
    stack = vm.current_frame();
    match run_result {
        Ok(value) => MaybeError::Ok(format!("{:?}", value.0)),
        Err(err) => {
            let trace = stack.stacktrace(frame_level);
            let fmt = format!("{}\n{}", err, trace);
            while stack.stack.get_frames().len() > frame_level {
                match stack.exit_scope() {
                    Some(new_stack) => stack = new_stack,
                    None => return MaybeError::Err(fmt),
                }
            }
            MaybeError::Err(fmt)
        }
    }
}

fn load_script(name: WithVM<&str>, expr: &str) -> MaybeError<String, String> {
    let WithVM { vm, value: name } = name;
    let mut stack = vm.current_frame();
    let frame_level = stack.stack.get_frames().len();
    drop(stack);
    let run_result = Compiler::new().load_script(vm, &name[..], &expr);
    stack = vm.current_frame();
    match run_result {
        Ok(()) => MaybeError::Ok(format!("Loaded {}", &name[..])),
        Err(err) => {
            let trace = stack.stacktrace(frame_level);
            let fmt = format!("{}\n{}", err, trace);
            while stack.stack.get_frames().len() > frame_level {
                match stack.exit_scope() {
                    Some(new_stack) => stack = new_stack,
                    None => return MaybeError::Err(fmt),
                }
            }
            MaybeError::Err(fmt)
        }
    }
}

pub fn load(vm: &Thread) -> Result<()> {
    try!(vm.register_type::<GluonFile>("File", &[]));

    try!(vm.define_global("io",
                          record!(
        print_int => primitive!(1 print_int),
        open_file => primitive!(1 open_file),
        read_file => primitive!(2 read_file),
        read_file_to_string => primitive!(1 read_file_to_string),
        read_char => primitive!(0 read_char),
        read_line => primitive!(0 read_line),
        print => primitive!(1 print),
        catch =>
            primitive::<fn (fn (()) -> A, fn (StdString) -> A) -> A>("io.catch", catch_io),
        run_expr => primitive!(1 run_expr),
        load_script => primitive!(2 load_script)
    )));
    Ok(())
}
