use std::string::String as StdString;
use std::result::Result as StdResult;
use std::io::{Read, stdin};
use std::fs::File;

use vm::Result;
use vm::types::*;
use vm::thread::ThreadInternal;
use vm::thread::{Thread, Status, RootStr};
use vm::api::{Generic, VMType, Pushable, IO, WithVM, primitive};
use vm::api::generic::{A, B};

use super::Compiler;

pub fn print_int(i: VMInt) -> IO<()> {
    print!("{}", i);
    IO::Value(())
}

pub fn print(s: RootStr) -> IO<()> {
    println!("{}", &*s);
    IO::Value(())
}

pub fn read_file(s: RootStr) -> IO<String> {
    let mut buffer = String::new();
    match File::open(&s[..]).and_then(|mut file| file.read_to_string(&mut buffer)) {
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
pub fn catch_io(vm: &Thread) -> Status {
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
            match vm.call_function(stack, 2) {
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

pub fn run_expr(expr: WithVM<RootStr>) -> IO<String> {
    let WithVM { vm, value: expr } = expr;
    let mut stack = vm.current_frame();
    let frame_level = stack.stack.get_frames().len();
    drop(stack);
    let run_result: StdResult<Generic<A>, _> = Compiler::new().run_expr(vm, "<top>", &expr);
    stack = vm.current_frame();
    match run_result {
        Ok(value) => IO::Value(format!("{:?}", value.0)),
        Err(err) => {
            let trace = stack.stacktrace(frame_level);
            let fmt = format!("{}\n{}", err, trace);
            while stack.stack.get_frames().len() > frame_level {
                match stack.exit_scope() {
                    Some(new_stack) => stack = new_stack,
                    None => return IO::Exception(fmt),
                }
            }
            IO::Exception(fmt)
        }
    }
}

pub fn load_script(name: WithVM<RootStr>, expr: RootStr) -> IO<String> {
    let WithVM { vm, value: name } = name;
    let mut stack = vm.current_frame();
    let frame_level = stack.stack.get_frames().len();
    drop(stack);
    let run_result = Compiler::new().load_script(vm, &name[..], &expr);
    stack = vm.current_frame();
    match run_result {
        Ok(()) => IO::Value(format!("Loaded {}", &name[..])),
        Err(err) => {
            let trace = stack.stacktrace(frame_level);
            let fmt = format!("{}\n{}", err, trace);
            while stack.stack.get_frames().len() > frame_level {
                match stack.exit_scope() {
                    Some(new_stack) => stack = new_stack,
                    None => return IO::Exception(fmt),
                }
            }
            IO::Exception(fmt)
        }
    }
}

pub fn load(vm: &Thread) -> Result<()> {

    // io_bind m f (): IO a -> (a -> IO b) -> IO b
    //     = f (m ())
    let io_bind = vec![Pop(1), Push(0), PushInt(0), Call(1), PushInt(0), TailCall(2)];
    let io_bind_type = <fn (IO<A>, fn (A) -> IO<B>) -> IO<B> as VMType>::make_type(vm);
    vm.add_bytecode("io_bind", io_bind_type, 3, io_bind);


    vm.add_bytecode("io_return",
                    <fn(A) -> IO<A> as VMType>::make_type(vm),
                    2,
                    vec![Pop(1)]);
    // IO functions
    try!(vm.define_global("io",
                          record!(
        print_int => primitive!(1 print_int),
        read_file => primitive!(1 read_file),
        read_char => primitive!(0 read_char),
        read_line => primitive!(0 read_line),
        print => primitive!(1 print),
        catch =>
            primitive::<fn (IO<A>, fn (StdString) -> IO<A>) -> IO<A>>("io.catch", catch_io),
        run_expr => primitive!(1 run_expr),
        load_script => primitive!(2 load_script)
    )));
    Ok(())
}
