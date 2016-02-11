use std::string::String as StdString;
use std::io::{Read, stdin};
use std::fs::File;

use vm::types::*;
use vm::stack::StackFrame;
use vm::vm::{VM, Result, Status, Value, VMInt, RootStr};
use vm::api::{VMType, IO, WithVM, primitive};
use vm::api::generic::{A, B};

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

pub fn read_line() -> IO<String> {
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
pub fn catch_io(vm: &VM) -> Status {
    let mut stack = vm.current_frame();
    let frame_level = stack.stack.frames.len();
    let action = stack[0];
    stack.push(action);
    stack.push(Value::Int(0));
    match vm.call_function(stack, 1) {
        Ok(_) => Status::Ok,
        Err(err) => {
            stack = vm.current_frame();
            while stack.stack.frames.len() > frame_level {
                match stack.exit_scope() {
                    Some(new_stack) => stack = new_stack,
                    None => return Status::Error,
                }
            }
            let callback = stack[1];
            stack.push(callback);
            let fmt = format!("{}", err);
            let result = Value::String(vm.alloc(&stack.stack, &fmt[..]));
            stack.push(result);
            stack.push(Value::Int(0));
            match vm.call_function(stack, 2) {
                Ok(_) => Status::Ok,
                Err(err) => {
                    stack = vm.current_frame();
                    let fmt = format!("{}", err);
                    let result = Value::String(vm.alloc(&stack.stack, &fmt[..]));
                    stack.push(result);
                    Status::Error
                }
            }
        }
    }
}

pub fn run_expr(expr: WithVM<RootStr>) -> IO<String> {
    let WithVM { vm, value: expr } = expr;
    let mut stack = vm.current_frame();
    let frame_level = stack.stack.frames.len();
    drop(stack);
    let run_result = super::run_expr(vm, "<top>", &expr);
    stack = vm.current_frame();
    match run_result {
        Ok(value) => IO::Value(format!("{:?}", value)),
        Err(err) => {
            let trace = backtrace(vm, frame_level, &stack);
            let fmt = format!("{}\n{}", err, trace);
            while stack.stack.frames.len() > frame_level {
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
    let frame_level = stack.stack.frames.len();
    drop(stack);
    let run_result = super::load_script(vm, &name[..], &expr);
    stack = vm.current_frame();
    match run_result {
        Ok(()) => IO::Value(format!("Loaded {}", &name[..])),
        Err(err) => {
            let trace = backtrace(vm, frame_level, &stack);
            let fmt = format!("{}\n{}", err, trace);
            while stack.stack.frames.len() > frame_level {
                match stack.exit_scope() {
                    Some(new_stack) => stack = new_stack,
                    None => return IO::Exception(fmt),
                }
            }
            IO::Exception(fmt)
        }
    }
}

/// Creates a backtraces starting from `frame_level`
fn backtrace(vm: &VM, frame_level: usize, stack: &StackFrame) -> String {
    let mut buffer = String::from("Backtrace:\n");
    for frame in &stack.stack.frames[frame_level..] {
        match frame.function.map(|c| c.name()) {
            Some(name) => buffer.push_str(&vm.symbol_string(name)),
            None => buffer.push_str("<unknown>"),
        }
        buffer.push('\n');
    }
    if !stack.stack.frames.is_empty() {
        // Remove last newline
        buffer.pop();
    }
    buffer
}

fn f0<R>(f: fn() -> R) -> fn() -> R {
    f
}
fn f1<A, R>(f: fn(A) -> R) -> fn(A) -> R {
    f
}
fn f2<A, B, R>(f: fn(A, B) -> R) -> fn(A, B) -> R {
    f
}

pub fn load(vm: &VM) -> Result<()> {

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
        print_int => f1(print_int),
        read_file => f1(read_file),
        read_line => f0(read_line),
        print => f1(print),
        catch =>
            primitive::<fn (IO<A>, fn (StdString) -> IO<A>) -> IO<A>>("io.catch", catch_io),
        run_expr => f1(run_expr),
        load_script => f2(load_script)
    )));
    Ok(())
}
