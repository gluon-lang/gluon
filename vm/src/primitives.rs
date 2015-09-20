use std::fs::File;
use std::io::{Read, stdin};

use api::{generic, Array, IO};
use vm::{VM, BytecodeFunction, VMInt, Status, Value, RootStr};
use types::Instruction::Call;
use stack::StackFrame;

pub fn array_length(array: Array<generic::A>) -> VMInt {
    array.len() as VMInt
}
pub fn string_length(s: RootStr) -> VMInt {
    s.len() as VMInt
}
pub fn string_append(l: RootStr, r: RootStr) -> String {
    let mut s = String::with_capacity(l.len() + r.len());
    s.push_str(&l);
    s.push_str(&r);
    s
}
pub fn string_eq(l: RootStr, r: RootStr) -> bool {
    *l == *r
}

pub fn string_compare(l: RootStr, r: RootStr) -> VMInt {
    use std::cmp::Ordering::*;
    match l.cmp(&r) {
        Less => -1,
        Equal => 0,
        Greater => 1
    }
}
pub fn string_slice(s: RootStr, start: VMInt, end: VMInt) -> String {
    String::from(&s[start as usize..end as usize])
}
pub fn string_find(haystack: RootStr, needle: RootStr) -> Option<VMInt> {
    haystack.find(&needle[..]).map(|i| i as VMInt)
}
pub fn string_rfind(haystack: RootStr, needle: RootStr) -> Option<VMInt> {
    haystack.rfind(&needle[..]).map(|i| i as VMInt)
}
pub fn string_trim(s: RootStr) -> String {
    String::from(s.trim())
}
pub fn print_int(i: VMInt) -> IO<()> {
    print!("{}", i);
    IO::Value(())
}
pub fn trace(vm: &VM) -> Status {
    let stack = StackFrame::new(vm.stack.borrow_mut(), 1, None);
    println!("{:?}", stack[0]);
    Status::Ok
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

pub fn read_line() -> IO<String>  {
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

pub fn print(s: RootStr) -> IO<()>  {
    println!("{}", &*s);
    IO::Value(())
}

pub fn show_int(i: VMInt) -> String {
    format!("{}", i)
}

pub fn show_float(f: f64) -> String {
    format!("{}", f)
}

pub fn error(_: &VM) -> Status {
    //We expect a string as an argument to this function but we only return Status::Error
    //and let the caller take care of printing the message
    Status::Error
}

/// IO a -> (String -> IO a) -> IO a
pub fn catch_io(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 3, None);
    let frame_level = stack.stack.frames.len();
    let action = stack[0];
    stack.push(action);
    stack.push(Value::Int(0));
    match vm.execute(stack, &[Call(1)], &BytecodeFunction::empty()) {
        Ok(_) => Status::Ok,
        Err(err) => {
            stack = StackFrame::new(vm.stack.borrow_mut(), 3, None);
            while stack.stack.frames.len() > frame_level {
                stack = stack.exit_scope();
            }
            let callback = stack[1];
            stack.push(callback);
            let fmt = format!("{}", err);
            let result = Value::String(vm.alloc(&mut stack.stack.values, &fmt[..]));
            stack.push(result);
            stack.push(Value::Int(0));
            match vm.execute(stack, &[Call(2)], &BytecodeFunction::empty()) {
                Ok(_) => Status::Ok,
                Err(err) => {
                    stack = StackFrame::new(vm.stack.borrow_mut(), 3, None);
                    let fmt = format!("{}", err);
                    let result = Value::String(vm.alloc(&mut stack.stack.values, &fmt[..]));
                    stack.push(result);
                    Status::Error
                }
            }
        }
    }
}

pub fn run_expr(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 2, None);
    let s = stack[0];
    match s {
        Value::String(s) => {
            drop(stack);
            let run_result = ::vm::run_expr(vm, &s);
            stack = StackFrame::new(vm.stack.borrow_mut(), 2, None);
            match run_result {
                Ok(value) => {
                    let fmt = format!("{:?}", value);
                    let result = vm.alloc(&mut stack.stack.values, &fmt[..]);
                    stack.push(Value::String(result));
                }
                Err(err) => {
                    let fmt = format!("{}", err);
                    let result = vm.alloc(&mut stack.stack.values, &fmt[..]);
                    stack.push(Value::String(result));
                }
            }
            Status::Ok
        }
        x => panic!("Expected string got {:?}", x)
    }
}

pub fn load_script(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 3, None);
    match (stack[0], stack[1]) {
        (Value::String(name), Value::String(expr)) => {
            drop(stack);
            let run_result = ::vm::load_script(vm, &name, &expr);
            stack = StackFrame::new(vm.stack.borrow_mut(), 3, None);
            match run_result {
                Ok(()) => {
                    let fmt = format!("Loaded {}", name);
                    let result = vm.alloc(&mut stack.stack.values, &fmt[..]);
                    stack.push(Value::String(result));
                }
                Err(err) => {
                    let fmt = format!("{}", err);
                    let result = vm.alloc(&mut stack.stack.values, &fmt[..]);
                    stack.push(Value::String(result));
                }
            }
            Status::Ok
        }
        x => panic!("Expected 2 strings got {:?}", x)
    }
}
