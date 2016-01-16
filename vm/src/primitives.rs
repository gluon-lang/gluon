use std::cell::Cell;
use std::fs::File;
use std::io::{Read, stdin};
use std::string::String as StdString;

use base::ast;
use base::ast::{Type, ASTType};
use primitives as prim;
use types::*;
use api::{generic, Generic, Getable, Array, IO, MaybeError, primitive};
use api::generic::A;
use gc::{DataDef, WriteOnly};
use vm::{VM, BytecodeFunction, DataStruct, VMInt, Status, Value, RootStr, VMResult};
use stack::StackFrame;


pub fn array_length(array: Array<generic::A>) -> VMInt {
    array.len() as VMInt
}

pub fn array_index<'a, 'vm>(array: Array<'a, 'vm, Generic<'a, generic::A>>,
                            index: VMInt)
                            -> MaybeError<Generic<'a, generic::A>, String> {
    match array.get(index) {
        Some(value) => MaybeError::Ok(value),
        None => MaybeError::Err(format!("{} is out of range", index)),
    }
}

pub fn array_append<'a, 'vm>(lhs: Array<'a, 'vm, Generic<'a, generic::A>>,
                             rhs: Array<'a, 'vm, Generic<'a, generic::A>>)
                             -> Array<'a, 'vm, Generic<'a, generic::A>> {
    struct Append<'a: 'b, 'b> {
        lhs: &'b [Cell<Value<'a>>],
        rhs: &'b [Cell<Value<'a>>],
    }
    unsafe impl<'a, 'b> DataDef for Append<'a, 'b> {
        type Value = DataStruct<'a>;
        fn size(&self) -> usize {
            use std::mem::size_of;
            let len = self.lhs.len() + self.rhs.len();
            size_of::<usize>() + ::array::Array::<Value<'a>>::size_of(len)
        }
        fn initialize<'w>(self,
                          mut result: WriteOnly<'w, DataStruct<'a>>)
                          -> &'w mut DataStruct<'a> {
            unsafe {
                let result = &mut *result.as_mut_ptr();
                result.tag = 0;
                result.fields.initialize(self.lhs.iter().chain(self.rhs.iter()).cloned());
                result
            }
        }
    }
    Getable::from_value(lhs.vm(),
                        Value::Data(lhs.vm().new_def(Append {
                            lhs: &lhs.fields,
                            rhs: &rhs.fields,
                        })))
        .expect("Array")
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
        Greater => 1,
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

pub fn print(s: RootStr) -> IO<()> {
    println!("{}", &*s);
    IO::Value(())
}

pub fn show_int(i: VMInt) -> String {
    format!("{}", i)
}

pub fn show_float(f: f64) -> String {
    format!("{}", f)
}

pub fn show_char(c: char) -> String {
    format!("{}", c)
}

pub fn error(_: &VM) -> Status {
    // We expect a string as an argument to this function but we only return Status::Error
    // and let the caller take care of printing the message
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
            let result = Value::String(vm.alloc(&stack.stack, &fmt[..]));
            stack.push(result);
            stack.push(Value::Int(0));
            match vm.execute(stack, &[Call(2)], &BytecodeFunction::empty()) {
                Ok(_) => Status::Ok,
                Err(err) => {
                    stack = StackFrame::new(vm.stack.borrow_mut(), 3, None);
                    let fmt = format!("{}", err);
                    let result = Value::String(vm.alloc(&stack.stack, &fmt[..]));
                    stack.push(result);
                    Status::Error
                }
            }
        }
    }
}

#[cfg(all(feature = "check", feature = "parser"))]
pub fn run_expr(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 2, None);
    let frame_level = stack.stack.frames.len();
    let s = stack[0];
    match s {
        Value::String(s) => {
            drop(stack);
            let run_result = ::vm::run_expr(vm, "<top>", &s);
            stack = StackFrame::new(vm.stack.borrow_mut(), 2, None);
            match run_result {
                Ok(value) => {
                    let fmt = format!("{:?}", value);
                    let result = vm.alloc(&stack.stack, &fmt[..]);
                    stack.push(Value::String(result));
                }
                Err(err) => {
                    let trace = backtrace(vm, frame_level, &stack);
                    while stack.stack.frames.len() > frame_level {
                        stack = stack.exit_scope();
                    }
                    let fmt = format!("{}\n{}", err, trace);
                    let result = vm.alloc(&stack.stack, &fmt[..]);
                    stack.push(Value::String(result));
                }
            }
            Status::Ok
        }
        x => panic!("Expected string got {:?}", x),
    }
}

#[cfg(all(feature = "check", feature = "parser"))]
pub fn load_script(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 3, None);
    let frame_level = stack.stack.frames.len();
    match (stack[0], stack[1]) {
        (Value::String(name), Value::String(expr)) => {
            drop(stack);
            let run_result = ::vm::load_script(vm, &name[..], &expr);
            stack = StackFrame::new(vm.stack.borrow_mut(), 3, None);
            match run_result {
                Ok(()) => {
                    let fmt = format!("Loaded {}", name);
                    let result = vm.alloc(&stack.stack, &fmt[..]);
                    stack.push(Value::String(result));
                }
                Err(err) => {
                    let trace = backtrace(vm, frame_level, &stack);
                    let fmt = format!("{}\n{}", err, trace);
                    while stack.stack.frames.len() > frame_level {
                        stack = stack.exit_scope();
                    }
                    let result = vm.alloc(&stack.stack, &fmt[..]);
                    stack.push(Value::String(result));
                }
            }
            Status::Ok
        }
        x => panic!("Expected 2 strings got {:?}", x),
    }
}

/// Creates a backtraces starting from `frame_level`
#[cfg(all(feature = "check", feature = "parser"))]
fn backtrace(vm: &VM, frame_level: usize, stack: &StackFrame) -> String {
    let mut buffer = String::from("Backtrace:\n");
    for frame in &stack.stack.frames[frame_level..] {
        match frame.function_name {
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
fn f3<A, B, C, R>(f: fn(A, B, C) -> R) -> fn(A, B, C) -> R {
    f
}
pub fn load(vm: &VM) -> VMResult<()> {

    let a = Type::generic(ast::Generic {
        kind: ast::Kind::star(),
        id: vm.symbol("a"),
    });
    let b = Type::generic(ast::Generic {
        kind: ast::Kind::star(),
        id: vm.symbol("b"),
    });
    let io = |t| {
        ASTType::from(ast::Type::Data(ast::TypeConstructor::Data(vm.symbol("IO")), vec![t]))
    };

    try!(vm.define_global("array",
                          record!(
        length => f1(prim::array_length),
        index => f2(prim::array_index),
        append => f2(prim::array_append)
    )));

    try!(vm.define_global("string_prim",
                          record!(
        length => f1(prim::string_length),
        find => f2(prim::string_find),
        rfind => f2(prim::string_rfind),
        trim => f1(prim::string_trim),
        compare => f2(prim::string_compare),
        append => f2(prim::string_append),
        eq => f2(prim::string_eq),
        slice => f3(prim::string_slice)
    )));
    try!(vm.define_global("prim",
                          record!(
        show_Int => f1(prim::show_int),
        show_Float => f1(prim::show_float),
        show_Char => f1(prim::show_char)
    )));

    try!(vm.define_global("#error",
                          primitive::<fn(StdString) -> A>("#error", prim::error)));
    try!(vm.define_global("error",
                          primitive::<fn(StdString) -> A>("error", prim::error)));
    try!(vm.define_global("trace", primitive::<fn(A)>("trace", prim::trace)));
    let lazy = |t| {
        ASTType::from(ast::Type::data(ast::TypeConstructor::Data(vm.symbol("Lazy")), vec![t]))
    };
    try!(vm.extern_function("lazy",
                            vec![Type::function(vec![Type::unit()], a.clone())],
                            lazy(a.clone()),
                            Box::new(::lazy::lazy)));
    try!(vm.extern_function("force",
                            vec![lazy(a.clone())],
                            a.clone(),
                            Box::new(::lazy::force)));

    try!(load_io(vm));

    // io_bind m f (): IO a -> (a -> IO b) -> IO b
    //     = f (m ())
    let io_bind = vec![Pop(1), Push(0), PushInt(0), Call(1), PushInt(0), TailCall(2)];
    let f = Type::function(vec![a.clone()], io(b.clone()));
    let io_bind_type = Type::function(vec![io(a.clone()), f], io(b.clone()));
    vm.add_bytecode("io_bind", io_bind_type, 3, io_bind);


    vm.add_bytecode("io_return",
                    Type::function(vec![a.clone()], io(a.clone())),
                    2,
                    vec![Pop(1)]);
    Ok(())
}

#[cfg(all(feature = "check", feature = "parser"))]
fn load_io(vm: &VM) -> VMResult<()> {
    // IO functions
    try!(vm.define_global("io",
                          record!(
        print_int => f1(prim::print_int),
        read_file => f1(prim::read_file),
        read_line => f0(prim::read_line),
        print => f1(prim::print),
        catch =>
            primitive::<fn (IO<A>, fn (StdString) -> IO<A>) -> IO<A>>("io.catch", prim::catch_io),
        run_expr =>
            primitive::<fn (StdString) -> IO<StdString>>("io.run_expr", prim::run_expr),
        load_script =>
            primitive::<fn (StdString, StdString) -> IO<StdString>>("io.load_script",
                                                                    prim::load_script)
    )));
    Ok(())
}

#[cfg(not(all(feature = "check", feature = "parser")))]
fn load_io(vm: &VM) -> VMResult<()> {
    // IO functions
    try!(vm.define_global("io",
                          record!(
        print_int => f1(prim::print_int),
        read_file => f1(prim::read_file),
        read_line => f0(prim::read_line),
        print => f1(prim::print),
        catch =>
            primitive::<fn (IO<A>, fn (StdString) -> IO<A>) -> IO<A>>("io.catch", prim::catch_io)
    )));
    Ok(())
}
