//! A (WIP) C API allowing use of gluon in other langauges than Rust.

extern crate gluon;

use std::str;
use std::slice;

use gluon::vm::api::generic::A;
use gluon::vm::api::{Getable, Pushable, Generic, CPrimitive};
use gluon::vm::types::{VMIndex, VMInt};
use gluon::vm::thread::{RootedThread, Thread, ThreadInternal, Status};

use gluon::Compiler;

pub type Function = extern "C" fn(&Thread) -> Status;

// TODO What should the c api return as errors
// TODO How should error messages be returned
#[repr(C)]
#[derive(Debug, PartialEq)]
pub enum Error {
    Ok,
    Unknown,
}

pub extern "C" fn glu_new_vm() -> *const Thread {
    let vm = RootedThread::new();
    vm.into_raw()
}

pub unsafe extern "C" fn glu_free_vm(vm: &Thread) {
    RootedThread::from_raw(vm);
}

pub unsafe extern "C" fn glu_run_expr(vm: &Thread,
                                      module: &u8,
                                      module_len: usize,
                                      expr: &u8,
                                      expr_len: usize)
                                      -> Error {
    let module = match str::from_utf8(slice::from_raw_parts(module, module_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let expr = match str::from_utf8(slice::from_raw_parts(expr, expr_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let result: Result<Generic<A>, _> = Compiler::new().run_expr(&vm, module, expr);
    match result {
        Ok(_) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

pub unsafe extern "C" fn glu_load_script(vm: &Thread,
                                         module: &u8,
                                         module_len: usize,
                                         expr: &u8,
                                         expr_len: usize)
                                         -> Error {
    let module = match str::from_utf8(slice::from_raw_parts(module, module_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let expr = match str::from_utf8(slice::from_raw_parts(expr, expr_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let result = Compiler::new().load_script(vm, module, expr);
    match result {
        Ok(_) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

pub extern "C" fn glu_call_function(thread: &Thread, arguments: VMIndex) -> Error {
    let stack = thread.current_frame();
    match thread.call_function(stack, arguments) {
        Ok(_) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

pub extern "C" fn glu_len(vm: &Thread) -> usize {
    vm.current_frame().len() as usize
}

pub extern "C" fn glu_pop(vm: &Thread, n: usize) {
    let mut stack = vm.current_frame();
    for _ in 0..n {
        stack.pop();
    }
}

pub extern "C" fn glu_push_int(vm: &Thread, int: VMInt) {
    Thread::push(vm, int);
}

pub extern "C" fn glu_push_float(vm: &Thread, float: f64) {
    Thread::push(vm, float);
}

pub unsafe extern "C" fn glu_push_function(vm: &Thread,
                                           name: &u8,
                                           len: usize,
                                           function: Function,
                                           arguments: VMIndex)
                                           -> Error {
    let s = match str::from_utf8(slice::from_raw_parts(name, len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    Thread::push(vm, CPrimitive::new(function, arguments, s));
    Error::Ok
}

/// Push a string to the stack. The string must be valid utf-8 or an error will be returned
pub unsafe extern "C" fn glu_push_string(vm: &Thread, s: &u8, len: usize) -> Error {
    let s = match str::from_utf8(slice::from_raw_parts(s, len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    s.push(vm, &mut vm.get_stack());
    Error::Ok
}

/// Push a string to the stack. If the string is not utf-8 this function will trigger undefined
/// behaviour.
pub unsafe extern "C" fn glu_push_string_unchecked(vm: &Thread, s: &u8, len: usize) {
    let s = str::from_utf8_unchecked(slice::from_raw_parts(s, len));
    s.push(vm, &mut vm.get_stack());
}

pub extern "C" fn glu_get_int(vm: &Thread, index: VMIndex, out: &mut VMInt) -> Error {
    get_value(vm, index, out)
}

pub extern "C" fn glu_get_float(vm: &Thread, index: VMIndex, out: &mut f64) -> Error {
    get_value(vm, index, out)
}

/// The returned string is garbage collected and may not be valid after the string is removed from
/// its slot in the stack
pub unsafe extern "C" fn glu_get_string(vm: &Thread,
                                        index: VMIndex,
                                        out: &mut *const u8,
                                        out_len: &mut usize)
                                        -> Error {
    let stack = vm.current_frame();
    match stack.get_variants(index).and_then(|value| <&str>::from_value(vm, value)) {
        Some(value) => {
            *out = &*value.as_ptr();
            *out_len = value.len();
            Error::Ok
        }
        None => Error::Unknown,
    }
}

fn get_value<T>(vm: &Thread, index: VMIndex, out: &mut T) -> Error
    where T: for<'vm> Getable<'vm>
{
    let stack = vm.current_frame();
    match stack.get_variants(index).and_then(|value| T::from_value(vm, value)) {
        Some(value) => {
            *out = value;
            Error::Ok
        }
        None => Error::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use gluon::vm::thread::{Status, Thread};

    use std::ptr;
    use std::str;
    use std::slice;

    #[test]
    fn push_pop() {
        unsafe {
            let vm = &*glu_new_vm();

            glu_push_int(vm, 123);
            glu_push_float(vm, 3.14);
            let s = "test";
            glu_push_string(vm, &s.as_bytes()[0], s.len());

            let mut int = 0;
            assert_eq!(glu_get_int(vm, 0, &mut int), Error::Ok);
            assert_eq!(int, 123);

            let mut float = 0.0;
            assert_eq!(glu_get_float(vm, 1, &mut float), Error::Ok);
            assert_eq!(float, 3.14);

            let mut string_ptr = ptr::null();
            let mut string_len = 0;
            assert_eq!(glu_get_string(vm, 2, &mut string_ptr, &mut string_len),
                       Error::Ok);
            assert_eq!(str::from_utf8(slice::from_raw_parts(string_ptr, string_len)),
                       Ok("test"));

            assert_eq!(glu_len(vm), 3);

            glu_pop(vm, 3);

            glu_free_vm(vm);
        }
    }

    #[test]
    fn call_function() {
        extern "C" fn mult(vm: &Thread) -> Status {
            let mut l = 0.0;
            assert_eq!(glu_get_float(vm, 0, &mut l), Error::Ok);
            let mut r = 0.0;
            assert_eq!(glu_get_float(vm, 1, &mut r), Error::Ok);
            glu_push_float(vm, l * r);
            Status::Ok
        }

        unsafe {
            let vm = &*glu_new_vm();
            let name = "mult";
            glu_push_function(vm, &name.as_bytes()[0], name.len(), mult, 2);
            glu_push_float(vm, 12.0);
            glu_push_float(vm, 3.0);

            assert_eq!(glu_call_function(vm, 2), Error::Ok);
            let mut result = 0.0;
            assert_eq!(glu_get_float(vm, 0, &mut result), Error::Ok);
            assert_eq!(result, 36.0);

            glu_free_vm(vm);
        }
    }
}
