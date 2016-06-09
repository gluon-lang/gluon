use std::str;
use std::slice;

use vm::api::generic::A;
use vm::api::{Getable, Pushable, Generic};
use vm::types::VMIndex;
use vm::vm::{RootedThread, Thread, Value, VMInt};

use super::Compiler;

// TODO What should the c api return as errors
// TODO How should error messages be returned
#[repr(C)]
pub enum Error {
    Ok,
    Unknown,
}

pub extern "C" fn new_vm() -> *const Thread {
    let vm = RootedThread::new();
    vm.into_raw()
}

pub unsafe extern "C" fn free_vm(vm: &Thread) {
    RootedThread::from_raw(vm);
}

pub unsafe extern "C" fn run_expr(vm: &Thread,
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

pub unsafe extern "C" fn load_script(vm: &Thread,
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

pub extern "C" fn push_int(vm: &Thread, int: VMInt) {
    Thread::push(vm, Value::Int(int));
}

pub extern "C" fn push_float(vm: &Thread, float: f64) {
    Thread::push(vm, Value::Float(float));
}

/// Push a string to the stack. The string must be valid utf-8 or an error will be returned
pub unsafe extern "C" fn push_string(vm: &Thread, s: &u8, len: usize) -> Error {
    let s = match str::from_utf8(slice::from_raw_parts(s, len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    s.push(vm, &mut vm.get_stack());
    Error::Ok
}

/// Push a string to the stack. If the string is not utf-8 this function will trigger undefined
/// behaviour.
pub unsafe extern "C" fn push_string_unchecked(vm: &Thread, s: &u8, len: usize) {
    let s = str::from_utf8_unchecked(slice::from_raw_parts(s, len));
    s.push(vm, &mut vm.get_stack());
}

pub unsafe extern "C" fn get_int(vm: &Thread, index: VMIndex, out: &mut VMInt) -> Error {
    get_value(vm, index, out)
}

pub unsafe extern "C" fn get_float(vm: &Thread, index: VMIndex, out: &mut f64) -> Error {
    get_value(vm, index, out)
}

/// The returned string is garbage collected and may not be valid after the string is removed from
/// its slot in the stack
pub unsafe extern "C" fn get_string(vm: &Thread,
                                    index: VMIndex,
                                    out: &mut &u8,
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

unsafe fn get_value<T>(vm: &Thread, index: VMIndex, out: &mut T) -> Error
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
