use std::mem;
use std::str;
use std::slice;

use vm::api::{Getable, Pushable};
use vm::types::VMIndex;
use vm::vm::{VM, Thread, Value, VMInt};

use super::Compiler;

// TODO What should the c api return as errors
// TODO How should error messages be returned
#[repr(C)]
pub enum Error {
    Ok,
    Unknown,
}

pub extern "C" fn new_vm() -> *const Thread {
    let vm = VM::new();
    vm.into_raw()
}

pub unsafe extern "C" fn free_vm(vm: &Thread) {
    VM::from_raw(vm);
}

pub unsafe extern "C" fn run_expr(vm: &Thread, module: &u8, module_len: usize, expr: &u8, expr_len: usize) -> Error {
    let module = match str::from_utf8(slice::from_raw_parts(module, module_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let expr = match str::from_utf8(slice::from_raw_parts(expr, expr_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let vm = VM::from_raw(vm);
    let err = {
        let result = Compiler::new()
            .run_expr(&vm, module, expr);
        match result {
            Ok(_) => Error::Ok,
            Err(_) => Error::Unknown,
        }
    };
    mem::forget(vm);
    err
}

pub unsafe extern "C" fn load_script(vm: &Thread, module: &u8, module_len: usize, expr: &u8, expr_len: usize) -> Error {
    let module = match str::from_utf8(slice::from_raw_parts(module, module_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let expr = match str::from_utf8(slice::from_raw_parts(expr, expr_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let vm = VM::from_raw(vm);
    let err = {
        let result = Compiler::new()
            .load_script(&vm, module, expr);
        match result {
            Ok(_) => Error::Ok,
            Err(_) => Error::Unknown,
        }
    };
    mem::forget(vm);
    err
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
    let vm = VM::from_raw(vm);
    s.push(&vm, &mut vm.current_frame());
    mem::forget(vm);
    Error::Ok
}

/// Push a string to the stack. If the string is not utf-8 this function will trigger undefined
/// behaviour.
pub unsafe extern "C" fn push_string_unchecked(vm: &Thread, s: &u8, len: usize) {
    let s = str::from_utf8_unchecked(slice::from_raw_parts(s, len));
    let vm = VM::from_raw(vm);
    s.push(&vm, &mut vm.current_frame());
    mem::forget(vm);
}

pub unsafe extern "C" fn get_int(vm: &Thread, index: VMIndex, out: &mut VMInt) -> Error {
    get_value(vm, index, out)
}

pub unsafe extern "C" fn get_float(vm: &Thread, index: VMIndex, out: &mut f64) -> Error {
    get_value(vm, index, out)
}

/// The returned string is garbage collected and may not be valid after the string is removed from
/// its slot in the stack
pub unsafe extern "C" fn get_string(vm: &Thread, index: VMIndex, out: &mut &u8, out_len: &mut usize) -> Error {
    let vm = VM::from_raw(vm);
    let result = {
        let opt = <&str>::from_value(&vm, vm.current_frame()[index]);
        match opt {
            Some(value) => {
                *out = &*value.as_ptr();
                *out_len = value.len();
                Error::Ok
            }
            None => Error::Unknown,
        }
    };
    mem::forget(vm);
    result
}

unsafe fn get_value<T>(vm: &Thread, index: VMIndex, out: &mut T) -> Error
    where T: for<'vm> Getable<'vm>
{
    let vm = VM::from_raw(vm);
    let opt = T::from_value(&vm, vm.current_frame()[index]);
    mem::forget(vm);
    match opt {
        Some(value) => {
            *out = value;
            Error::Ok
        }
        None => Error::Unknown,
    }
}
