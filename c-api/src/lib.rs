//! A (WIP) C API allowing use of gluon in other langauges than Rust.
#![doc(html_root_url = "https://docs.rs/gluon_c-api/0.17.2")] // # GLUON

use std::{slice, str};

use futures::{executor::block_on, future};

use gluon::{
    vm::{
        api::{CPrimitive, Getable, Hole, OpaqueValue, Pushable},
        stack,
        thread::{RootedThread, Status, Thread, ThreadInternal},
        types::{VmIndex, VmInt},
    },
    ThreadExt,
};

pub type Function = extern "C" fn(&Thread) -> Status;

// TODO What should the c api return as errors
// TODO How should error messages be returned
#[repr(C)]
#[derive(Debug, PartialEq)]
pub enum Error {
    Ok,
    Unknown,
}

#[no_mangle]
pub extern "C" fn glu_new_vm() -> *const Thread {
    let vm = RootedThread::new();
    vm.into_raw()
}

#[no_mangle]
pub unsafe extern "C" fn glu_free_vm(vm: &Thread) {
    RootedThread::from_raw(vm);
}

#[no_mangle]
pub unsafe extern "C" fn glu_run_expr(
    vm: &Thread,
    module: &u8,
    module_len: usize,
    expr: &u8,
    expr_len: usize,
) -> Error {
    let module = match str::from_utf8(slice::from_raw_parts(module, module_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let expr = match str::from_utf8(slice::from_raw_parts(expr, expr_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let result = vm.run_expr::<OpaqueValue<&Thread, Hole>>(module, expr);
    match result {
        Ok(_) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

#[no_mangle]
pub unsafe extern "C" fn glu_load_script(
    vm: &Thread,
    module: &u8,
    module_len: usize,
    expr: &u8,
    expr_len: usize,
) -> Error {
    let module = match str::from_utf8(slice::from_raw_parts(module, module_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let expr = match str::from_utf8(slice::from_raw_parts(expr, expr_len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    let result = vm.load_script(module, expr);
    match result {
        Ok(_) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

#[no_mangle]
pub extern "C" fn glu_call_function(thread: &Thread, args: VmIndex) -> Error {
    match block_on(future::poll_fn(|cx| {
        let context = thread.context();
        thread.call_function(cx, context, args)
    })) {
        Ok(_) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

#[no_mangle]
pub extern "C" fn glu_len(vm: &Thread) -> usize {
    let mut context = vm.context();
    let stack = context.stack_frame::<stack::State>();
    stack.len() as usize
}

#[no_mangle]
pub extern "C" fn glu_pop(vm: &Thread, n: usize) {
    let mut context = vm.context();
    let mut stack = context.stack_frame::<stack::State>();
    for _ in 0..n {
        stack.pop();
    }
}

#[no_mangle]
pub extern "C" fn glu_push_int(vm: &Thread, int: VmInt) {
    Thread::push(vm, int).unwrap();
}

#[no_mangle]
pub extern "C" fn glu_push_byte(vm: &Thread, b: u8) {
    Thread::push(vm, b).unwrap();
}

#[no_mangle]
pub extern "C" fn glu_push_float(vm: &Thread, float: f64) {
    Thread::push(vm, float).unwrap();
}

#[no_mangle]
pub extern "C" fn glu_push_bool(vm: &Thread, b: i8) {
    Thread::push(vm, b != 0).unwrap();
}

#[no_mangle]
pub unsafe extern "C" fn glu_push_function(
    vm: &Thread,
    name: &u8,
    len: usize,
    function: Function,
    args: VmIndex,
) -> Error {
    let s = match str::from_utf8(slice::from_raw_parts(name, len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    match Thread::push(vm, CPrimitive::new(function, args, s)) {
        Ok(()) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

/// Push a string to the stack. The string must be valid utf-8 or an error will be returned
#[no_mangle]
pub unsafe extern "C" fn glu_push_string(vm: &Thread, s: &u8, len: usize) -> Error {
    let s = match str::from_utf8(slice::from_raw_parts(s, len)) {
        Ok(s) => s,
        Err(_) => return Error::Unknown,
    };
    match s.vm_push(&mut vm.current_context()) {
        Ok(()) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

/// Push a string to the stack. If the string is not utf-8 this function will trigger undefined
/// behaviour.
#[no_mangle]
pub unsafe extern "C" fn glu_push_string_unchecked(vm: &Thread, s: &u8, len: usize) -> Error {
    let s = str::from_utf8_unchecked(slice::from_raw_parts(s, len));
    match s.vm_push(&mut vm.current_context()) {
        Ok(()) => Error::Ok,
        Err(_) => Error::Unknown,
    }
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub extern "C" fn glu_push_light_userdata(vm: &Thread, data: *mut libc::c_void) {
    Thread::push(vm, data as usize).unwrap()
}

#[no_mangle]
pub extern "C" fn glu_get_byte(vm: &Thread, index: VmIndex, out: &mut u8) -> Error {
    get_value(vm, index, out)
}

#[no_mangle]
pub extern "C" fn glu_get_int(vm: &Thread, index: VmIndex, out: &mut VmInt) -> Error {
    get_value(vm, index, out)
}

#[no_mangle]
pub extern "C" fn glu_get_float(vm: &Thread, index: VmIndex, out: &mut f64) -> Error {
    get_value(vm, index, out)
}

#[no_mangle]
pub extern "C" fn glu_get_bool(vm: &Thread, index: VmIndex, out: &mut i8) -> Error {
    let mut b = false;
    let err = get_value(vm, index, &mut b);
    if err == Error::Ok {
        *out = b as i8;
    }
    err
}

/// The returned string is garbage collected and may not be valid after the string is removed from
/// its slot in the stack
#[no_mangle]
pub unsafe extern "C" fn glu_get_string(
    vm: &Thread,
    index: VmIndex,
    out: &mut *const u8,
    out_len: &mut usize,
) -> Error {
    let mut context = vm.context();
    let stack = context.stack_frame::<stack::State>();
    match stack
        .get_variant(index)
        .map(|value| <&str>::from_value(vm, value))
    {
        Some(value) => {
            *out = &*value.as_ptr();
            *out_len = value.len();
            Error::Ok
        }
        None => Error::Unknown,
    }
}

#[cfg(not(target_arch = "wasm32"))]
#[no_mangle]
pub extern "C" fn glu_get_light_userdata(
    vm: &Thread,
    index: VmIndex,
    out: &mut *mut libc::c_void,
) -> Error {
    let mut userdata = 0usize;
    let err = get_value(vm, index, &mut userdata);
    if err == Error::Ok {
        *out = userdata as *mut libc::c_void;
    }
    err
}

fn get_value<T>(vm: &Thread, index: VmIndex, out: &mut T) -> Error
where
    T: for<'vm, 'value> Getable<'vm, 'value>,
{
    let mut context = vm.context();
    let stack = context.stack_frame::<stack::State>();
    match stack
        .get_variant(index)
        .map(|value| T::from_value(vm, value))
    {
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

    use std::{ptr, slice, str};

    #[test]
    fn push_pop() {
        unsafe {
            let vm = &*glu_new_vm();

            glu_push_int(vm, 123);
            glu_push_float(vm, 3.14);
            let s = "test";
            glu_push_string(vm, &s.as_bytes()[0], s.len());
            glu_push_bool(vm, 1);
            glu_push_byte(vm, 128);

            let mut int = 0;
            assert_eq!(glu_get_int(vm, 0, &mut int), Error::Ok);
            assert_eq!(int, 123);

            let mut float = 0.0;
            assert_eq!(glu_get_float(vm, 1, &mut float), Error::Ok);
            assert_eq!(float, 3.14);

            let mut string_ptr = ptr::null();
            let mut string_len = 0;
            assert_eq!(
                glu_get_string(vm, 2, &mut string_ptr, &mut string_len),
                Error::Ok
            );
            assert_eq!(
                str::from_utf8(slice::from_raw_parts(string_ptr, string_len)),
                Ok("test")
            );

            let mut b = 0;
            assert_eq!(glu_get_bool(vm, 3, &mut b), Error::Ok);
            assert_eq!(b, 1);

            let mut b = 0;
            assert_eq!(glu_get_byte(vm, 4, &mut b), Error::Ok);
            assert_eq!(b, 128);

            assert_eq!(glu_len(vm), 5);

            glu_pop(vm, 4);

            glu_free_vm(vm);
        }
    }

    #[cfg(not(target_arch = "wasm32"))]
    #[test]
    fn push_userdata() {
        unsafe {
            let vm = &*glu_new_vm();

            let x = 123i32;
            glu_push_light_userdata(vm, &x as *const i32 as *mut ::libc::c_void);
            let mut p = ptr::null_mut();
            assert_eq!(glu_get_light_userdata(vm, 0, &mut p), Error::Ok);
            assert_eq!(*(p as *const i32), 123);
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
