use vm::{VM, BytecodeFunction, Value, Userdata_, StackFrame, VMInt};
use typecheck::{TcType, Typed, Type, UNIT_TYPE, BOOL_TYPE, INT_TYPE, FLOAT_TYPE};
use compiler::Instruction::Call;
use std::any::Any;
use std::marker::PhantomData;

pub trait VMType {
    fn vm_type<'a>(vm: &'a VM) -> &'a TcType;
    fn make_type(vm: &VM) -> TcType {
        <Self as VMType>::vm_type(vm).clone()
    }
}
pub trait VMValue<'a> : VMType {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>);
    fn from_value(value: Value<'a>) -> Option<Self>;
}

impl VMType for () {
    fn vm_type<'a>(_: &VM) -> &'a TcType {
        &UNIT_TYPE
    }
}
impl <'a> VMValue<'a> for () {
    fn push<'b>(self, _: &VM<'a>, _: &mut StackFrame<'a, 'b>) {
    }
    fn from_value(_: Value) -> Option<()> {
        Some(())
    }
}

impl VMType for VMInt {
    fn vm_type<'a>(_: &'a VM) -> &'a TcType {
        &INT_TYPE
    }
}
impl <'a> VMValue<'a> for VMInt {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Value::Int(self));
    }
    fn from_value(value: Value<'a>) -> Option<VMInt> {
        match value {
            Value::Int(i) => Some(i),
            _ => None
        }
    }
}
impl VMType for f64 {
    fn vm_type<'a>(_: &'a VM) -> &'a TcType {
        &FLOAT_TYPE
    }
}
impl <'a> VMValue<'a> for f64 {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Value::Float(self));
    }
    fn from_value(value: Value<'a>) -> Option<f64> {
        match value {
            Value::Float(f) => Some(f),
            _ => None
        }
    }
}
impl VMType for bool {
    fn vm_type<'a>(_: &'a VM) -> &'a TcType {
        &BOOL_TYPE
    }
}
impl <'a> VMValue<'a> for bool {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Value::Int(if self { 1 } else { 0 }));
    }
    fn from_value(value: Value<'a>) -> Option<bool> {
        match value {
            Value::Int(1) => Some(true),
            Value::Int(0) => Some(false),
            _ => None
        }
    }
}
impl <T: Any + VMType> VMType for Box<T> {
    fn vm_type<'a>(vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
}
impl <'a, T: ?Sized + Any + VMType + Clone> VMValue<'a> for Box<T> {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Value::Userdata(Userdata_::new(vm, self)));
    }
    fn from_value(value: Value<'a>) -> Option<Box<T>> {
        match value {
            Value::Userdata(v) => v.data.borrow().downcast_ref::<T>().map(|x| box x.clone()),
            _ => None
        }
    }
}
impl <T: Any> VMType for *mut T {
    fn vm_type<'a>(vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
}
impl <'a, T: Any> VMValue<'a> for *mut T {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Value::Userdata(Userdata_::new(vm, self)));
    }
    fn from_value(value: Value<'a>) -> Option<*mut T> {
        match value {
            Value::Userdata(v) => v.data.borrow().downcast_ref::<*mut T>().map(|x| *x),
            _ => None
        }
    }
}

fn vm_type<'a, T: ?Sized + VMType>(vm: &'a VM) -> &'a TcType {
    <T as VMType>::vm_type(vm)
}

fn make_type<T: ?Sized + VMType>(vm: &VM) -> TcType {
    <T as VMType>::make_type(vm)
}

pub trait Get<'a, 'b> {
    fn get_function(vm: &'a VM<'b>, name: &str) -> Option<Self>;
}
macro_rules! make_get {
    ($($args:ident),*) => (
impl <'a, 'b, $($args : VMValue<'b>,)* R: VMValue<'b>> Get<'a, 'b> for Callable<'a, 'b, ($($args,)*), R> {
    fn get_function(vm: &'a VM<'b>, name: &str) -> Option<Callable<'a, 'b, ($($args,)*), R>> {
        let value = match vm.get_global(name) {
            Some(global) => {
                match global.type_of() {
                    &Type::Function(ref args, ref return_type) => {
                        let mut arg_iter = args.iter();
                        let ok = $({
                            arg_iter.next().unwrap() == vm_type::<$args>(vm)
                            } &&)* true;
                        if arg_iter.next().is_none() && ok && **return_type == *vm_type::<R>(vm) {
                            Some(FunctionRef { value: global.value.get(), _marker: PhantomData })
                        }
                        else {
                            None
                        }
                    }
                    _ => None
                }
            }
            None => None
        };
        match value {
            Some(value) => Some(Callable { vm: vm, value: value }),
            None => None
        }
    }
}
)}

make_get!();
make_get!(A);
make_get!(A, B);
make_get!(A, B, C);
make_get!(A, B, C, D);
make_get!(A, B, C, D, E);
make_get!(A, B, C, D, E, F);
make_get!(A, B, C, D, E, F, G);

pub struct Callable<'a, 'b: 'a , Args, R> {
    vm: &'a VM<'b>,
    value: FunctionRef<'b, Args, R>
}
struct FunctionRef<'a, Args, R> {
    value: Value<'a>,
    _marker: PhantomData<fn (Args) -> R>
}

impl <'a, Args, R> Copy for FunctionRef<'a, Args, R> { }
impl <'a, Args, R> Clone for FunctionRef<'a, Args, R> { fn clone(&self) -> FunctionRef<'a, Args, R> { *self } }

impl <'b, Args, R> VMType for FunctionRef<'b, Args, R> {
    fn vm_type<'a>(vm: &'a VM) -> &'a TcType {
        vm.get_type::<&fn (Args) -> R>()
    }
}

impl <'a, Args, R> VMValue<'a> for FunctionRef<'a, Args, R> {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) {
        stack.push(self.value);
    }
    fn from_value(value: Value<'a>) -> Option<FunctionRef<'a, Args, R>> {
        Some(FunctionRef { value: value, _marker: PhantomData })//TODO not type safe
    }
}

impl <'a, 'b, A: VMValue<'b>, R: VMValue<'b>> Callable<'a, 'b, (A,), R> {
    pub fn call(&mut self, a: A) -> Result<R, String> {
        let mut stack = StackFrame::new_empty(self.vm);
        self.value.push(self.vm, &mut stack);
        a.push(self.vm, &mut stack);
        stack = try!(self.vm.execute(stack, &[Call(1)], &BytecodeFunction::empty()));
        match VMValue::from_value(stack.pop()) {
            Some(x) => Ok(x),
            None => Err("Wrong type".to_string())
        }
    }
}
impl <'a, 'b, A: VMValue<'b>, B: VMValue<'b>, R: VMValue<'b>> Callable<'a, 'b, (A, B), R> {
    pub fn call2(&mut self, a: A, b: B) -> Result<R, String> {
        let mut stack = StackFrame::new_empty(self.vm);
        self.value.push(self.vm, &mut stack);
        a.push(self.vm, &mut stack);
        b.push(self.vm, &mut stack);
        stack = try!(self.vm.execute(stack, &[Call(2)], &BytecodeFunction::empty()));
        match VMValue::from_value(stack.pop()) {
            Some(x) => Ok(x),
            None => Err("Wrong type".to_string())
        }
    }
}

pub fn get_function<'a, 'b, T: Get<'a, 'b>>(vm: &'a VM<'b>, name: &str) -> Option<T> {
    Get::get_function(vm, name)
}


pub trait VMFunction<'a> {
    fn unpack_and_call(&self, vm: &VM<'a>);
}
macro_rules! count {
    () => { 0 };
    ($_e: ident) => { 1 };
    ($_e: ident, $($rest: ident),*) => { 1 + count!($($rest),*) }
}

macro_rules! make_vm_function {
    ($($args:ident),*) => (
impl <$($args: VMType,)* R: VMType> VMType for fn ($($args),*) -> R {
    #[allow(non_snake_case)]
    fn vm_type<'r>(vm: &'r VM) -> &'r TcType {
        vm.get_type::<fn ($($args),*) -> R>()
    }
    #[allow(non_snake_case)]
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::Function(args, box make_type::<R>(vm))
    }
}

impl <'a, $($args : VMValue<'a>,)* R: VMValue<'a>> VMFunction<'a> for fn ($($args),*) -> R {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(&self, vm: &VM<'a>) {
        let n_args = count!($($args),*);
        let mut stack = StackFrame::new(vm.stack.borrow_mut(), n_args, None);
        let mut i = 0;
        $(let $args = {
            let x = VMValue::from_value(stack[i].clone()).unwrap();
            i += 1;
            x
        });*;
        let r = (*self)($($args),*);
        r.push(vm, &mut stack);
    }
}
impl <'a, 's, $($args: VMType,)* R: VMType> VMType for Fn($($args),*) -> R + 's {
    #[allow(non_snake_case)]
    fn vm_type<'r>(vm: &'r VM) -> &'r TcType {
        vm.get_type::<fn ($($args),*) -> R>()
    }
    #[allow(non_snake_case)]
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::Function(args, box make_type::<R>(vm))
    }
}
impl <'a, 's, $($args : VMValue<'a>,)* R: VMValue<'a>> VMFunction<'a> for Box<Fn($($args),*) -> R + 's> {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(&self, vm: &VM<'a>) {
        let n_args = count!($($args),*);
        let mut stack = StackFrame::new(vm.stack.borrow_mut(), n_args, None);
        let mut i = 0;
        $(let $args = {
            let x = VMValue::from_value(stack[i].clone()).unwrap();
            i += 1;
            x
        });*;
        let r = (*self)($($args),*);
        r.push(vm, &mut stack);
    }
}
    )
}

make_vm_function!();
make_vm_function!(A);
make_vm_function!(A, B);
make_vm_function!(A, B, C);
make_vm_function!(A, B, C, D);
make_vm_function!(A, B, C, D, E);
make_vm_function!(A, B, C, D, E, F);
make_vm_function!(A, B, C, D, E, F, G);

#[macro_export]
macro_rules! vm_function {
    ($func: expr) => ({
        fn wrapper<'a, 'b, 'c>(vm: &VM<'a>) {
            $func.unpack_and_call(vm)
        }
        wrapper
    })
}

