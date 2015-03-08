use vm::{VM, VMResult, Value, Userdata_, StackFrame, VMInt};
use typecheck::{TcType, Typed, FunctionType, UNIT_TYPE, BOOL_TYPE, INT_TYPE, FLOAT_TYPE};
use compiler::Instruction::CallGlobal;
use std::boxed::BoxAny;
use std::marker::{PhantomData, PhantomFn};

pub trait VMType: PhantomFn<Self> {
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
impl <T: 'static + BoxAny + Clone> VMType for Box<T> {
    fn vm_type<'a>(vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
}
impl <'a, T: 'static + BoxAny + Clone> VMValue<'a> for Box<T> {
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
impl <T: 'static> VMType for *mut T {
    fn vm_type<'a>(vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
}
impl <'a, T: 'static> VMValue<'a> for *mut T {
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

fn vm_type<'a, T: VMType>(vm: &'a VM) -> &'a TcType {
    <T as VMType>::vm_type(vm)
}

fn make_type<T: VMType>(vm: &VM) -> TcType {
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
                    &FunctionType(ref args, ref return_type) => {
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
        stack = try!(self.vm.execute(stack, &[CallGlobal(1)], &[]));
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
        stack = try!(self.vm.execute(stack, &[CallGlobal(2)], &[]));
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
    fn unpack_and_call(vm: &VM<'a>, f: &Self);
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
        FunctionType(args, box make_type::<R>(vm))
    }
}

impl <'a, $($args : VMValue<'a>,)* R: VMValue<'a>> VMFunction<'a> for fn ($($args),*) -> R {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(vm: &VM<'a>, f: &fn ($($args),*) -> R) {
        let n_args = count!($($args),*);
        let mut stack = StackFrame::new(vm.stack.borrow_mut(), n_args, None);
        let mut i = 0;
        $(let $args = {
            let x = VMValue::from_value(stack[i].clone()).unwrap();
            i += 1;
            x
        });*;
        let r = (*f)($($args),*);
        r.push(vm, &mut stack);
    }
}
impl <'a, $($args: VMType,)* R: VMType> VMType for Box<Fn($($args),*) -> R + 'static> {
    #[allow(non_snake_case)]
    fn vm_type<'r>(vm: &'r VM) -> &'r TcType {
        vm.get_type::<Box<Fn($($args),*) -> R>>()
    }
    #[allow(non_snake_case)]
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        FunctionType(args, box make_type::<R>(vm))
    }
}
impl <'a, $($args : VMValue<'a>,)* R: VMValue<'a>> VMFunction<'a> for Box<Fn($($args),*) -> R + 'static> {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(vm: &VM<'a>, f: &Box<Fn($($args),*) -> R>) {
        let n_args = count!($($args),*);
        let mut stack = StackFrame::new(vm.stack.borrow_mut(), n_args, None);
        let mut i = 0;
        $(let $args = {
            let x = VMValue::from_value(stack[i].clone()).unwrap();
            i += 1;
            x
        });*;
        let r = f($($args),*);
        r.push(vm, &mut stack);
    }
}
    )
}

pub fn unpack_and_call<'a, F: VMFunction<'a>>(vm: &VM<'a>, f: &F) {
    VMFunction::unpack_and_call(vm, f)
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
            unpack_and_call(vm, $func)
        }
        wrapper
    })
}


fn define_function<'a, F: VMFunction<'a> + VMType + 'static>(vm: &VM<'a>, name: &str, f: F) -> VMResult<()> {
    let (args, ret) = match make_type::<F>(vm) {
        FunctionType(ref args, ref return_type) => (args.clone(), (**return_type).clone()),
        _ => panic!()
    };
    vm.extern_function(name, args, ret, box move |vm| unpack_and_call(vm, &f))
}

#[cfg(test)]
mod tests {
    use super::{Get, Callable, define_function};

    use vm::{VM, VMInt, load_script};
    use std::io::BufReader;

    #[test]
    fn call_function() {
        let s =
r"
add10 : (Int) -> Int;
add10 = \x -> {
    x + 10
}
mul : (Float, Float) -> Float;
mul = \x y -> {
    x * y
}
";
        let mut vm = VM::new();
        let mut buffer = BufReader::new(s.as_bytes());
        load_script(&mut vm, &mut buffer)
            .unwrap_or_else(|err| panic!("{}", err));
        {
            let mut f: Callable<(VMInt,), VMInt> = Get::get_function(&vm, "add10")
                .expect("No function");
            let result = f.call(2).unwrap();
            assert_eq!(result, 12);
        }
        let mut f: Callable<(f64, f64), f64> = Get::get_function(&vm, "mul")
            .expect("No function");
        let result = f.call2(4., 5.).unwrap();
        assert_eq!(result, 20.);
    }
    #[test]
    fn pass_userdata() {
        let s =
r"
id : (Test) -> Test;
id = \x -> {
    x
}
";
        let mut vm = VM::new();
        fn test(test: *mut Test) -> bool {
            let test = unsafe { &mut *test };
            let x = test.x == 123;
            test.x *= 2;
            x
        }
        struct Test {
            x: VMInt
        }
        vm.register_type::<Test>("Test")
            .unwrap_or_else(|_| panic!("Could not add type"));
        define_function(&vm, "test", test as fn (_) -> _)
            .unwrap_or_else(|err| panic!("{}", err));
        let mut buffer = BufReader::new(s.as_bytes());
        load_script(&mut vm, &mut buffer)
            .unwrap_or_else(|err| panic!("{}", err));

        let mut test = Test { x: 123 };
        {
            let mut f: Callable<(*mut Test,), *mut Test> = Get::get_function(&vm, "id")
                .expect("No function id");
            let result = f.call(&mut test).unwrap();
            assert!(result == &mut test as *mut Test);
        }
        let mut f: Callable<(*mut Test,), bool> = Get::get_function(&vm, "test")
            .expect("No function test");
        let result = f.call(&mut test).unwrap();
        assert!(result);
        assert_eq!(test.x, 123 * 2);
    }
    #[test]
    fn function_object() {
        let vm = VM::new();
        define_function(&vm, "mul", (box |x:VMInt, y:VMInt| x * y) as Box<Fn(VMInt, VMInt) -> VMInt>)
            .unwrap_or_else(|err| panic!("{}", err));

        let mut f: Callable<(VMInt, VMInt), VMInt> = Get::get_function(&vm, "mul")
            .expect("No function id");
        let result = f.call2(2, 3).unwrap();
        assert_eq!(result, 6);
    }
}
