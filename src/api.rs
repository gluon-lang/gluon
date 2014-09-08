#![macro_escape]
use vm::{VM, Value, Int, Float, Function, Userdata, StackFrame};
use typecheck::{TcType, Typed, FunctionType, unit_type_tc, bool_type_tc, int_type_tc, float_type_tc};
use compiler::CallGlobal;
use std::any::{Any, AnyRefExt};
use std::boxed::BoxAny;

pub trait VMType {
    fn vm_type<'a>(_: Option<Self>, vm: &'a VM) -> &'a TcType;
    fn make_type(x: Option<Self>, vm: &VM) -> TcType {
        VMType::vm_type(x, vm).clone()
    }
}
pub trait VMValue : VMType {
    fn push(self, stack: &mut StackFrame);
    fn from_value(value: Value) -> Option<Self>;
}
impl VMType for () {
    fn vm_type<'a>(_: Option<()>, _: &'a VM) -> &'a TcType {
        &unit_type_tc
    }
}
impl VMValue for () {
    fn push(self, _: &mut StackFrame) {
    }
    fn from_value(_: Value) -> Option<()> {
        Some(())
    }
}

impl VMType for int {
    fn vm_type<'a>(_: Option<int>, _: &'a VM) -> &'a TcType {
        &int_type_tc
    }
}
impl VMValue for int {
    fn push(self, stack: &mut StackFrame) {
        stack.push(Int(self));
    }
    fn from_value(value: Value) -> Option<int> {
        match value {
            Int(i) => Some(i),
            _ => None
        }
    }
}
impl VMType for f64 {
    fn vm_type<'a>(_: Option<f64>, _: &'a VM) -> &'a TcType {
        &float_type_tc
    }
}
impl VMValue for f64 {
    fn push(self, stack: &mut StackFrame) {
        stack.push(Float(self));
    }
    fn from_value(value: Value) -> Option<f64> {
        match value {
            Float(f) => Some(f),
            _ => None
        }
    }
}
impl VMType for bool {
    fn vm_type<'a>(_: Option<bool>, _: &'a VM) -> &'a TcType {
        &bool_type_tc
    }
}
impl VMValue for bool {
    fn push(self, stack: &mut StackFrame) {
        stack.push(Int(if self { 1 } else { 0 }));
    }
    fn from_value(value: Value) -> Option<bool> {
        match value {
            Int(1) => Some(true),
            Int(0) => Some(false),
            _ => None
        }
    }
}
impl <T: 'static + BoxAny + Clone> VMType for Box<T> {
    fn vm_type<'a>(_: Option<Box<T>>, vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
}
impl <T: 'static + BoxAny + Clone> VMValue for Box<T> {
    fn push(self, stack: &mut StackFrame) {
        stack.push(Userdata(Userdata::new(self as Box<Any>)));
    }
    fn from_value(value: Value) -> Option<Box<T>> {
        match value {
            Userdata(v) => v.data.borrow().downcast_ref::<T>().map(|x| box x.clone()),
            _ => None
        }
    }
}
impl <T: 'static> VMType for *mut T {
    fn vm_type<'a>(_: Option<*mut T>, vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
}
impl <T: 'static> VMValue for *mut T {
    fn push(self, stack: &mut StackFrame) {
        stack.push(Userdata(Userdata::new(box self as Box<Any>)));
    }
    fn from_value(value: Value) -> Option<*mut T> {
        match value {
            Userdata(v) => v.data.borrow().downcast_ref::<*mut T>().map(|x| *x),
            _ => None
        }
    }
}

fn vm_type<'a, T: VMValue>(vm: &'a VM) -> &'a TcType {
    VMType::vm_type(None::<T>, vm)
}

fn make_type<'a, T: VMValue>(vm: &'a VM) -> TcType {
    VMType::make_type(None::<T>, vm)
}

trait Get<'a> {
    fn get_function(vm: &'a VM<'a>, name: &str) -> Option<Self>;
}
macro_rules! make_get(
    ($($args:ident),*) => (
impl <'a, $($args : VMValue,)* R: VMValue> Get<'a> for Callable<'a, ($($args,)*), R> {
    fn get_function(vm: &'a VM<'a>, name: &str) -> Option<Callable<'a, ($($args,)*), R>> {
        let value = match vm.get_global(name) {
            Some((function_ref, global)) => {
                match global.type_of() {
                    &FunctionType(ref args, ref return_type) => {
                        let mut arg_iter = args.iter();
                        let ok = $({
                            arg_iter.next().unwrap() == vm_type::<$args>(vm)
                            } &&)* true;
                        if arg_iter.next().is_none() && ok && **return_type == *vm_type::<R>(vm) {
                            Some(FunctionRef { value: function_ref })
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
))

make_get!()
make_get!(A)
make_get!(A, B)
make_get!(A, B, C)
make_get!(A, B, C, D)
make_get!(A, B, C, D, E)
make_get!(A, B, C, D, E, F, G)

pub struct Callable<'a, Args, R> {
    vm: &'a VM<'a>,
    value: FunctionRef<Args, R>
}
struct FunctionRef<Args, R> {
    value: uint
}

impl <Args, R> VMType for FunctionRef<Args, R> {
    fn vm_type<'a>(_: Option<FunctionRef<Args, R>>, vm: &'a VM) -> &'a TcType {
        vm.get_type::<|Args|:'static -> R>()
    }
}

impl <Args, R> VMValue for FunctionRef<Args, R> {
    fn push(self, stack: &mut StackFrame) {
        stack.push(Function(self.value));
    }
    fn from_value(value: Value) -> Option<FunctionRef<Args, R>> {
        match value {
            Function(i) => Some(FunctionRef { value: i }),//TODO not type safe
            _ => None
        }
    }
}

impl <'a, A: VMValue, R: VMValue> Callable<'a, (A,), R> {
    pub fn call(&mut self, a: A) -> R {
        let mut vec = Vec::new();
        {
            let mut stack = StackFrame::new(&mut vec, 0, [].as_mut_slice());
            self.value.push(&mut stack);
            a.push(&mut stack);
            self.vm.execute(stack, &[CallGlobal(1)]);
        }
        vec.pop().and_then(|value| VMValue::from_value(value))
            .expect("Wrong type")
    }
}
impl <'a, A: VMValue, B: VMValue, R: VMValue> Callable<'a, (A, B), R> {
    pub fn call2(&mut self, a: A, b: B) -> R {
        let mut vec = Vec::new();
        {
            let mut stack = StackFrame::new(&mut vec, 0, [].as_mut_slice());
            self.value.push(&mut stack);
            a.push(&mut stack);
            b.push(&mut stack);
            self.vm.execute(stack, &[CallGlobal(2)]);
        }
        vec.pop().and_then(|value| VMValue::from_value(value))
            .expect("Wrong type")
    }
}

pub fn get_function<'a, T: Get<'a>>(vm: &'a VM<'a>, name: &str) -> Option<T> {
    Get::get_function(vm, name)
}

trait VMFunction {
    fn unpack_and_call(mut stack: StackFrame, f: Self);
}

macro_rules! make_vm_function(
    ($($args:ident),*) => (
impl <$($args: VMValue,)* R: VMValue> VMType for fn ($($args),*) -> R {
    #[allow(non_snake_case)]
    fn vm_type<'a>(_: Option<fn ($($args),*) -> R>, vm: &'a VM) -> &'a TcType {
        vm.get_type::<fn ($($args),*) -> R>()
    }
    #[allow(non_snake_case)]
    fn make_type(_: Option<fn ($($args),*) -> R>, vm: &VM) -> TcType {
        FunctionType(vec![$(make_type::<$args>(vm)),*], box make_type::<R>(vm))
    }
}

impl <$($args : VMValue,)* R: VMValue> VMFunction for fn ($($args),*) -> R {
    #[allow(non_snake_case, unused_mut, dead_assignment, unused_variable)]
    fn unpack_and_call(mut stack: StackFrame, f: fn ($($args),*) -> R) {
        let mut i = 0u;
        $(let $args = {
            let x = VMValue::from_value(stack[i].clone()).unwrap();
            i += 1;
            x
        });*;
        let r = f($($args),*);
        r.push(&mut stack);
    }
}
    )
)
pub fn unpack_and_call<F: VMFunction>(stack: StackFrame, f: F) {
    VMFunction::unpack_and_call(stack, f)
}

make_vm_function!()
make_vm_function!(A)
make_vm_function!(A, B)
make_vm_function!(A, B, C)
make_vm_function!(A, B, C, D)
make_vm_function!(A, B, C, D, E)
make_vm_function!(A, B, C, D, E, F)
make_vm_function!(A, B, C, D, E, F, G)

#[macro_export]
macro_rules! vm_function(
    ($func: expr) => ({
        fn wrapper(_: &VM, stack: StackFrame) {
            unpack_and_call(stack, $func)
        }
        wrapper
    })
)

#[macro_export]
macro_rules! define_function(
    ($vm: expr, $name: expr, $func: expr) => ({
        let vm = $vm;
        let (args, ret) = match VMType::make_type(Some($func), vm) {
            FunctionType(ref args, ref return_type) => (args.clone(), (**return_type).clone()),
            _ => fail!()
        };
        vm.extern_function($name, args, ret, vm_function!($func))
    })
)

#[cfg(test)]
mod tests {
    use super::{Get, Callable, VMType, unpack_and_call};

    use typecheck::FunctionType;
    use vm::{VM, load_script, StackFrame};
    use std::io::BufReader;

    #[test]
    fn call_function() {
        let s =
r"
fn add10(x: int) -> int {
    x + 10
}
fn mul(x: float, y: float) -> float {
    x * y
}
";
        let mut vm = VM::new();
        let mut buffer = BufReader::new(s.as_bytes());
        load_script(&mut vm, &mut buffer)
            .unwrap_or_else(|err| fail!("{}", err));
        {
            let mut f: Callable<(int,), int> = Get::get_function(&vm, "add10")
                .expect("No function");
            let result = f.call(2);
            assert_eq!(result, 12);
        }
        let mut f: Callable<(f64, f64), f64> = Get::get_function(&vm, "mul")
            .expect("No function");
        let result = f.call2(4., 5.);
        assert_eq!(result, 20.);
    }
    #[test]
    fn pass_userdata() {
        let s =
r"
fn id(x: Test) -> Test {
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
            x: int
        }
        vm.register_type::<Test>("Test")
            .unwrap_or_else(|_| fail!("Could not add type"));
        define_function!(&mut vm, "test", test);
        let mut buffer = BufReader::new(s.as_bytes());
        load_script(&mut vm, &mut buffer)
            .unwrap_or_else(|err| fail!("{}", err));

        let mut test = Test { x: 123 };
        {
            let mut f: Callable<(*mut Test,), *mut Test> = Get::get_function(&vm, "id")
                .expect("No function id");
            let result = f.call(&mut test);
            assert!(result == &mut test as *mut Test);
        }
        let mut f: Callable<(*mut Test,), bool> = Get::get_function(&vm, "test")
            .expect("No function test");
        let result = f.call(&mut test);
        assert!(result);
        assert_eq!(test.x, 123 * 2);
    }
}
