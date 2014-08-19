use vm::*;
use typecheck::*;
use compiler::CallGlobal;
use std::any::{Any, AnyRefExt};
use std::boxed::BoxAny;

pub trait VMValue {
    fn vm_type<'a>(&self, vm: &'a VM) -> &'a TcType;
    fn push(self, stack: &mut StackFrame);
    fn from_value(value: Value) -> Option<Self>;
}
impl VMValue for int {
    fn vm_type<'a>(&self, _: &'a VM) -> &'a TcType {
        &int_type_tc
    }
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
impl VMValue for f64 {
    fn vm_type<'a>(&self, _: &'a VM) -> &'a TcType {
        &float_type_tc
    }
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
impl VMValue for bool {
    fn vm_type<'a>(&self, _: &'a VM) -> &'a TcType {
        &bool_type_tc
    }
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
impl <T: 'static + BoxAny + Clone> VMValue for Box<T> {
    fn vm_type<'a>(&self, vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
    fn push(self, stack: &mut StackFrame) {
        stack.push(Userdata(Data::new(self as Box<Any>)));
    }
    fn from_value(value: Value) -> Option<Box<T>> {
        match value {
            Userdata(v) => v.data.borrow().downcast_ref::<T>().map(|x| box x.clone()),
            _ => None
        }
    }
}
impl <T: 'static> VMValue for *mut T {
    fn vm_type<'a>(&self, vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
    fn push(self, stack: &mut StackFrame) {
        stack.push(Userdata(Data::new(box self as Box<Any>)));
    }
    fn from_value(value: Value) -> Option<*mut T> {
        match value {
            Userdata(v) => v.data.borrow().downcast_ref::<*mut T>().map(|x| *x),
            _ => None
        }
    }
}

fn vm_type<'a, T: VMValue>(vm: &'a VM) -> &'a TcType {
    let t: T = unsafe { ::std::mem::uninitialized() };
    let typ = t.vm_type(vm);
    unsafe { ::std::mem::forget(t) }
    typ
}

trait Get<'a> {
    fn get_function(vm: &'a mut VM, name: &str) -> Option<Self>;
}
macro_rules! make_get(
    ($($args:ident),* -> $result:ident) => (
impl <'a, $($args : VMValue),*, $result: VMValue> Get<'a> for Callable<'a, ($($args),*), $result> {
    fn get_function(vm: &'a mut VM, name: &str) -> Option<Callable<'a, ($($args),*), $result>> {
        let value = match vm.get_global(name) {
            Some((function_ref, global)) => {
                match global.type_of() {
                    &FunctionType(ref args, ref return_type) => {
                        let mut arg_iter = args.iter();
                        let ok = $({
                            arg_iter.next().unwrap() == vm_type::<$args>(vm)
                            })&&*;
                        if arg_iter.next().is_none() && ok && **return_type == *vm_type::<$result>(vm) {
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

make_get!(A, B -> R)

impl <'a, T: VMValue, R: VMValue> Get<'a> for Callable<'a, (T,), R> {
    fn get_function(vm: &'a mut VM, name: &str) -> Option<Callable<'a, (T,), R>> {
        let value = match vm.get_global(name) {
            Some((function_ref, global)) => {
                match global.type_of() {
                    &FunctionType(ref args, ref return_type) => {
                        if args.len() == 1 {
                            let ok = args[0] == *vm_type::<T>(vm);
                            if ok && **return_type == *vm_type::<R>(vm) {
                                Some(FunctionRef { value: function_ref })
                            }
                            else {
                                None
                            }
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


struct Callable<'a, Args, R> {
    vm: &'a mut VM,
    value: FunctionRef<Args, R>
}
struct FunctionRef<Args, R> {
    value: uint
}

impl <Args, R> VMValue for FunctionRef<Args, R> {
    fn vm_type<'a>(&self, vm: &'a VM) -> &'a TcType {
        vm.get_type::<|Args|:'static -> R>()
    }
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
            let mut stack = StackFrame::new(&mut vec, 0, None);
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
            let mut stack = StackFrame::new(&mut vec, 0, None);
            self.value.push(&mut stack);
            a.push(&mut stack);
            b.push(&mut stack);
            self.vm.execute(stack, &[CallGlobal(2)]);
        }
        vec.pop().and_then(|value| VMValue::from_value(value))
            .expect("Wrong type")
    }
}

#[cfg(test)]
mod tests {
    use super::{Get, Callable};

    use vm::{VM, load_script, StackFrame};
    use typecheck::{bool_type_tc};
    use std::io::BufReader;
    use std::any::AnyMutRefExt;

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
            let mut f: Callable<(int,), int> = Get::get_function(&mut vm, "add10")
                .expect("No function");
            let result = f.call(2);
            assert_eq!(result, 12);
        }
        let mut f: Callable<(f64, f64), f64> = Get::get_function(&mut vm, "mul")
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
        fn test(_: &VM, mut stack: StackFrame) {
            use vm::{Int, Userdata};
            let v = match stack.pop() {
                Userdata(ptr) => {
                    let mut cell = ptr.data.borrow_mut();
                    let test: &mut Test = unsafe { &mut **cell.downcast_mut::<*mut Test>().expect("Expected Test type") };
                    let x = if test.x == 123 { 1 } else { 0 };
                    test.x *= 2;
                    x
                }
                _ => 0
            };
            stack.push(Int(v));
        }
        struct Test {
            x: int
        }
        let test_type = vm.register_type::<Test>("Test")
            .unwrap_or_else(|_| fail!("Could not add type"))
            .clone();
        vm.extern_function("test", vec![test_type], bool_type_tc.clone(), test);
        let mut buffer = BufReader::new(s.as_bytes());
        load_script(&mut vm, &mut buffer)
            .unwrap_or_else(|err| fail!("{}", err));

        let mut test = Test { x: 123 };
        {
            let mut f: Callable<(*mut Test,), *mut Test> = Get::get_function(&mut vm, "id")
                .expect("No function id");
            let result = f.call(&mut test);
            assert!(result == &mut test as *mut Test);
        }
        let mut f: Callable<(*mut Test,), bool> = Get::get_function(&mut vm, "test")
            .expect("No function test");
        let result = f.call(&mut test);
        assert!(result);
        assert_eq!(test.x, 123 * 2);
    }
}
