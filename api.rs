
use vm::*;
use typecheck::*;
use compiler::CallGlobal;

trait VMValue {
    fn vm_type(&self) -> TcType;
    fn push(self, stack: &mut StackFrame);
    fn from_value(value: Value) -> Option<Self>;
}
impl VMValue for int {
    fn vm_type(&self) -> TcType {
        int_type_tc.clone()
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
    fn vm_type(&self) -> TcType {
        float_type_tc.clone()
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
impl <T> VMValue for *mut T {
    fn vm_type(&self) -> TcType {
        fail!()
    }
    fn push(self, stack: &mut StackFrame) {
        fail!()
    }
    fn from_value(value: Value) -> Option<*mut T> {
        fail!()
    }
}

fn vm_type<T: VMValue>() -> TcType {
    let t: T = unsafe { ::std::mem::uninitialized() };
    let typ = t.vm_type();
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
                            *arg_iter.next().unwrap() == vm_type::<$args>()
                            })&&*;
                        if arg_iter.next().is_none() && ok && **return_type == vm_type::<$result>() {
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
                            let ok = args[0] == vm_type::<T>();
                            if ok && **return_type == vm_type::<R>() {
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
    fn vm_type(&self) -> TcType {
        fail!()
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
    fn call(&mut self, a: A) -> R {
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
    fn call2(&mut self, a: A, b: B) -> R {
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

mod tests {
    use super::{Get, Callable};

    use vm::{VM, load_script};
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
}
