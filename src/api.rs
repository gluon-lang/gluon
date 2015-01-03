#![macro_escape]
use vm::{VM, VMResult, Value, Int, Float, Function, Userdata, Userdata_, StackFrame};
use typecheck::{TcType, Typed, FunctionType, UNIT_TYPE, BOOL_TYPE, INT_TYPE, FLOAT_TYPE};
use compiler::Instruction::CallGlobal;
use std::any::{Any, AnyRefExt};
use std::boxed::BoxAny;

pub trait VMType {
    fn vm_type<'a>(_: Option<&Self>, vm: &'a VM) -> &'a TcType;
    fn make_type(x: Option<&Self>, vm: &VM) -> TcType {
        VMType::vm_type(x, vm).clone()
    }
}
pub trait VMValue<'a> : VMType {
    fn push<'b, 'c>(self, stack: &mut StackFrame<'a, 'b>);
    fn from_value(value: Value<'a>) -> Option<Self>;
}

impl VMType for () {
    fn vm_type<'a>(_: Option<&()>, _: &VM) -> &'a TcType {
        &UNIT_TYPE
    }
}
impl <'a> VMValue<'a> for () {
    fn push<'b, 'c>(self, _: &mut StackFrame<'a, 'b>) {
    }
    fn from_value(_: Value) -> Option<()> {
        Some(())
    }
}

impl VMType for int {
    fn vm_type<'a>(_: Option<&int>, _: &'a VM) -> &'a TcType {
        &INT_TYPE
    }
}
impl <'a> VMValue<'a> for int {
    fn push<'b, 'c>(self, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Int(self));
    }
    fn from_value(value: Value<'a>) -> Option<int> {
        match value {
            Int(i) => Some(i),
            _ => None
        }
    }
}
impl VMType for f64 {
    fn vm_type<'a>(_: Option<&f64>, _: &'a VM) -> &'a TcType {
        &FLOAT_TYPE
    }
}
impl <'a> VMValue<'a> for f64 {
    fn push<'b, 'c>(self, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Float(self));
    }
    fn from_value(value: Value<'a>) -> Option<f64> {
        match value {
            Float(f) => Some(f),
            _ => None
        }
    }
}
impl VMType for bool {
    fn vm_type<'a>(_: Option<&bool>, _: &'a VM) -> &'a TcType {
        &BOOL_TYPE
    }
}
impl <'a> VMValue<'a> for bool {
    fn push<'b, 'c>(self, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Int(if self { 1 } else { 0 }));
    }
    fn from_value(value: Value<'a>) -> Option<bool> {
        match value {
            Int(1) => Some(true),
            Int(0) => Some(false),
            _ => None
        }
    }
}
impl <T: 'static + BoxAny + Clone> VMType for Box<T> {
    fn vm_type<'a>(_: Option<&Box<T>>, vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
}
impl <'a, T: 'static + BoxAny + Clone> VMValue<'a> for Box<T> {
    fn push<'b, 'c>(self, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Userdata(Userdata_::new(self as Box<Any>)));
    }
    fn from_value(value: Value<'a>) -> Option<Box<T>> {
        match value {
            Userdata(v) => v.data.borrow().downcast_ref::<T>().map(|x| box x.clone()),
            _ => None
        }
    }
}
impl <T: 'static> VMType for *mut T {
    fn vm_type<'a>(_: Option<&*mut T>, vm: &'a VM) -> &'a TcType {
        vm.get_type::<T>()
    }
}
impl <'a, T: 'static> VMValue<'a> for *mut T {
    fn push<'b, 'c>(self, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Userdata(Userdata_::new(box self as Box<Any>)));
    }
    fn from_value(value: Value<'a>) -> Option<*mut T> {
        match value {
            Userdata(v) => v.data.borrow().downcast_ref::<*mut T>().map(|x| *x),
            _ => None
        }
    }
}

fn vm_type<'a, T: VMType>(vm: &'a VM) -> &'a TcType {
    VMType::vm_type(None::<&T>, vm)
}

fn make_type<T: VMType>(vm: &VM) -> TcType {
    VMType::make_type(None::<&T>, vm)
}

pub trait Get<'a, 'b> {
    fn get_function(vm: &'a VM<'b>, name: &str) -> Option<Self>;
}
macro_rules! make_get {
    ($($args:ident),*) => (
impl <'a, 'b, $($args : VMValue<'b>,)* R: VMValue<'b>> Get<'a, 'b> for Callable<'a, 'b, ($($args,)*), R> {
    fn get_function(vm: &'a VM<'b>, name: &str) -> Option<Callable<'a, 'b, ($($args,)*), R>> {
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
    value: FunctionRef<Args, R>
}
struct FunctionRef<Args, R> {
    value: uint
}

impl <Args, R> Copy for FunctionRef<Args, R> { }

impl <Args, R> VMType for FunctionRef<Args, R> {
    fn vm_type<'a>(_: Option<&FunctionRef<Args, R>>, vm: &'a VM) -> &'a TcType {
        vm.get_type::<|Args|:'static -> R>()
    }
}

impl <'a, Args, R> VMValue<'a> for FunctionRef<Args, R> {
    fn push<'b, 'c>(self, stack: &mut StackFrame<'a, 'b>) {
        stack.push(Function(self.value));
    }
    fn from_value(value: Value<'a>) -> Option<FunctionRef<Args, R>> {
        match value {
            Function(i) => Some(FunctionRef { value: i }),//TODO not type safe
            _ => None
        }
    }
}

impl <'a, 'b, A: VMValue<'b>, R: VMValue<'b>> Callable<'a, 'b, (A,), R> {
    pub fn call(&mut self, a: A) -> Result<R, String> {
        let mut stack = StackFrame::new_empty(self.vm);
        self.value.push(&mut stack);
        a.push(&mut stack);
        stack = try!(self.vm.execute(stack, &[CallGlobal(1)]));
        match VMValue::from_value(stack.pop()) {
            Some(x) => Ok(x),
            None => Err("Wrong type".to_string())
        }
    }
}
impl <'a, 'b, A: VMValue<'b>, B: VMValue<'b>, R: VMValue<'b>> Callable<'a, 'b, (A, B), R> {
    pub fn call2(&mut self, a: A, b: B) -> Result<R, String> {
        let mut stack = StackFrame::new_empty(self.vm);
        self.value.push(&mut stack);
        a.push(&mut stack);
        b.push(&mut stack);
        stack = try!(self.vm.execute(stack, &[CallGlobal(2)]));
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
    ($_e: ident $(, $rest: ident)*) => { 1 + count!($($rest),*) }
}

macro_rules! make_vm_function {
    ($($args:ident),*) => (
impl <$($args: VMType,)* R: VMType> VMType for fn ($($args),*) -> R {
    #[allow(non_snake_case)]
    fn vm_type<'r>(_: Option<&fn ($($args),*) -> R>, vm: &'r VM) -> &'r TcType {
        vm.get_type::<fn ($($args),*) -> R>()
    }
    #[allow(non_snake_case)]
    fn make_type(_: Option<&fn ($($args),*) -> R>, vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        FunctionType(args, box make_type::<R>(vm))
    }
}

impl <'a, $($args : VMValue<'a>,)* R: VMValue<'a>> VMFunction<'a> for fn ($($args),*) -> R {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(vm: &VM<'a>, f: &fn ($($args),*) -> R) {
        let n_args = count!($($args),*);
        let mut stack = StackFrame::new(vm.stack.borrow_mut(), n_args, None);
        let mut i = 0u;
        $(let $args = {
            let x = VMValue::from_value(stack[i].clone()).unwrap();
            i += 1;
            x
        });*;
        let r = (*f)($($args),*);
        r.push(&mut stack);
    }
}
impl <'a, $($args: VMType,)* R: VMType> VMType for Box<Fn($($args),*) -> R + 'static> {
    #[allow(non_snake_case)]
    fn vm_type<'r>(_: Option<&Box<Fn($($args),*) -> R>>, vm: &'r VM) -> &'r TcType {
        vm.get_type::<Box<Fn($($args),*) -> R>>()
    }
    #[allow(non_snake_case)]
    fn make_type(_: Option<&Box<Fn($($args),*) -> R>>, vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        FunctionType(args, box make_type::<R>(vm))
    }
}
impl <'a, $($args : VMValue<'a>,)* R: VMValue<'a>> VMFunction<'a> for Box<Fn($($args),*) -> R + 'static> {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(vm: &VM<'a>, f: &Box<Fn($($args),*) -> R>) {
        let n_args = count!($($args),*);
        let mut stack = StackFrame::new(vm.stack.borrow_mut(), n_args, None);
        let mut i = 0u;
        $(let $args = {
            let x = VMValue::from_value(stack[i].clone()).unwrap();
            i += 1;
            x
        });*;
        let r = f.call(($($args,)*));
        r.push(&mut stack);
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
    let (args, ret) = match VMType::make_type(None::<&F>, vm) {
        FunctionType(ref args, ref return_type) => (args.clone(), (**return_type).clone()),
        _ => panic!()
    };
    vm.extern_function(name, args, ret, box move |vm| unpack_and_call(vm, &f))
}

#[cfg(test)]
mod tests {
    use super::{Get, Callable, define_function};

    use vm::{VM, load_script};
    use std::io::BufReader;

    #[test]
    fn call_function() {
        let s =
r"
fn add10(x: Int) -> Int {
    x + 10
}
fn mul(x: Float, y: Float) -> Float {
    x * y
}
";
        let mut vm = VM::new();
        let mut buffer = BufReader::new(s.as_bytes());
        load_script(&mut vm, &mut buffer)
            .unwrap_or_else(|err| panic!("{}", err));
        {
            let mut f: Callable<(int,), int> = Get::get_function(&vm, "add10")
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
        define_function(&vm, "mul", (box |&:x:int, y:int| x * y) as Box<Fn(int, int) -> int>)
            .unwrap_or_else(|err| panic!("{}", err));

        let mut f: Callable<(int, int), int> = Get::get_function(&vm, "mul")
            .expect("No function id");
        let result = f.call2(2, 3).unwrap();
        assert_eq!(result, 6);
    }
}
