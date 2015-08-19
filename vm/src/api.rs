use base::ast;
use base::interner::InternedStr;
use vm::{VM, VMResult, Status, BytecodeFunction, Value, Userdata_, StackFrame, VMInt, Error, Root, RootStr};
use check::typecheck::{TcType, Typed, Type};
use types::Instruction::Call;
use types::VMIndex;
use std::any::Any;
use std::fmt;
use std::marker::PhantomData;


#[derive(Debug)]
pub struct IO<T>(pub T);

pub trait VMType {
    type Type: ?Sized + Any;

    fn make_type(vm: &VM) -> TcType {
        TcType::from(vm_type::<Self>(vm).clone())
    }

    //How many extra arguments a function returning this type requires
    fn extra_args() -> VMIndex { 0 }
}

pub trait Pushable<'a> : VMType {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status;
}
pub trait Getable<'a, 'vm>: Sized {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Self>;
}
pub trait VMValue<'a, 'vm> : Pushable<'a> + Getable<'a, 'vm> { }
impl <'a, 'vm, T> VMValue<'a, 'vm> for T where T: Pushable<'a> + Getable<'a, 'vm> { }

impl VMType for () {
    type Type = Self;
}
impl <'a> Pushable<'a> for () {
    fn push<'b>(self, _: &VM<'a>, _: &mut StackFrame<'a, 'b>) -> Status {
        Status::Ok
    }
}
impl <'a, 'vm> Getable<'a, 'vm> for () {
    fn from_value(_: &'vm VM<'a>, _: Value) -> Option<()> {
        Some(())
    }
}

impl VMType for VMInt {
    type Type = Self;
}
impl <'a> Pushable<'a> for VMInt {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Int(self));
        Status::Ok
    }
}
impl <'a, 'vm> Getable<'a, 'vm> for VMInt {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<VMInt> {
        match value {
            Value::Int(i) => Some(i),
            _ => None
        }
    }
}
impl VMType for f64 {
    type Type = Self;
}
impl <'a> Pushable<'a> for f64 {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Float(self));
        Status::Ok
    }
}
impl <'a, 'vm> Getable<'a, 'vm> for f64 {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<f64> {
        match value {
            Value::Float(f) => Some(f),
            _ => None
        }
    }
}
impl VMType for bool {
    type Type = Self;
}
impl <'a> Pushable<'a> for bool {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Int(if self { 1 } else { 0 }));
        Status::Ok
    }
}
impl <'a, 'vm> Getable<'a, 'vm> for bool {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<bool> {
        match value {
            Value::Int(1) => Some(true),
            Value::Int(0) => Some(false),
            _ => None
        }
    }
}
impl VMType for str {
    type Type = String;
}
impl <'s> VMType for &'s str {
    type Type = <str as VMType>::Type;
}
impl VMType for String {
    type Type = <str as VMType>::Type;
}
impl <'a, 's> Pushable<'a> for &'s str {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        let s = vm.alloc(&mut stack.stack.values, self);
        stack.push(Value::String(s));
        Status::Ok
    }
}
impl <'a,'vm> Getable<'a, 'vm> for String {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<String> {
        match value {
            Value::String(i) => Some(String::from(&i[..])),
            _ => None
        }
    }
}
impl <'a> Pushable<'a> for String {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        let s = vm.alloc(&mut stack.stack.values, &self[..]);
        stack.push(Value::String(s));
        Status::Ok
    }
}

impl <T: VMType> VMType for Box<T> {
    type Type = T::Type;
}
impl <'a, T: Any + VMType> Pushable<'a> for Box<T> {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Userdata(Userdata_::new(vm, self)));
        Status::Ok
    }
}

impl <T: VMType> VMType for *mut T {
    type Type = T::Type;
}
impl <'a, T: VMType + Any> Pushable<'a> for *mut T {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Userdata(Userdata_::new(vm, self)));
        Status::Ok
    }
}
impl <'a, 'vm, T: Any> Getable<'a, 'vm> for *mut T {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<*mut T> {
        match value {
            Value::Userdata(v) => v.data.downcast_ref::<*mut T>().map(|x| *x),
            _ => None
        }
    }
}
impl <T: VMType + Any> VMType for Option<T>
where T::Type: Sized {
    type Type = Option<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        let ctor = ast::TypeConstructor::Data(vm.intern("Option"));
        ast::Type::data(ctor, vec![T::make_type(vm)])
    }
}
impl <'a, T: Pushable<'a> + Any> Pushable<'a> for Option<T>
where T::Type: Sized {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        match self {
            Some(value) => {
                let len = stack.len();
                value.push(vm, stack);
                let value = vm.new_data(1, &[stack.pop()]);
                assert!(stack.len() == len);
                stack.push(value);
            }
            None => {
                let value = vm.new_data(0, &[]);
                stack.push(value);
            }
        }
        Status::Ok
    }
}
impl <'a, 'vm, T: Getable<'a, 'vm>> Getable<'a, 'vm> for Option<T> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Option<T>> {
        match value {
            Value::Data(data) => {
                if data.tag == 0 {
                    Some(None)
                }
                else {
                    T::from_value(vm, data.fields[1].get()).map(Some)
                }
            }
            _ => None
        }
    }
}

impl <T: VMType, E> VMType for Result<T, E> {
    type Type = T::Type;
}
impl <'a, T: Pushable<'a>, E: fmt::Display> Pushable<'a> for Result<T, E> {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        match self {
            Ok(value) => {
                value.push(vm, stack);
                Status::Ok
            }
            Err(err) => {
                let msg = format!("{}", err);
                let s = vm.alloc(&mut stack.stack.values, &msg[..]);
                stack.push(Value::String(s));
                Status::Error
            }
        }
    }
}

impl <T: VMType> VMType for IO<T>
where T::Type: Sized {
    type Type = IO<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        ast::Type::data(ast::TypeConstructor::Data(vm.intern("IO")), vec![T::make_type(vm)])
    }
    fn extra_args() -> VMIndex { 1 }
}
impl <'a, T: Pushable<'a> + Any> Pushable<'a> for IO<T>
where T::Type: Sized {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        self.0.push(vm, stack)
    }
}

impl <'r, T: Any> VMType for Root<'r, T> {
    type Type = T;
}
impl <'a, 'vm, T: Any> Getable<'a, 'vm> for Root<'vm, T> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Root<'vm, T>> {
        match value {
            Value::Userdata(v) => vm.root::<T>(v.data).map(From::from),
            _ => None
        }
    }
}

impl <'r> VMType for RootStr<'r> {
    type Type = <str as VMType>::Type;
}
impl <'a, 'vm> Getable<'a, 'vm> for RootStr<'vm> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<RootStr<'vm>> {
        match value {
            Value::String(v) => Some(vm.root_string(v)),
            _ => None
        }
    }
}

fn vm_type<'a, T: ?Sized + VMType>(vm: &'a VM) -> &'a Type<InternedStr> {
    vm.get_type::<T::Type>()
}

fn make_type<T: ?Sized + VMType>(vm: &VM) -> TcType {
    <T as VMType>::make_type(vm)
}

pub trait Get<'a, 'b>: Sized {
    fn get_function(vm: &'a VM<'b>, name: &str) -> Option<Self>;
}


pub struct ArgIterator<'a> {
    pub typ: &'a Type<InternedStr>
}
fn arg_iter(typ: &Type<InternedStr>) -> ArgIterator {
    ArgIterator { typ: typ }
}
impl <'a> Iterator for ArgIterator<'a> {
    type Item = &'a Type<InternedStr>;
    fn next(&mut self) -> Option<&'a Type<InternedStr>> {
        match *self.typ {
            Type::Function(ref arg, ref return_type) => {
                self.typ = &**return_type;
                Some(&arg[0])
            }
            _ => None
        }
    }
}

macro_rules! make_get {
    ($($args:ident),*) => (
impl <'a, 'b, $($args : VMType + Pushable<'b>,)* R: VMType + Getable<'b, 'a>> Get<'a, 'b> for Callable<'a, 'b, ($($args,)*), R> {
    fn get_function(vm: &'a VM<'b>, name: &str) -> Option<Callable<'a, 'b, ($($args,)*), R>> {
        let value = match vm.get_global(name) {
            Some(global) => {
                let typ = global.type_of();
                let mut arg_iter = arg_iter(&typ);
                let ok = $({
                    arg_iter.next().expect("Arg iter") == vm_type::<$args>(vm)
                    } &&)* true;
                if arg_iter.next().is_none() && ok && arg_iter.typ == vm_type::<R>(vm) {
                    Some(FunctionRef { value: global.value.get(), _marker: PhantomData })
                }
                else {
                    None
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

impl <'vm, 'b, Args: 'static, R: 'static> VMType for Callable<'vm, 'b, Args, R> {
    type Type = fn (Args) -> R;
}

impl <'vm, 'a, Args: 'static, R: 'static> Pushable<'a> for Callable<'vm, 'a, Args, R> {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(self.value.value);
        Status::Ok
    }
}
impl <'a, 'vm, Args, R> Getable<'a, 'vm> for Callable<'vm, 'a, Args, R> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Callable<'vm, 'a, Args, R>> {
        Some(Callable {
            vm: vm,
            value: FunctionRef { value: value, _marker: PhantomData }
        })//TODO not type safe
    }
}

impl <'b, A: 'static, R: 'static> VMType for FunctionRef<'b, (A,), R> {
    type Type = fn (A) -> R;
}

impl <'a, A: 'static, R: 'static> Pushable<'a> for FunctionRef<'a, (A,), R> {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(self.value);
        Status::Ok
    }
}
impl <'a, 'vm, A, R> Getable<'a, 'vm> for FunctionRef<'a, (A,), R> {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<FunctionRef<'a, (A,), R>> {
        Some(FunctionRef { value: value, _marker: PhantomData })//TODO not type safe
    }
}

impl <'b, A: 'static, B: 'static, R: 'static> VMType for FunctionRef<'b, (A, B), R> {
    type Type = fn (A, R) -> R;
}

impl <'a, A: 'static, B: 'static, R: 'static> Pushable<'a> for FunctionRef<'a, (A, B), R> {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(self.value);
        Status::Ok
    }
}
impl <'a, 'vm, A, B, R> Getable<'a, 'vm> for FunctionRef<'a, (A, B), R> {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<FunctionRef<'a, (A, B), R>> {
        Some(FunctionRef { value: value, _marker: PhantomData })//TODO not type safe
    }
}

impl <'a, 'b, A: Pushable<'b> + 'static, R: Getable<'b, 'a> + 'static> Callable<'a, 'b, (A,), R> {
    pub fn call(&mut self, a: A) -> Result<R, Error> {
        let mut stack = StackFrame::new_empty(self.vm);
        self.value.push(self.vm, &mut stack);
        a.push(self.vm, &mut stack);
        stack = try!(self.vm.execute(stack, &[Call(1)], &BytecodeFunction::empty()));
        match R::from_value(self.vm, stack.pop()) {
            Some(x) => Ok(x),
            None => Err(Error::Message("Wrong type".to_string()))
        }
    }
}
impl <'a, 'b, A: Pushable<'b> + 'static, B: Pushable<'b> + 'static, R: Getable<'b, 'a> + 'static> Callable<'a, 'b, (A, B), R> {
    pub fn call2(&mut self, a: A, b: B) -> Result<R, Error> {
        let mut stack = StackFrame::new_empty(self.vm);
        self.value.push(self.vm, &mut stack);
        a.push(self.vm, &mut stack);
        b.push(self.vm, &mut stack);
        stack = try!(self.vm.execute(stack, &[Call(2)], &BytecodeFunction::empty()));
        match R::from_value(self.vm, stack.pop()) {
            Some(x) => Ok(x),
            None => Err(Error::Message("Wrong type".to_string()))
        }
    }
}

pub fn get_function<'a, 'b, T: Get<'a, 'b>>(vm: &'a VM<'b>, name: &str) -> Option<T> {
    Get::get_function(vm, name)
}


pub trait VMFunction<'a, 'vm> {
    fn unpack_and_call(&self, vm: &'vm VM<'a>) -> Status;
}

impl <'a, 'vm, 's, T> VMFunction<'a, 'vm> for &'s T
where T: VMFunction<'a, 'vm> {
    fn unpack_and_call(&self, vm: &'vm VM<'a>) -> Status {
        (**self).unpack_and_call(vm)
    }
}

macro_rules! count {
    () => { 0 };
    ($_e: ident) => { 1 };
    ($_e: ident, $($rest: ident),*) => { 1 + count!($($rest),*) }
}

macro_rules! make_vm_function {
    ($($args:ident),*) => (
impl <$($args: VMType + 'static ,)* R: VMType + 'static> VMType for fn ($($args),*) -> R {
    #[allow(non_snake_case)]
    type Type = fn ($($args),*) -> R;
    #[allow(non_snake_case)]
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::function(args, make_type::<R>(vm))
    }
}

impl <'a, 'vm, $($args : Getable<'a, 'vm>,)* R: Pushable<'a>> VMFunction<'a, 'vm> for fn ($($args),*) -> R {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(&self, vm: &'vm VM<'a>) -> Status {
        let n_args = count!($($args),*) + R::extra_args();
        let mut stack = StackFrame::new(vm.stack.borrow_mut(), n_args, None);
        let mut i = 0;
        $(let $args = {
            let x = $args::from_value(vm, stack[i].clone()).expect(stringify!(Argument $args));
            i += 1;
            x
        });*;
        let r = (*self)($($args),*);
        r.push(vm, &mut stack)
    }
}
impl <'a, 's, $($args: VMType + 'static,)* R: VMType + 'static> VMType for Fn($($args),*) -> R + 's {
    type Type = fn ($($args),*) -> R;

    #[allow(non_snake_case)]
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::function(args, make_type::<R>(vm))
    }
}
impl <'a, 'vm, 's, $($args : Getable<'a, 'vm>,)* R: Pushable<'a>> VMFunction<'a, 'vm> for Fn($($args),*) -> R + 's {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(&self, vm: &'vm VM<'a>) -> Status {
        let n_args = count!($($args),*) + R::extra_args();
        let mut stack = StackFrame::new(vm.stack.borrow_mut(), n_args, None);
        let mut i = 0;
        $(let $args = {
            let x = $args::from_value(vm, stack[i].clone()).expect(stringify!(Argument $args));
            i += 1;
            x
        });*;
        let r = (*self)($($args),*);
        r.push(vm, &mut stack)
    }
}
impl <'a, 'vm, 's, $($args : Getable<'a, 'vm>,)* R: Pushable<'a>> VMFunction<'a, 'vm> for Box<Fn($($args),*) -> R + 's> {
    fn unpack_and_call(&self, vm: &'vm VM<'a>) -> Status {
        (**self).unpack_and_call(vm)
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


pub fn define_function<'a, 'vm, F>(vm: &VM<'a>, name: &str, f: F) -> VMResult<()>
where F: VMFunction<'a, 'vm> + VMType + 'static {
    let typ = make_type::<F>(vm);
    let args = {
        let mut iter = arg_iter(&typ);
        let args = iter.by_ref().count() as VMIndex;
        args + (match *iter.typ {
            ast::Type::Data(ast::TypeConstructor::Data(name), _) if name == "IO" => 1,
            _ => 0
        })
    };
    let f = Box::new(move |vm: &'vm VM<'a>| {
        f.unpack_and_call(vm)
    });
    unsafe {
        //The VM guarantess that it only ever calls this function with itself which should
        //make sure that ignoring the lifetime is safe
        let extern_fn = ::std::mem::transmute
                ::<Box<Fn(&'vm VM<'a>) -> Status + 'static>,
                   Box<Fn(&VM<'a>) -> Status + 'static>>(f);
        vm.extern_function_io(name, args, typ, extern_fn)
    }
}
#[cfg(test)]
mod tests {
    use super::{VMType, Get, Callable, define_function};

    use vm::{VM, VMInt, Value, Root, RootStr, load_script, run_expr};

    #[test]
    fn call_function() {
        let _ = ::env_logger::init();
        let add10 =
r"
let add10 : Int -> Int = \x -> x #Int+ 10 in add10
";
let mul = r"
let mul : Float -> Float -> Float = \x y -> x #Float* y in mul
";
        let mut vm = VM::new();
        load_script(&mut vm, "add10", &add10)
            .unwrap_or_else(|err| panic!("{}", err));
        load_script(&mut vm, "mul", &mul)
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
        let _ = ::env_logger::init();
        let s =
r"
let id : Test -> Test = \x -> x in id
";
        let mut vm = VM::new();
        fn test(test: *mut Test) -> bool {
            let test = unsafe { &mut *test };
            let x = test.x == 123;
            test.x *= 2;
            x
        }
        let test: fn (_) -> _ = test;
        impl VMType for Test { type Type = Test; }
        struct Test {
            x: VMInt
        }
        vm.register_type::<Test>("Test")
            .unwrap_or_else(|_| panic!("Could not add type"));
        define_function(&vm, "test", test)
            .unwrap_or_else(|err| panic!("{}", err));
        load_script(&mut vm, "id", &s)
            .unwrap_or_else(|err| panic!("{}", err));

        let mut test = Test { x: 123 };
        {
            let mut f: Callable<(*mut Test,), *mut Test> = Get::get_function(&vm, "id")
                .expect("No function id");
            let result = f.call(&mut test).unwrap();
            let p: *mut _ = &mut test;
            assert!(result == p);
        }
        let mut f: Callable<(*mut Test,), bool> = Get::get_function(&vm, "test")
            .expect("No function test");
        let result = f.call(&mut test).unwrap();
        assert!(result);
        assert_eq!(test.x, 123 * 2);
    }
    #[test]
    fn root_data() {
        let _ = ::env_logger::init();

        struct Test(VMInt);
        impl VMType for Test { type Type = Test; }

        let expr =
r#"
\x -> test x 1
"#;
        let vm = VM::new();
        fn test(r: Root<Test>, i: VMInt) -> VMInt {
            r.0 + i
        }
        vm.register_type::<Test>("Test")
            .unwrap_or_else(|_| panic!("Could not add type"));
        define_function(&vm, "test", { let test: fn (_, _) -> _ = test; test }).unwrap();
        load_script(&vm, "script_fn", expr)
            .unwrap_or_else(|err| panic!("{}", err));
        let mut script_fn: Callable<(Box<Test>,), VMInt> = Get::get_function(&vm, "script_fn")
            .expect("No function script_fn");
        let result = script_fn.call(Box::new(Test(123)))
            .unwrap();
        assert_eq!(result, 124);
    }
    #[test]
    fn root_string() {
        let _ = ::env_logger::init();
        let expr =
r#"
test "hello"
"#;
        let mut vm = VM::new();
        fn test(s: RootStr) -> String {
            let mut result = String::from(&s[..]);
            result.push_str(" world");
            result
        }
        define_function(&vm, "test", { let test: fn (_) -> _ = test; test }).unwrap();
        let result = run_expr(&mut vm, expr)
            .unwrap_or_else(|err| panic!("{}", err));
        match result {
            Value::String(s) => assert_eq!(&s[..], "hello world"),
            x => panic!("Expected string {:?}", x)
        }
    }
}
