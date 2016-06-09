use Variants;
use gc::{Gc, Traverseable, Move};
use base::symbol::Symbol;
use stack::{State, Stack, StackFrame};
use vm::{Thread, Status, DataStruct, ExternFunction, RootedValue, Value, Def, VMInt, Error, Root,
         RootStr};
use thread::RootedThread;
use base::types;
use base::types::{TcType, Type};
use types::{VMIndex, VMTag};
use std::any::Any;
use std::cell::Ref;
use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;

macro_rules! count {
    () => { 0 };
    ($_e: ident) => { 1 };
    ($_e: ident, $($rest: ident),*) => { 1 + count!($($rest),*) }
}

#[derive(Copy, Clone, PartialEq)]
pub enum ValueRef<'a> {
    Int(VMInt),
    Float(f64),
    String(&'a str),
    Data(Data<'a>),
    Userdata(&'a ::vm::Userdata),
    Internal,
}

impl<'a> ValueRef<'a> {
    pub fn new(value: &'a Value) -> ValueRef<'a> {
        match *value {
            Value::Int(i) => ValueRef::Int(i),
            Value::Float(f) => ValueRef::Float(f),
            Value::String(ref s) => ValueRef::String(s),
            Value::Data(ref data) => ValueRef::Data(Data(data)),
            Value::Userdata(ref data) => ValueRef::Userdata(&***data),
            Value::Thread(_) |
            Value::Function(_) |
            Value::Closure(_) |
            Value::PartialApplication(_) => ValueRef::Internal,
        }
    }
}

#[derive(Copy, Clone, PartialEq)]
pub struct Data<'a>(&'a DataStruct);

impl<'a> Data<'a> {
    pub fn tag(&self) -> VMTag {
        self.0.tag
    }

    pub fn len(&self) -> usize {
        self.0.fields.len()
    }

    pub fn get(&self, index: usize) -> Option<ValueRef<'a>> {
        self.0.fields.get(index).map(ValueRef::new)
    }
}

/// Type representing gluon's IO type#[derive(Debug)]
#[derive(Debug, PartialEq)]
pub enum IO<T> {
    Value(T),
    Exception(String),
}

pub struct Primitive<F> {
    name: &'static str,
    function: fn(&Thread) -> Status,
    _typ: PhantomData<F>,
}

pub fn primitive<F>(name: &'static str, function: fn(&Thread) -> Status) -> Primitive<F> {
    Primitive {
        name: name,
        function: function,
        _typ: PhantomData,
    }
}

#[derive(PartialEq)]
pub struct Generic<T>(pub Value, PhantomData<T>);

impl<T> fmt::Debug for Generic<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> From<Value> for Generic<T> {
    fn from(v: Value) -> Generic<T> {
        Generic(v, PhantomData)
    }
}

impl<T: VMType> VMType for Generic<T> {
    type Type = T::Type;

    fn make_type(vm: &Thread) -> TcType {
        T::make_type(vm)
    }

    fn extra_args() -> VMIndex {
        T::extra_args()
    }
}
impl<'vm, T: VMType> Pushable<'vm> for Generic<T> {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(self.0);
        Status::Ok
    }
}
impl<'vm, T> Getable<'vm> for Generic<T> {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<Generic<T>> {
        Some(Generic::from(*value.0))
    }
}

impl<T> Traverseable for Generic<T> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

/// Module containing types which represent generic variables in gluon's type system
pub mod generic {
    use super::VMType;
    use base::types::TcType;
    use vm::Thread;

    macro_rules! make_generics {
        ($($i: ident)+) => {
            $(
            #[derive(Clone, Copy, PartialEq)]
            pub enum $i { }
            impl VMType for $i {
                type Type = $i;
                fn make_type(vm: &Thread) -> TcType {
                    let s = stringify!($i);
                    let lower  = [s.as_bytes()[0] + 32];
                    let lower_str = unsafe { ::std::str::from_utf8_unchecked(&lower) };
                    vm.get_generic(lower_str)
                }
            }
            )+
        }
    }
    make_generics!{A B C D E F G H I J K L M N O P Q R X Y Z}
}

/// Trait which maps a type in rust to a type in gluon
pub trait VMType {
    /// A version of `Self` which implements `Any` allowing a `TypeId` to be retrieved
    type Type: ?Sized + Any;

    /// Creates an gluon type which maps to `Self` in rust
    fn make_type(vm: &Thread) -> TcType {
        vm.get_type::<Self::Type>()
    }

    /// How many extra arguments a function returning this type requires.
    /// Used for abstract types which when used in return position should act like they still need
    /// more arguments before they are called
    fn extra_args() -> VMIndex {
        0
    }
}


/// Trait which allows a rust value to be pushed to the virtual machine
pub trait Pushable<'vm>: VMType {
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status;
}

/// Trait which allows rust values to be retrieved from the virtual machine
pub trait Getable<'vm>: Sized {
    /// unsafe version of from_value which allows references to the internal of GcPtr's to be
    /// extracted if `value` is rooted
    unsafe fn from_value_unsafe(vm: &'vm Thread, value: Variants) -> Option<Self> {
        Self::from_value(vm, value)
    }
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<Self>;
}

impl<'vm> Getable<'vm> for Value {
    fn from_value(_vm: &'vm Thread, value: Variants) -> Option<Self> {
        Some(*value.0)
    }
}

impl<'vm, T: ?Sized + VMType> VMType for &'vm T {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> TcType {
        T::make_type(vm)
    }
}

impl<'vm, T> Getable<'vm> for &'vm T
    where T: ::vm::Userdata
{
    unsafe fn from_value_unsafe(vm: &'vm Thread, value: Variants) -> Option<Self> {
        <*const T as Getable<'vm>>::from_value(vm, value).map(|p| &*p)
    }
    // Only allow the unsafe version to be used
    fn from_value(_vm: &'vm Thread, _value: Variants) -> Option<Self> {
        None
    }
}

unsafe fn forget_lifetime<'a, 'b, T: ?Sized>(x: &'a T) -> &'b T {
    ::std::mem::transmute(x)
}

impl<'vm> Getable<'vm> for &'vm str {
    fn from_value(_vm: &'vm Thread, value: Variants) -> Option<Self> {
        unsafe {
            match value.as_ref() {
                ValueRef::String(ref s) => Some(forget_lifetime(s)),
                _ => None,
            }
        }
    }
}

/// Wrapper type which passes acts as the type `T` but also passes the `VM` to the called function
pub struct WithVM<'vm, T> {
    pub vm: &'vm Thread,
    pub value: T,
}

impl<'vm, T> VMType for WithVM<'vm, T>
    where T: VMType
{
    type Type = T::Type;

    fn make_type(vm: &Thread) -> TcType {
        T::make_type(vm)
    }

    fn extra_args() -> VMIndex {
        T::extra_args()
    }
}

impl<'vm, T> Pushable<'vm> for WithVM<'vm, T>
    where T: Pushable<'vm>
{
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        self.value.push(vm, stack)
    }
}

impl<'vm, T> Getable<'vm> for WithVM<'vm, T>
    where T: Getable<'vm>
{
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<WithVM<'vm, T>> {
        T::from_value(vm, value).map(|t| WithVM { vm: vm, value: t })
    }
}

impl VMType for () {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for () {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Int(0));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for () {
    fn from_value(_: &'vm Thread, _: Variants) -> Option<()> {
        Some(())
    }
}

impl VMType for i32 {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for i32 {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Int(self as VMInt));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for i32 {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<i32> {
        match value.as_ref() {
            ValueRef::Int(i) => Some(i as i32),
            _ => None,
        }
    }
}
impl VMType for u32 {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for u32 {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Int(self as VMInt));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for u32 {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<u32> {
        match value.as_ref() {
            ValueRef::Int(i) => Some(i as u32),
            _ => None,
        }
    }
}
impl VMType for usize {
    type Type = VMInt;
}
impl<'vm> Pushable<'vm> for usize {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Int(self as VMInt));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for usize {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<usize> {
        match value.as_ref() {
            ValueRef::Int(i) => Some(i as usize),
            _ => None,
        }
    }
}
impl VMType for VMInt {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for VMInt {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Int(self));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for VMInt {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<VMInt> {
        match value.as_ref() {
            ValueRef::Int(i) => Some(i),
            _ => None,
        }
    }
}
impl VMType for f64 {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for f64 {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Float(self));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for f64 {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<f64> {
        match value.as_ref() {
            ValueRef::Float(f) => Some(f),
            _ => None,
        }
    }
}
impl VMType for bool {
    type Type = Self;
    fn make_type(vm: &Thread) -> TcType {
        (*vm.get_env().find_type_info("std.types.Bool").unwrap()).clone().into_type()
    }
}
impl<'vm> Pushable<'vm> for bool {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Int(if self {
            1
        } else {
            0
        }));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for bool {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<bool> {
        match value.as_ref() {
            ValueRef::Int(1) => Some(true),
            ValueRef::Int(0) => Some(false),
            _ => None,
        }
    }
}

impl VMType for Ordering {
    type Type = Self;
    fn make_type(vm: &Thread) -> TcType {
        let symbol = vm.find_type_info("std.types.Ordering").unwrap().name.clone();
        Type::data(Type::id(symbol), vec![])
    }
}
impl<'vm> Pushable<'vm> for Ordering {
    fn push(self, _vm: &'vm Thread, stack: &mut Stack) -> Status {
        let tag = match self {
            Ordering::Less => 0,
            Ordering::Equal => 1,
            Ordering::Greater => 2,
        };
        stack.push(Value::Int(tag));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for Ordering {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<Ordering> {
        let tag = match value.as_ref() {
            ValueRef::Data(data) => data.tag() as VMInt,
            ValueRef::Int(tag) => tag,
            _ => return None,
        };
        match tag {
            0 => Some(Ordering::Less),
            1 => Some(Ordering::Equal),
            2 => Some(Ordering::Greater),
            _ => None,
        }
    }
}

impl VMType for str {
    type Type = <String as VMType>::Type;
}
impl VMType for String {
    type Type = String;
}
impl<'vm, 's> Pushable<'vm> for &'s String {
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        <&str as Pushable>::push(self, vm, stack)
    }
}
impl<'vm, 's> Pushable<'vm> for &'s str {
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        let s = vm.alloc(stack, self);
        stack.push(Value::String(s));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for String {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<String> {
        match value.as_ref() {
            ValueRef::String(i) => Some(String::from(&i[..])),
            _ => None,
        }
    }
}
impl<'vm> Pushable<'vm> for String {
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        <&str as Pushable>::push(&self, vm, stack)
    }
}

impl VMType for char {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for char {
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Int(self as VMInt));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for char {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<char> {
        match value.as_ref() {
            ValueRef::Int(x) => ::std::char::from_u32(x as u32),
            _ => None,
        }
    }
}

impl<'s, T: VMType> VMType for Ref<'s, T> {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> TcType {
        T::make_type(vm)
    }
}

impl<'s, 'vm, T> Pushable<'vm> for Ref<'s, T>
    where for<'t> &'t T: Pushable<'vm>,
          T: VMType
{
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        <&T as Pushable>::push(&*self, vm, stack)
    }
}

impl<T> VMType for Vec<T>
    where T: VMType,
          T::Type: Sized
{
    type Type = Vec<T::Type>;
}

impl<'vm, T> Pushable<'vm> for Vec<T>
    where T: Pushable<'vm>,
          T::Type: Sized
{
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        let len = self.len() as VMIndex;
        for v in self {
            if v.push(vm, stack) == Status::Error {
                return Status::Error;
            }
        }
        let result = {
            let values = &stack[stack.len() - len..];
            vm.alloc(stack,
                     Def {
                         tag: 0,
                         elems: values,
                     })
        };
        for _ in 0..len {
            stack.pop();
        }
        stack.push(Value::Data(result));
        Status::Ok
    }
}

pub struct Userdata<T>(pub T);

impl<T: VMType> VMType for Userdata<T> {
    type Type = T::Type;
}
impl<'vm, T: ::vm::Userdata + VMType> Pushable<'vm> for Userdata<T> {
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        let data: Box<::vm::Userdata> = Box::new(self.0);
        let userdata = vm.alloc(stack, Move(data));
        stack.push(Value::Userdata(userdata));
        Status::Ok
    }
}
impl<'vm, T: Clone + ::vm::Userdata> Getable<'vm> for Userdata<T> {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<Userdata<T>> {
        match value.as_ref() {
            ValueRef::Userdata(data) => data.downcast_ref::<T>().map(|x| Userdata(x.clone())),
            _ => None,
        }
    }
}

impl<'s, T: VMType> VMType for *const T {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> TcType {
        T::make_type(vm)
    }
}

impl<'vm, T: ::vm::Userdata> Getable<'vm> for *const T {
    fn from_value(_: &'vm Thread, value: Variants) -> Option<*const T> {
        match value.as_ref() {
            ValueRef::Userdata(data) => data.downcast_ref::<T>().map(|x| x as *const T),
            _ => None,
        }
    }
}

impl<T: VMType> VMType for Option<T>
    where T::Type: Sized
{
    type Type = Option<T::Type>;
    fn make_type(vm: &Thread) -> TcType {
        let symbol = vm.find_type_info("std.types.Option").unwrap().name.clone();
        Type::data(Type::id(symbol), vec![T::make_type(vm)])
    }
}
impl<'vm, T: Pushable<'vm>> Pushable<'vm> for Option<T>
    where T::Type: Sized
{
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        match self {
            Some(value) => {
                let len = stack.len();
                value.push(vm, stack);
                let value = vm.new_data(1, &[stack.pop()]);
                assert!(stack.len() == len);
                stack.push(value);
            }
            None => stack.push(Value::Int(0)),
        }
        Status::Ok
    }
}
impl<'vm, T: Getable<'vm>> Getable<'vm> for Option<T> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<Option<T>> {
        match *value.0 {
            Value::Data(data) => {
                if data.tag == 0 {
                    Some(None)
                } else {
                    T::from_value(vm, Variants(&data.fields[1])).map(Some)
                }
            }
            Value::Int(0) => Some(None),
            _ => None,
        }
    }
}

impl<T: VMType, E: VMType> VMType for Result<T, E>
    where T::Type: Sized,
          E::Type: Sized
{
    type Type = Result<T::Type, E::Type>;
    fn make_type(vm: &Thread) -> TcType {
        let symbol = vm.find_type_info("std.types.Result").unwrap().name.clone();
        Type::data(Type::id(symbol), vec![E::make_type(vm), T::make_type(vm)])
    }
}

impl<'vm, T: Pushable<'vm>, E: Pushable<'vm>> Pushable<'vm> for Result<T, E>
    where T::Type: Sized,
          E::Type: Sized
{
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        let tag = match self {
            Ok(ok) => {
                ok.push(vm, stack);
                1
            }
            Err(err) => {
                err.push(vm, stack);
                0
            }
        };
        let value = stack.pop();
        let data = vm.alloc(stack,
                            Def {
                                tag: tag,
                                elems: &[value],
                            });
        stack.push(Value::Data(data));
        Status::Ok
    }
}

impl<'vm, T: Getable<'vm>, E: Getable<'vm>> Getable<'vm> for Result<T, E> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<Result<T, E>> {
        match *value.0 {
            Value::Data(data) => {
                match data.tag {
                    0 => E::from_value(vm, Variants(&data.fields[0])).map(Err),
                    1 => T::from_value(vm, Variants(&data.fields[0])).map(Ok),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

pub enum MaybeError<T, E> {
    Ok(T),
    Err(E),
}

impl<T: VMType, E> VMType for MaybeError<T, E> {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> TcType {
        T::make_type(vm)
    }
}
impl<'vm, T: Pushable<'vm>, E: fmt::Display> Pushable<'vm> for MaybeError<T, E> {
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        match self {
            MaybeError::Ok(value) => {
                value.push(vm, stack);
                Status::Ok
            }
            MaybeError::Err(err) => {
                let msg = format!("{}", err);
                let s = vm.alloc(stack, &msg[..]);
                stack.push(Value::String(s));
                Status::Error
            }
        }
    }
}

impl<T> VMType for IO<T>
    where T: VMType,
          T::Type: Sized
{
    type Type = IO<T::Type>;
    fn make_type(vm: &Thread) -> TcType {
        let env = vm.get_env();
        let symbol = env.find_type_info("IO").unwrap().name.clone();
        Type::data(Type::id(symbol), vec![T::make_type(vm)])
    }
    fn extra_args() -> VMIndex {
        1
    }
}

impl<'vm, T: Getable<'vm>> Getable<'vm> for IO<T> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<IO<T>> {
        T::from_value(vm, value).map(IO::Value)
    }
}

impl<'vm, T: Pushable<'vm>> Pushable<'vm> for IO<T>
    where T::Type: Sized
{
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        match self {
            IO::Value(value) => {
                value.push(vm, stack);
                Status::Ok
            }
            IO::Exception(exc) => {
                exc.push(vm, stack);
                Status::Error
            }
        }
    }
}

/// Type which represents an array in gluon
/// Type implementing both `Pushable` and `Getable` of values of `V`.
/// The actual value, `V` is not accessible directly but is only intended to be transferred between
/// two different threads.
pub struct OpaqueValue<T, V>(RootedValue<T>, PhantomData<V>) where T: Deref<Target = Thread>;

impl<T, V> VMType for OpaqueValue<T, V>
    where T: Deref<Target = Thread>,
          V: VMType,
          V::Type: Sized
{
    type Type = V::Type;
    fn make_type(vm: &Thread) -> TcType {
        V::make_type(vm)
    }
}

impl<'vm, T, V> Pushable<'vm> for OpaqueValue<T, V>
    where T: Deref<Target = Thread>,
          V: VMType,
          V::Type: Sized
{
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(*self.0);
        Status::Ok
    }
}

impl<'vm, V> Getable<'vm> for OpaqueValue<&'vm Thread, V> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<OpaqueValue<&'vm Thread, V>> {
        Some(OpaqueValue(vm.root_value_ref(*value.0), PhantomData))
    }
}

impl<'vm, V> Getable<'vm> for OpaqueValue<RootedThread, V> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<OpaqueValue<RootedThread, V>> {
        Some(OpaqueValue(vm.root_value(*value.0), PhantomData))
    }
}


/// Type which represents an array in embed_lang
pub struct Array<'vm, T>(RootedValue<&'vm Thread>, PhantomData<T>);

impl<'vm, T> Deref for Array<'vm, T> {
    type Target = DataStruct;
    fn deref(&self) -> &DataStruct {
        match *self.0 {
            Value::Data(ref data) => data,
            _ => panic!("Expected data"),
        }
    }
}

impl<'vm, T> Array<'vm, T> {
    pub fn vm(&self) -> &'vm Thread {
        self.0.vm_()
    }

    pub fn len(&self) -> VMIndex {
        self.fields.len() as VMIndex
    }
}

impl<'vm, T: for<'vm2> Getable<'vm2>> Array<'vm, T> {
    pub fn get(&self, index: VMInt) -> Option<T> {
        match *self.0 {
            Value::Data(data) => {
                data.fields
                    .get(index as usize)
                    .and_then(|v| T::from_value(self.0.vm(), Variants(v)))
            }
            _ => None,
        }
    }
}

impl<'vm, T: VMType> VMType for Array<'vm, T>
    where T::Type: Sized
{
    type Type = Array<'static, T::Type>;
    fn make_type(vm: &Thread) -> TcType {
        Type::array(T::make_type(vm))
    }
}


impl<'vm, T: VMType> Pushable<'vm> for Array<'vm, T>
    where T::Type: Sized
{
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(*self.0);
        Status::Ok
    }
}

impl<'vm, T> Getable<'vm> for Array<'vm, T> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<Array<'vm, T>> {
        Some(Array(vm.root_value_ref(*value.0), PhantomData))
    }
}

impl<'vm, T: Any> VMType for Root<'vm, T> {
    type Type = T;
}
impl<'vm, T: ::vm::Userdata> Getable<'vm> for Root<'vm, T> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<Root<'vm, T>> {
        match *value.0 {
            Value::Userdata(data) => vm.root::<T>(data).map(From::from),
            _ => None,
        }
    }
}

impl<'vm> VMType for RootStr<'vm> {
    type Type = <str as VMType>::Type;
}
impl<'vm> Getable<'vm> for RootStr<'vm> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<RootStr<'vm>> {
        match *value.0 {
            Value::String(v) => Some(vm.root_string(v)),
            _ => None,
        }
    }
}

macro_rules! define_tuple {
    ($($id: ident)+) => {
        impl<$($id),+> VMType for ($($id),+)
        where $($id: VMType),+,
              $($id::Type: Sized),+
        {
            type Type = ($($id::Type),+);

            fn make_type(vm: &Thread) -> TcType {
                let fields = vec![$(
                    types::Field {
                        name: Symbol::new(stringify!($id)),
                        typ: $id::make_type(vm),
                    }
                ),+];
                Type::record(Vec::new(), fields)
            }
        }
        impl<'vm, $($id: Getable<'vm>),+> Getable<'vm> for ($($id),+) {
            #[allow(unused_assignments)]
            fn from_value(vm: &'vm Thread, value: Variants) -> Option<($($id),+)> {
                match value.as_ref() {
                    ValueRef::Data(v) => {
                        let mut i = 0;
                        let x = ( $(
                            { let a = $id::from_value(vm, Variants(&v.0.fields[i])); i += 1; a }
                        ),+ );
                        match x {
                            ($(Some($id)),+) => Some(( $($id),+ )),
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
        }
        impl<'vm, $($id),+> Pushable<'vm> for ($($id),+)
        where $($id: Pushable<'vm>),+,
              $($id::Type: Sized),+
        {
            fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
                let ( $($id),+ ) = self;
                $(
                    $id.push(vm, stack);
                )+
                let len = count!($($id),+);
                let offset = stack.len() - len;
                let value = vm.new_data(0, &stack[offset..]);
                for _ in 0..len {
                    stack.pop();
                }
                stack.push(value);
                Status::Ok
            }
        }
    }
}

macro_rules! define_tuples {
    ($first: ident) => { };
    ($first: ident $($rest: ident)+) => {
        define_tuple!{ $first $($rest)+ }
        define_tuples!{ $($rest)+ }
    }
}
define_tuples! { _0 _1 _2 _3 _4 _5 _6 }


pub use self::record::Record;

pub mod record {
    use base::types;
    use base::types::{Type, TcType};
    use base::symbol::Symbol;

    use Variants;
    use stack::Stack;
    use types::VMIndex;
    use vm::{Thread, Status, Value};
    use super::{VMType, Getable, Pushable};

    pub struct Record<T> {
        pub fields: T,
    }

    impl<FA, A, FB, B> Record<HList<(FA, A), HList<(FB, B), ()>>> {
        pub fn split(self) -> (A, B) {
            let Record { fields: HList((_, a), HList((_, b), ())) } = self;
            (a, b)
        }
    }

    pub struct HList<H, T>(pub H, pub T);

    pub trait Field: Default {
        fn name() -> &'static str;
    }

    pub trait FieldList {
        fn len() -> VMIndex;

        fn field_types(vm: &Thread, fields: &mut Vec<types::Field<Symbol, TcType>>);
    }

    impl FieldList for () {
        fn len() -> VMIndex {
            0
        }

        fn field_types(_: &Thread, _: &mut Vec<types::Field<Symbol, TcType>>) {}
    }

    impl<F: Field, H: VMType, T> FieldList for HList<(F, H), T>
        where T: FieldList
{
        fn len() -> VMIndex {
            1 + T::len()
        }

        fn field_types(vm: &Thread, fields: &mut Vec<types::Field<Symbol, TcType>>) {
            fields.push(types::Field {
                name: Symbol::new(F::name()),
                typ: H::make_type(vm),
            });
            T::field_types(vm, fields);
        }
    }

    pub trait PushableFieldList<'vm>: FieldList {
        fn push(self, vm: &'vm Thread, fields: &mut Stack);
    }

    impl<'vm> PushableFieldList<'vm> for () {
        fn push(self, _: &'vm Thread, _: &mut Stack) {}
    }

    impl<'vm, F: Field, H: Pushable<'vm>, T> PushableFieldList<'vm> for HList<(F, H), T>
        where T: PushableFieldList<'vm>
{
        fn push(self, vm: &'vm Thread, fields: &mut Stack) {
            let HList((_, head), tail) = self;
            head.push(vm, fields);
            tail.push(vm, fields);
        }
    }

    pub trait GetableFieldList<'vm>: FieldList + Sized {
        fn from_value(vm: &'vm Thread, values: &[Value]) -> Option<Self>;
    }

    impl<'vm> GetableFieldList<'vm> for () {
        fn from_value(_vm: &'vm Thread, values: &[Value]) -> Option<Self> {
            debug_assert!(values.is_empty());
            Some(())
        }
    }
    impl<'vm, F, H, T> GetableFieldList<'vm> for HList<(F, H), T>
        where F: Field,
              H: Getable<'vm> + VMType,
              T: GetableFieldList<'vm>
{
        fn from_value(vm: &'vm Thread, values: &[Value]) -> Option<Self> {
            let head = unsafe { H::from_value(vm, Variants::new(&values[0])) };
            head.and_then(|head| {
                T::from_value(vm, &values[1..]).map(move |tail| HList((F::default(), head), tail))
            })
        }
    }

    impl<A: VMType, F: Field, T: FieldList> VMType for Record<HList<(F, A), T>>
        where A::Type: Sized
{
        type Type = Record<((&'static str, A::Type),)>;
        fn make_type(vm: &Thread) -> TcType {
            let len = HList::<(F, A), T>::len() as usize;
            let mut fields = Vec::with_capacity(len);
            HList::<(F, A), T>::field_types(vm, &mut fields);
            Type::record(Vec::new(), fields)
        }
    }
    impl<'vm, A, F, T> Pushable<'vm> for Record<HList<(F, A), T>>
        where A: Pushable<'vm>,
              F: Field,
              T: PushableFieldList<'vm>,
              A::Type: Sized
{
        fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
            self.fields.push(vm, stack);
            let len = HList::<(F, A), T>::len();
            let offset = stack.len() - len;
            let value = vm.new_data(0, &stack[offset..]);
            for _ in 0..len {
                stack.pop();
            }
            stack.push(value);
            Status::Ok
        }
    }
    impl<'vm, A, F, T> Getable<'vm> for Record<HList<(F, A), T>>
        where A: Getable<'vm> + VMType,
              F: Field,
              T: GetableFieldList<'vm>
{
        fn from_value(vm: &'vm Thread, value: Variants) -> Option<Self> {
            match *value.0 {
                Value::Data(ref data) => {
                    HList::<(F, A), T>::from_value(vm, &data.fields)
                        .map(|fields| Record { fields: fields })
                }
                _ => None,
            }
        }
    }
}

#[macro_export]
macro_rules! types {
    ($($field: ident),*) => {
        $(
        #[allow(non_camel_case_types)]
        #[derive(Default)]
        pub struct $field;
        impl $crate::api::record::Field for $field {
            fn name() -> &'static str {
                stringify!($field)
            }
        }
        )*
    }
}

#[macro_export]
macro_rules! hlist {
    () => { () };
    ($field: ident => $value: expr) => {
        $crate::api::record::HList((_field::$field, $value), ())
    };
    ($field: ident => $value: expr, $($field_tail: ident => $value_tail: expr),*) => {
        $crate::api::record::HList((_field::$field, $value),
                                   hlist!($($field_tail => $value_tail),*))
    }
}

#[macro_export]
macro_rules! field_decl {
    ($($field: ident),*) => {
        mod _field { types!($($field),*); }
    }
}

#[macro_export]
macro_rules! record_no_decl {
    ($($field: ident => $value: expr),*) => {
        {
            $crate::api::Record {
                fields: hlist!($($field => $value),*)
            }
        }
    }
}

#[macro_export]
macro_rules! record {
    ($($field: ident => $value: expr),*) => {
        {
            field_decl!($($field),*);
            record_no_decl!($($field => $value),*)
        }
    }
}

impl<F: VMType> VMType for Primitive<F> {
    type Type = F::Type;
    fn make_type(vm: &Thread) -> TcType {
        F::make_type(vm)
    }
}

impl<'vm, F> Pushable<'vm> for Primitive<F>
    where F: FunctionType + VMType + Send + Sync
{
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        use std::mem::transmute;
        let extern_function = unsafe {
            // The VM guarantess that it only ever calls this function with itself which should
            // make sure that ignoring the lifetime is safe
            transmute::<Box<Fn(&'vm Thread) -> Status + Send + Sync>,
                        Box<Fn(&Thread) -> Status + Send + Sync>>(Box::new(self.function))
        };
        let id = Symbol::new(self.name);
        let value = Value::Function(vm.alloc(stack,
                                             Move(ExternFunction {
                                                 id: id,
                                                 args: F::arguments(),
                                                 function: extern_function,
                                             })));
        stack.push(value);
        Status::Ok
    }
}

fn make_type<T: ?Sized + VMType>(vm: &Thread) -> TcType {
    <T as VMType>::make_type(vm)
}

/// Type which represents a function reference in gluon
pub type FunctionRef<'vm, F> = Function<&'vm Thread, F>;

/// Type which represents an function in gluon
pub struct Function<T, F>
    where T: Deref<Target = Thread>
{
    value: RootedValue<T>,
    _marker: PhantomData<F>,
}

impl<T, F> Function<T, F>
    where T: Deref<Target = Thread>
{
    pub fn value(&self) -> Value {
        *self.value
    }
}

impl<T, F> VMType for Function<T, F>
    where T: Deref<Target = Thread>,
          F: VMType
{
    type Type = F::Type;
    fn make_type(vm: &Thread) -> TcType {
        F::make_type(vm)
    }
}

impl<'vm, T, F: Any> Pushable<'vm> for Function<T, F>
    where T: Deref<Target = Thread>,
          F: VMType
{
    fn push(self, _: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(*self.value);
        Status::Ok
    }
}
impl<'vm, F> Getable<'vm> for Function<&'vm Thread, F> {
    fn from_value(vm: &'vm Thread, value: Variants) -> Option<Function<&'vm Thread, F>> {
        Some(Function {
            value: vm.root_value_ref(*value.0),
            _marker: PhantomData,
        })//TODO not type safe
    }
}

/// Trait which represents a function
pub trait FunctionType {
    /// Returns how many arguments the function needs to be provided to call it
    fn arguments() -> VMIndex;
}

/// Trait which abstracts over types which can be called by being pulling the arguments it needs
/// from the virtual machine's stack
pub trait VMFunction<'vm> {
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status;
}

impl<'s, T: FunctionType> FunctionType for &'s T {
    fn arguments() -> VMIndex {
        T::arguments()
    }
}

impl<'vm, 's, T: ?Sized> VMFunction<'vm> for &'s T
    where T: VMFunction<'vm>
{
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status {
        (**self).unpack_and_call(vm)
    }
}

impl<F> FunctionType for Box<F>
    where F: FunctionType
{
    fn arguments() -> VMIndex {
        F::arguments()
    }
}

impl<'vm, F: ?Sized> VMFunction<'vm> for Box<F>
    where F: VMFunction<'vm>
{
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status {
        (**self).unpack_and_call(vm)
    }
}

macro_rules! make_vm_function {
    ($($args:ident),*) => (
impl <$($args: VMType,)* R: VMType> VMType for fn ($($args),*) -> R {
    #[allow(non_snake_case)]
    type Type = fn ($($args::Type),*) -> R::Type;
    #[allow(non_snake_case)]
    fn make_type(vm: &Thread) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::function(args, make_type::<R>(vm))
    }
}

impl <'vm, $($args,)* R> Pushable<'vm> for fn ($($args),*) -> R
where $($args: Getable<'vm> + VMType + 'vm,)* R: Pushable<'vm> + 'vm {
    fn push(self, vm: &'vm Thread, stack: &mut Stack) -> Status {
        let f = Box::new(move |vm| self.unpack_and_call(vm));
        let extern_function = unsafe {
            //The VM guarantess that it only ever calls this function with itself which should
            //make sure that ignoring the lifetime is safe
            ::std::mem::transmute
                    ::<Box<Fn(&'vm Thread) -> Status + Send + Sync>,
                       Box<Fn(&Thread) -> Status + Send + Sync>>(f)
        };
        let id = Symbol::new("<extern>");
        let value = Value::Function(vm.alloc(stack, Move(
            ExternFunction {
                id: id,
                args: count!($($args),*) + R::extra_args(),
                function: extern_function
            })));
        stack.push(value);
        Status::Ok
    }
}

impl <'vm, $($args,)* R: VMType> FunctionType for fn ($($args),*) -> R {
    fn arguments() -> VMIndex {
        count!($($args),*) + R::extra_args()
    }
}

impl <'vm, $($args,)* R> VMFunction<'vm> for fn ($($args),*) -> R
where $($args: Getable<'vm> + 'vm,)* R: Pushable<'vm> + 'vm {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables, unused_unsafe)]
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status {
        let n_args = Self::arguments();
        let mut stack = vm.current_frame();
        let mut i = 0;
        let r = unsafe {
            $(let $args = {
                let x = $args::from_value_unsafe(vm, Variants(&stack[i]))
                    .expect(stringify!(Argument $args));
                i += 1;
                x
            });*;
            // Lock the frame to ensure that any reference from_value_unsafe may have returned stay
            // rooted
            let lock = stack.into_lock();
            let r = (*self)($($args),*);
            vm.release_lock(lock);
            stack = vm.current_frame();
            r
        };
        r.push(vm, &mut stack.stack)
    }
}

impl <'s, $($args,)* R: VMType> FunctionType for Fn($($args),*) -> R + 's {
    fn arguments() -> VMIndex {
        count!($($args),*) + R::extra_args()
    }
}

impl <'s, $($args: VMType,)* R: VMType> VMType for Fn($($args),*) -> R + 's {
    type Type = fn ($($args::Type),*) -> R::Type;

    #[allow(non_snake_case)]
    fn make_type(vm: &Thread) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::function(args, make_type::<R>(vm))
    }
}

impl <'vm, $($args,)* R> VMFunction<'vm> for Fn($($args),*) -> R + 'vm
where $($args: Getable<'vm> + 'vm,)* R: Pushable<'vm> + 'vm {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables, unused_unsafe)]
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status {
        let n_args = Self::arguments();
        let mut stack = vm.current_frame();
        let mut i = 0;
        let r = unsafe {
            $(let $args = {
                let x = $args::from_value_unsafe(vm, Variants(&stack[i]))
                    .expect(stringify!(Argument $args));
                i += 1;
                x
            });*;
            // Lock the frame to ensure that any reference from_value_unsafe may have returned stay
            // rooted
            let lock = stack.into_lock();
            let r = (*self)($($args),*);
            vm.release_lock(lock);
            stack = vm.current_frame();
            r
        };
        r.push(vm, &mut stack.stack)
    }
}

impl<'vm, T, $($args,)* R> Function<T, fn($($args),*) -> R>
    where $($args: Pushable<'vm>,)*
          T: Deref<Target = Thread>,
          R: VMType + Getable<'vm>
{
    #[allow(non_snake_case)]
    pub fn call(&'vm mut self $(, $args: $args)*) -> Result<R, Error> {
        let vm = self.value.vm();
        let mut stack = vm.get_stack();
        StackFrame::current(stack).enter_scope(0, State::Unknown);
        stack = vm.get_stack();
        stack.push(*self.value);
        $(
            $args.push(vm, &mut stack);
        )*
        for _ in 0..R::extra_args() {
            0.push(vm, &mut stack);
        }
        let args = stack.len() - 1;
        let mut stack = try!(vm.call_function(StackFrame::current(stack), args)).unwrap();
        let result = stack.pop();
        R::from_value(vm, Variants(&result))
            .ok_or_else(|| {
                error!("Wrong type {:?}", result);
                Error::Message("Wrong type".to_string())
            })
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
        fn wrapper<'b, 'c>(vm: &Thread) {
            $func.unpack_and_call(vm)
        }
        wrapper
    })
}
