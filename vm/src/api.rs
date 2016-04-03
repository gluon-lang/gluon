use gc::{Gc, Traverseable, Move};
use base::symbol::Symbol;
use stack::StackFrame;
use vm::{VM, Thread, Status, DataStruct, ExternFunction, RootedValue, Value, Def, Userdata_,
         VMInt, Error, Root, RootStr};
use base::types;
use base::types::{TcType, Type, TypeConstructor};
use types::VMIndex;
use std::any::Any;
use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;

/// Type representing embed_lang's IO type#[derive(Debug)]
pub enum IO<T> {
    Value(T),
    Exception(String),
}

pub struct Primitive<F> {
    name: &'static str,
    function: fn(&VM) -> Status,
    _typ: PhantomData<F>,
}

pub fn primitive<F>(name: &'static str, function: fn(&VM) -> Status) -> Primitive<F> {
    Primitive {
        name: name,
        function: function,
        _typ: PhantomData,
    }
}

#[derive(Clone, Copy)]
pub struct Generic<T>(pub Value, PhantomData<T>);

impl<T> From<Value> for Generic<T> {
    fn from(v: Value) -> Generic<T> {
        Generic(v, PhantomData)
    }
}

impl<T: VMType> VMType for Generic<T> {
    type Type = T::Type;

    fn make_type(vm: &VM) -> TcType {
        T::make_type(vm)
    }

    fn extra_args() -> VMIndex {
        T::extra_args()
    }
}
impl<T: VMType> Pushable for Generic<T> {
    fn push<'b>(self, _: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(self.0);
        Status::Ok
    }
}
impl<'vm, T> Getable<'vm> for Generic<T> {
    fn from_value(_: &'vm VM, value: Value) -> Option<Generic<T>> {
        Some(Generic::from(value))
    }
}

impl<T> Traverseable for Generic<T> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

/// Module containing types which represent generic variables in embed_lang's type system
pub mod generic {
    use super::VMType;
    use base::types::TcType;
    use vm::VM;

    macro_rules! make_generics {
        ($($i: ident)+) => {
            $(
            #[derive(Clone, Copy)]
            pub enum $i { }
            impl VMType for $i {
                type Type = $i;
                fn make_type(vm: &VM) -> TcType {
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

/// Trait which maps a type in rust to a type in embed_lang
pub trait VMType {
    /// A version of `Self` which implements `Any` allowing a `TypeId` to be retrieved
    type Type: ?Sized + Any;

    /// Creates an embed_lang type which maps to `Self` in rust
    fn make_type(vm: &VM) -> TcType {
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
pub trait Pushable : VMType {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status;
}

/// Trait which allows rust values to be retrieved from the virtual machine
pub trait Getable<'vm>: Sized {
    fn from_value(vm: &'vm VM, value: Value) -> Option<Self>;
}

/// Wrapper type which passes acts as the type `T` but also passes the `VM` to the called function
pub struct WithVM<'vm, T> {
    pub vm: &'vm VM,
    pub value: T,
}

impl<'vm, T> VMType for WithVM<'vm, T>
    where T: VMType
{
    type Type = T::Type;

    fn make_type(vm: &VM) -> TcType {
        T::make_type(vm)
    }

    fn extra_args() -> VMIndex {
        T::extra_args()
    }
}

impl<'vm, T> Pushable for WithVM<'vm, T>
    where T: Pushable
{
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        self.value.push(vm, stack)
    }
}

impl<'vm, T> Getable<'vm> for WithVM<'vm, T>
    where T: Getable<'vm>
{
    fn from_value(vm: &'vm VM, value: Value) -> Option<WithVM<'vm, T>> {
        T::from_value(vm, value).map(|t| WithVM { vm: vm, value: t })
    }
}

impl VMType for Thread {
    type Type = Thread;
}

impl Pushable for Thread {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        let value = Value::Thread(vm.alloc(&stack.stack, Move(self)));
        stack.push(value);
        Status::Ok
    }
}

impl VMType for () {
    type Type = Self;
}
impl Pushable for () {
    fn push<'b>(self, _: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(Value::Int(0));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for () {
    fn from_value(_: &'vm VM, _: Value) -> Option<()> {
        Some(())
    }
}

impl VMType for VMInt {
    type Type = Self;
}
impl Pushable for VMInt {
    fn push<'b>(self, _: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(Value::Int(self));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for VMInt {
    fn from_value(_: &'vm VM, value: Value) -> Option<VMInt> {
        match value {
            Value::Int(i) => Some(i),
            _ => None,
        }
    }
}
impl VMType for f64 {
    type Type = Self;
}
impl Pushable for f64 {
    fn push<'b>(self, _: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(Value::Float(self));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for f64 {
    fn from_value(_: &'vm VM, value: Value) -> Option<f64> {
        match value {
            Value::Float(f) => Some(f),
            _ => None,
        }
    }
}
impl VMType for bool {
    type Type = Self;
}
impl Pushable for bool {
    fn push<'b>(self, _: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(Value::Int(if self {
            1
        } else {
            0
        }));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for bool {
    fn from_value(_: &'vm VM, value: Value) -> Option<bool> {
        match value {
            Value::Int(1) => Some(true),
            Value::Int(0) => Some(false),
            _ => None,
        }
    }
}

impl VMType for Ordering {
    type Type = Self;
    fn make_type(vm: &VM) -> TcType {
        let symbol = vm.find_type_info("std.types.Ordering").unwrap().name.clone();
        let ctor = types::TypeConstructor::Data(symbol);
        Type::data(ctor, vec![])
    }
}
impl Pushable for Ordering {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        let tag = match self {
            Ordering::Less => 0,
            Ordering::Equal => 1,
            Ordering::Greater => 2,
        };
        let value = Value::Data(vm.alloc(&stack.stack,
                                         Def {
                                             tag: tag,
                                             elems: &[],
                                         }));
        stack.push(value);
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for Ordering {
    fn from_value(_: &'vm VM, value: Value) -> Option<Ordering> {
        match value {
            Value::Data(data) => {
                match data.tag {
                    0 => Some(Ordering::Less),
                    1 => Some(Ordering::Equal),
                    2 => Some(Ordering::Greater),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

impl VMType for str {
    type Type = String;
}
impl<'s> VMType for &'s str {
    type Type = <str as VMType>::Type;
}
impl VMType for String {
    type Type = <str as VMType>::Type;
}
impl<'s> Pushable for &'s str {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        let s = vm.alloc(&stack.stack, self);
        stack.push(Value::String(s));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for String {
    fn from_value(_: &'vm VM, value: Value) -> Option<String> {
        match value {
            Value::String(i) => Some(String::from(&i[..])),
            _ => None,
        }
    }
}
impl Pushable for String {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        let s = vm.alloc(&stack.stack, &self[..]);
        stack.push(Value::String(s));
        Status::Ok
    }
}

impl VMType for char {
    type Type = Self;
}
impl Pushable for char {
    fn push<'b>(self, _: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(Value::Int(self as VMInt));
        Status::Ok
    }
}
impl<'vm> Getable<'vm> for char {
    fn from_value(_: &'vm VM, value: Value) -> Option<char> {
        match value {
            Value::Int(x) => ::std::char::from_u32(x as u32),
            _ => None,
        }
    }
}

impl<T> VMType for Vec<T>
    where T: VMType,
          T::Type: Sized
{
    type Type = Vec<T::Type>;
}

impl<T> Pushable for Vec<T>
    where T: Pushable,
          T::Type: Sized
{
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        let len = self.len() as VMIndex;
        for v in self {
            if v.push(vm, stack) == Status::Error {
                return Status::Error;
            }
        }
        let result = {
            let values = &stack[stack.len() - len..];
            vm.alloc(&stack.stack,
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
impl<T: ::vm::Userdata + VMType> Pushable for Userdata<T> {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(Value::Userdata(Userdata_::new(vm, self.0)));
        Status::Ok
    }
}
impl<'vm, T: Clone + ::vm::Userdata> Getable<'vm> for Userdata<T> {
    fn from_value(_: &'vm VM, value: Value) -> Option<Userdata<T>> {
        match value {
            Value::Userdata(v) => v.data.downcast_ref::<T>().map(|x| Userdata(x.clone())),
            _ => None,
        }
    }
}

impl<'s, T: VMType> VMType for *const T {
    type Type = T::Type;
    fn make_type(vm: &VM) -> TcType {
        T::make_type(vm)
    }
}

impl<'vm, T: ::vm::Userdata> Getable<'vm> for *const T {
    fn from_value(_: &'vm VM, value: Value) -> Option<*const T> {
        match value {
            Value::Userdata(v) => v.data.downcast_ref::<T>().map(|x| x as *const T),
            _ => None,
        }
    }
}

impl<T: VMType> VMType for *mut T {
    type Type = T::Type;
}
impl<T: VMType + Any> Pushable for *mut T {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(Value::Userdata(Userdata_::new(vm, self)));
        Status::Ok
    }
}
impl<'vm, T: Any> Getable<'vm> for *mut T {
    fn from_value(_: &'vm VM, value: Value) -> Option<*mut T> {
        match value {
            Value::Userdata(v) => v.data.downcast_ref::<*mut T>().map(|x| *x),
            _ => None,
        }
    }
}
impl<T: VMType> VMType for Option<T>
    where T::Type: Sized
{
    type Type = Option<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        let symbol = vm.find_type_info("std.types.Option").unwrap().name.clone();
        let ctor = types::TypeConstructor::Data(symbol);
        Type::data(ctor, vec![T::make_type(vm)])
    }
}
impl<T: Pushable> Pushable for Option<T>
    where T::Type: Sized
{
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
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
impl<'vm, T: Getable<'vm>> Getable<'vm> for Option<T> {
    fn from_value(vm: &'vm VM, value: Value) -> Option<Option<T>> {
        match value {
            Value::Data(data) => {
                if data.tag == 0 {
                    Some(None)
                } else {
                    T::from_value(vm, data.fields[1]).map(Some)
                }
            }
            _ => None,
        }
    }
}

impl<T: VMType, E: VMType> VMType for Result<T, E>
    where T::Type: Sized,
          E::Type: Sized
{
    type Type = Result<T::Type, E::Type>;
    fn make_type(vm: &VM) -> TcType {
        let symbol = vm.find_type_info("std.types.Result").unwrap().name.clone();
        let ctor = types::TypeConstructor::Data(symbol);
        Type::data(ctor, vec![E::make_type(vm), T::make_type(vm)])
    }
}

impl<T: Pushable, E: Pushable> Pushable for Result<T, E>
    where T::Type: Sized,
          E::Type: Sized
{
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
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
        let data = vm.alloc(&stack.stack,
                            Def {
                                tag: tag,
                                elems: &[value],
                            });
        stack.push(Value::Data(data));
        Status::Ok
    }
}

impl<'vm, T: Getable<'vm>, E: Getable<'vm>> Getable<'vm> for Result<T, E> {
    fn from_value(vm: &'vm VM, value: Value) -> Option<Result<T, E>> {
        match value {
            Value::Data(data) => {
                match data.tag {
                    0 => E::from_value(vm, data.fields[0]).map(Err),
                    1 => T::from_value(vm, data.fields[0]).map(Ok),
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
    fn make_type(vm: &VM) -> TcType {
        T::make_type(vm)
    }
}
impl<T: Pushable, E: fmt::Display> Pushable for MaybeError<T, E> {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        match self {
            MaybeError::Ok(value) => {
                value.push(vm, stack);
                Status::Ok
            }
            MaybeError::Err(err) => {
                let msg = format!("{}", err);
                let s = vm.alloc(&stack.stack, &msg[..]);
                stack.push(Value::String(s));
                Status::Error
            }
        }
    }
}

impl<T: VMType> VMType for IO<T>
    where T::Type: Sized
{
    type Type = IO<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        let env = vm.get_env();
        let symbol = env.find_type_info("IO").unwrap().name.clone();
        Type::data(TypeConstructor::Data(symbol), vec![T::make_type(vm)])
    }
    fn extra_args() -> VMIndex {
        1
    }
}

impl<'vm, T: Getable<'vm>> Getable<'vm> for IO<T> {
    fn from_value(vm: &'vm VM, value: Value) -> Option<IO<T>> {
        T::from_value(vm, value).map(IO::Value)
    }
}

impl<T: Pushable> Pushable for IO<T>
    where T::Type: Sized
{
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
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

/// Type which represents an array in embed_lang
pub struct Array<'vm, T>(RootedValue<'vm>, PhantomData<T>);

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
    pub fn vm(&self) -> &'vm VM {
        self.0.vm()
    }

    pub fn len(&self) -> VMIndex {
        self.fields.len() as VMIndex
    }
}

impl<'vm, T: Getable<'vm>> Array<'vm, T> {
    pub fn get(&self, index: VMInt) -> Option<T> {
        match *self.0 {
            Value::Data(data) => {
                data.fields
                    .get(index as usize)
                    .and_then(|v| T::from_value(self.0.vm(), *v))
            }
            _ => None,
        }
    }
}

impl<'vm, T: VMType> VMType for Array<'vm, T>
    where T::Type: Sized
{
    type Type = Array<'static, T::Type>;
    fn make_type(vm: &VM) -> TcType {
        Type::array(T::make_type(vm))
    }
}


impl<'vm, T: VMType> Pushable for Array<'vm, T>
    where T::Type: Sized
{
    fn push<'b>(self, _: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(*self.0);
        Status::Ok
    }
}

impl<'vm, T> Getable<'vm> for Array<'vm, T> {
    fn from_value(vm: &'vm VM, value: Value) -> Option<Array<'vm, T>> {
        Some(Array(vm.root_value(value), PhantomData))
    }
}

impl<'vm, T: Any> VMType for Root<'vm, T> {
    type Type = T;
}
impl<'vm, T: ::vm::Userdata> Getable<'vm> for Root<'vm, T> {
    fn from_value(vm: &'vm VM, value: Value) -> Option<Root<'vm, T>> {
        match value {
            Value::Userdata(v) => vm.root::<T>(v.data).map(From::from),
            _ => None,
        }
    }
}

impl<'vm> VMType for RootStr<'vm> {
    type Type = <str as VMType>::Type;
}
impl<'vm> Getable<'vm> for RootStr<'vm> {
    fn from_value(vm: &'vm VM, value: Value) -> Option<RootStr<'vm>> {
        match value {
            Value::String(v) => Some(vm.root_string(v)),
            _ => None,
        }
    }
}

pub use self::record::Record;

pub mod record {
    use base::types;
    use base::types::{Type, TcType};
    use base::symbol::Symbol;

    use stack::StackFrame;
    use types::VMIndex;
    use vm::{VM, Status};
    use super::{VMType, Pushable};

    pub struct Record<T> {
        pub fields: T,
    }

    pub struct HList<H, T>(pub H, pub T);

    pub trait Field {
        fn name() -> &'static str;
    }

    pub trait FieldList {
        fn len() -> VMIndex;

        fn field_types(vm: &VM, fields: &mut Vec<types::Field<Symbol, TcType>>);
    }

    impl FieldList for () {
        fn len() -> VMIndex {
            0
        }

        fn field_types(_: &VM, _: &mut Vec<types::Field<Symbol, TcType>>) {}
    }

    impl<F: Field, H: VMType, T> FieldList for HList<(F, H), T>
        where T: FieldList
{
        fn len() -> VMIndex {
            1 + T::len()
        }

        fn field_types(vm: &VM, fields: &mut Vec<types::Field<Symbol, TcType>>) {
            fields.push(types::Field {
                name: Symbol::new(F::name()),
                typ: H::make_type(vm),
            });
            T::field_types(vm, fields);
        }
    }

    pub trait PushableFieldList: FieldList {
        fn push<'b>(self, vm: &VM, fields: &mut StackFrame<'b>);
    }

    impl PushableFieldList for () {
        fn push<'b>(self, _: &VM, _: &mut StackFrame<'b>) {}
    }

    impl<F: Field, H: Pushable, T> PushableFieldList for HList<(F, H), T>
        where T: PushableFieldList
{
        fn push<'b>(self, vm: &VM, fields: &mut StackFrame<'b>) {
            let HList((_, head), tail) = self;
            head.push(vm, fields);
            tail.push(vm, fields);
        }
    }

    impl<A: VMType, F: Field, T: FieldList> VMType for Record<HList<(F, A), T>>
        where A::Type: Sized
{
        type Type = Record<((&'static str, A::Type),)>;
        fn make_type(vm: &VM) -> TcType {
            let len = HList::<(F, A), T>::len() as usize;
            let mut fields = Vec::with_capacity(len);
            HList::<(F, A), T>::field_types(vm, &mut fields);
            Type::record(Vec::new(), fields)
        }
    }
    impl<A, F, T> Pushable for Record<HList<(F, A), T>>
        where A: Pushable,
              F: Field,
              T: PushableFieldList,
              A::Type: Sized
{
        fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
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
}

#[macro_export]
macro_rules! types {
    ($($field: ident),*) => {
        $(
        #[allow(non_camel_case_types)]
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
    fn make_type(vm: &VM) -> TcType {
        F::make_type(vm)
    }
}

impl<'vm, F: FunctionType + VMType> Pushable for Primitive<F> {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        let extern_function = unsafe {
            // The VM guarantess that it only ever calls this function with itself which should
            // make sure that ignoring the lifetime is safe
            ::std::mem::transmute::<Box<Fn(&'vm VM) -> Status + 'static>,
                                      Box<Fn(&VM) -> Status + 'static>>(Box::new(self.function))
        };
        let id = Symbol::new(self.name);
        let value = Value::Function(vm.alloc(&stack.stack,
                                             Move(ExternFunction {
                                                 id: id,
                                                 args: F::arguments(),
                                                 function: extern_function,
                                             })));
        stack.push(value);
        Status::Ok
    }
}

fn make_type<T: ?Sized + VMType>(vm: &VM) -> TcType {
    <T as VMType>::make_type(vm)
}

/// Type which represents an function in embed_lang
pub struct Function<'vm, F> {
    value: RootedValue<'vm>,
    _marker: PhantomData<F>,
}

impl<'vm, F> Function<'vm, F> {
    pub fn value(&self) -> Value {
        *self.value
    }
}

impl<'vm, F> VMType for Function<'vm, F>
    where F: VMType
{
    type Type = F::Type;
    fn make_type(vm: &VM) -> TcType {
        F::make_type(vm)
    }
}

impl<'vm, F: Any> Pushable for Function<'vm, F>
    where F: VMType
{
    fn push<'b>(self, _: &VM, stack: &mut StackFrame<'b>) -> Status {
        stack.push(*self.value);
        Status::Ok
    }
}
impl<'vm, F> Getable<'vm> for Function<'vm, F> {
    fn from_value(vm: &'vm VM, value: Value) -> Option<Function<'vm, F>> {
        Some(Function {
            value: vm.root_value(value),
            _marker: PhantomData,
        })//TODO not type safe
    }
}

impl<'vm, A, R> Function<'vm, fn(A) -> R>
    where A: Pushable + 'static,
          R: VMType + Getable<'vm> + 'static
{
    pub fn call(&mut self, a: A) -> Result<R, Error> {
        let vm = self.value.vm();
        let mut stack = vm.current_frame();
        stack = stack.enter_scope(0, None);
        stack.push(*self.value);
        a.push(vm, &mut stack);
        for _ in 0..R::extra_args() {
            0.push(vm, &mut stack);
        }
        let args = stack.len() - 1;
        stack = try!(vm.call_function(stack, args)).unwrap();
        match R::from_value(vm, stack.pop()) {
            Some(x) => Ok(x),
            None => Err(Error::Message("Wrong type".to_string())),
        }
    }
}
impl<'vm, A, B, R> Function<'vm, fn(A, B) -> R>
    where A: Pushable + 'static,
          B: Pushable + 'static,
          R: VMType + Getable<'vm> + 'static
{
    pub fn call2(&mut self, a: A, b: B) -> Result<R, Error> {
        let vm = self.value.vm();
        let mut stack = vm.current_frame();
        stack = stack.enter_scope(0, None);
        stack.push(*self.value);
        a.push(vm, &mut stack);
        b.push(vm, &mut stack);
        for _ in 0..R::extra_args() {
            0.push(vm, &mut stack);
        }
        let args = stack.len() - 1;
        stack = try!(vm.call_function(stack, args)).unwrap();
        match R::from_value(vm, stack.pop()) {
            Some(x) => Ok(x),
            None => Err(Error::Message("Wrong type".to_string())),
        }
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
    fn unpack_and_call(&self, vm: &'vm VM) -> Status;
}

impl<'s, T: FunctionType> FunctionType for &'s T {
    fn arguments() -> VMIndex {
        T::arguments()
    }
}

impl<'vm, 's, T> VMFunction<'vm> for &'s T
    where T: VMFunction<'vm>
{
    fn unpack_and_call(&self, vm: &'vm VM) -> Status {
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
impl <$($args: VMType,)* R: VMType> VMType for fn ($($args),*) -> R {
    #[allow(non_snake_case)]
    type Type = fn ($($args::Type),*) -> R::Type;
    #[allow(non_snake_case)]
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::function(args, make_type::<R>(vm))
    }
}

impl <'vm, $($args,)* R> Pushable for fn ($($args),*) -> R
where $($args: Getable<'vm> + VMType + 'vm,)* R: Pushable + 'vm {
    fn push<'b>(self, vm: &VM, stack: &mut StackFrame<'b>) -> Status {
        let f = Box::new(move |vm| self.unpack_and_call(vm));
        let extern_function = unsafe {
            //The VM guarantess that it only ever calls this function with itself which should
            //make sure that ignoring the lifetime is safe
            ::std::mem::transmute
                    ::<Box<Fn(&'vm VM) -> Status>,
                       Box<Fn(&VM) -> Status>>(f)
        };
        let id = Symbol::new("<extern>");
        let value = Value::Function(vm.alloc(&stack.stack, Move(
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
where $($args: Getable<'vm> + 'vm,)* R: Pushable + 'vm {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(&self, vm: &'vm VM) -> Status {
        let n_args = Self::arguments();
        let mut stack = vm.current_frame();
        let mut i = 0;
        $(let $args = {
            let x = $args::from_value(vm, stack[i].clone()).expect(stringify!(Argument $args));
            i += 1;
            x
        });*;
        drop(stack);
        let r = (*self)($($args),*);
        let mut stack = vm.current_frame();
        r.push(vm, &mut stack)
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
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::function(args, make_type::<R>(vm))
    }
}
impl <'vm, 's, $($args,)* R> VMFunction<'vm> for Fn($($args),*) -> R + 's
where $($args: Getable<'vm> + 'vm,)* R: Pushable + 'vm {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(&self, vm: &'vm VM) -> Status {
        let n_args = Self::arguments();
        let mut stack = vm.current_frame();
        let mut i = 0;
        $(let $args = {
            let x = $args::from_value(vm, stack[i].clone()).expect(stringify!(Argument $args));
            i += 1;
            x
        });*;
        drop(stack);
        let r = (*self)($($args),*);
        let mut stack = vm.current_frame();
        r.push(vm, &mut stack)
    }
}

impl <'s, $($args,)* R: VMType> FunctionType for Box<Fn($($args),*) -> R + 's> {
    fn arguments() -> VMIndex {
        count!($($args),*) + R::extra_args()
    }
}

impl <'vm, 's, $($args,)* R> VMFunction<'vm> for Box<Fn($($args),*) -> R + 's>
where $($args: Getable<'vm> + 'vm,)* R: Pushable + 'vm {
    fn unpack_and_call(&self, vm: &'vm VM) -> Status {
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
        fn wrapper<'b, 'c>(vm: &VM) {
            $func.unpack_and_call(vm)
        }
        wrapper
    })
}
