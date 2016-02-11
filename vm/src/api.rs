use gc::Move;
use base::symbol::Symbol;
use stack::StackFrame;
use vm::{VM, Status, DataStruct, ExternFunction, RootedValue, Value, Def, Userdata_, VMInt, Error,
         Root, RootStr};
use base::types;
use base::types::{TcType, Type, TypeConstructor};
use types::VMIndex;
use std::any::Any;
use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;

/// Type representing embed_lang's IO type
#[derive(Debug)]
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
pub struct Generic<'a, T>(pub Value<'a>, PhantomData<T>);

impl<'a, T: VMType> VMType for Generic<'a, T> {
    type Type = T::Type;

    fn make_type(vm: &VM) -> TcType {
        T::make_type(vm)
    }

    fn extra_args() -> VMIndex {
        T::extra_args()
    }
}
impl<'a, T: VMType> Pushable<'a> for Generic<'a, T> {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(self.0);
        Status::Ok
    }
}
impl<'a, 'vm, T> Getable<'a, 'vm> for Generic<'a, T> {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<Generic<'a, T>> {
        Some(Generic(value, PhantomData))
    }
}

/// Module containing types which represent generic variables in embed_lang's type system
pub mod generic {
    use super::VMType;
    use base::types::{Type, TcType, Generic, Kind};
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
                    Type::generic(Generic {
                        id: vm.symbol(lower_str),
                        kind: Kind::star(),
                    })
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
        TcType::from(vm_type::<Self>(vm).clone())
    }

    /// How many extra arguments a function returning this type requires.
    /// Used for abstract types which when used in return position should act like they still need
    /// more arguments before they are called
    fn extra_args() -> VMIndex {
        0
    }
}


/// Trait which allows a rust value to be pushed to the virtual machine
pub trait Pushable<'a> : VMType {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status;
}

/// Trait which allows rust values to be retrieved from the virtual machine
pub trait Getable<'a, 'vm>: Sized {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Self>;
}

/// Wrapper type which passes acts as the type `T` but also passes the `VM` to the called function
pub struct WithVM<'a: 'vm, 'vm, T> {
    pub vm: &'vm VM<'a>,
    pub value: T,
}

impl<'a, 'vm, T> VMType for WithVM<'a, 'vm, T> where T: VMType
{
    type Type = T::Type;

    fn make_type(vm: &VM) -> TcType {
        T::make_type(vm)
    }

    fn extra_args() -> VMIndex {
        T::extra_args()
    }
}

impl<'a, 'vm, T> Pushable<'a> for WithVM<'a, 'vm, T> where T: Pushable<'a>
{
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        self.value.push(vm, stack)
    }
}

impl<'a, 'vm, T> Getable<'a, 'vm> for WithVM<'a, 'vm, T> where T: Getable<'a, 'vm>
{
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<WithVM<'a, 'vm, T>> {
        T::from_value(vm, value).map(|t| WithVM { vm: vm, value: t })
    }
}


impl VMType for () {
    type Type = Self;
}
impl<'a> Pushable<'a> for () {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Int(0));
        Status::Ok
    }
}
impl<'a, 'vm> Getable<'a, 'vm> for () {
    fn from_value(_: &'vm VM<'a>, _: Value) -> Option<()> {
        Some(())
    }
}

impl VMType for VMInt {
    type Type = Self;
}
impl<'a> Pushable<'a> for VMInt {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Int(self));
        Status::Ok
    }
}
impl<'a, 'vm> Getable<'a, 'vm> for VMInt {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<VMInt> {
        match value {
            Value::Int(i) => Some(i),
            _ => None,
        }
    }
}
impl VMType for f64 {
    type Type = Self;
}
impl<'a> Pushable<'a> for f64 {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Float(self));
        Status::Ok
    }
}
impl<'a, 'vm> Getable<'a, 'vm> for f64 {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<f64> {
        match value {
            Value::Float(f) => Some(f),
            _ => None,
        }
    }
}
impl VMType for bool {
    type Type = Self;
}
impl<'a> Pushable<'a> for bool {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Int(if self {
            1
        } else {
            0
        }));
        Status::Ok
    }
}
impl<'a, 'vm> Getable<'a, 'vm> for bool {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<bool> {
        match value {
            Value::Int(1) => Some(true),
            Value::Int(0) => Some(false),
            _ => None,
        }
    }
}

impl VMType for Ordering {
    type Type = Self;
}
impl<'a> Pushable<'a> for Ordering {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
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
impl<'a, 'vm> Getable<'a, 'vm> for Ordering {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<Ordering> {
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
impl<'a, 's> Pushable<'a> for &'s str {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        let s = vm.alloc(&stack.stack, self);
        stack.push(Value::String(s));
        Status::Ok
    }
}
impl<'a, 'vm> Getable<'a, 'vm> for String {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<String> {
        match value {
            Value::String(i) => Some(String::from(&i[..])),
            _ => None,
        }
    }
}
impl<'a> Pushable<'a> for String {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        let s = vm.alloc(&stack.stack, &self[..]);
        stack.push(Value::String(s));
        Status::Ok
    }
}

impl VMType for char {
    type Type = Self;
}
impl<'a> Pushable<'a> for char {
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Int(self as VMInt));
        Status::Ok
    }
}
impl<'a, 'vm> Getable<'a, 'vm> for char {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<char> {
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

impl<'a, T> Pushable<'a> for Vec<T>
    where T: Pushable<'a>,
          T::Type: Sized
{
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
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

impl<T: VMType> VMType for Box<T> {
    type Type = T::Type;
}
impl<'a, T: Any + VMType> Pushable<'a> for Box<T> {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Userdata(Userdata_::new(vm, self)));
        Status::Ok
    }
}

impl<T: VMType> VMType for *mut T {
    type Type = T::Type;
}
impl<'a, T: VMType + Any> Pushable<'a> for *mut T {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(Value::Userdata(Userdata_::new(vm, self)));
        Status::Ok
    }
}
impl<'a, 'vm, T: Any> Getable<'a, 'vm> for *mut T {
    fn from_value(_: &'vm VM<'a>, value: Value<'a>) -> Option<*mut T> {
        match value {
            Value::Userdata(v) => v.data.downcast_ref::<*mut T>().map(|x| *x),
            _ => None,
        }
    }
}
impl<T: VMType> VMType for Option<T> where T::Type: Sized
{
    type Type = Option<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        let ctor = types::TypeConstructor::Data(vm.symbol("std.prelude.Option"));
        Type::data(ctor, vec![T::make_type(vm)])
    }
}
impl<'a, T: Pushable<'a>> Pushable<'a> for Option<T> where T::Type: Sized
{
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
impl<'a, 'vm, T: Getable<'a, 'vm>> Getable<'a, 'vm> for Option<T> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Option<T>> {
        match value {
            Value::Data(data) => {
                if data.tag == 0 {
                    Some(None)
                } else {
                    T::from_value(vm, data.fields[1].get()).map(Some)
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
        let ctor = types::TypeConstructor::Data(vm.symbol("std.prelude.Result"));
        Type::data(ctor, vec![E::make_type(vm), T::make_type(vm)])
    }
}

impl<'a, T: Pushable<'a>, E: Pushable<'a>> Pushable<'a> for Result<T, E>
    where T::Type: Sized,
          E::Type: Sized
{
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
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

impl<'a, 'vm, T: Getable<'a, 'vm>, E: Getable<'a, 'vm>> Getable<'a, 'vm> for Result<T, E> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Result<T, E>> {
        match value {
            Value::Data(data) => {
                match data.tag {
                    0 => E::from_value(vm, data.fields[0].get()).map(Err),
                    1 => T::from_value(vm, data.fields[0].get()).map(Ok),
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
impl<'a, T: Pushable<'a>, E: fmt::Display> Pushable<'a> for MaybeError<T, E> {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
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

impl<T: VMType> VMType for IO<T> where T::Type: Sized
{
    type Type = IO<T::Type>;
    fn make_type(vm: &VM) -> TcType {
        Type::data(TypeConstructor::Data(vm.symbol("IO")),
                   vec![T::make_type(vm)])
    }
    fn extra_args() -> VMIndex {
        1
    }
}

impl<'a, 'vm, T: Getable<'a, 'vm>> Getable<'a, 'vm> for IO<T> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<IO<T>> {
        T::from_value(vm, value).map(IO::Value)
    }
}

impl<'a, T: Pushable<'a>> Pushable<'a> for IO<T> where T::Type: Sized
{
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
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
pub struct Array<'a: 'vm, 'vm, T: 'a>(RootedValue<'a, 'vm>, PhantomData<T>);

impl<'a, 'vm, T> Deref for Array<'a, 'vm, T> {
    type Target = DataStruct<'a>;
    fn deref(&self) -> &DataStruct<'a> {
        match *self.0 {
            Value::Data(ref data) => data,
            _ => panic!("Expected data"),
        }
    }
}

impl<'a, 'vm, T> Array<'a, 'vm, T> {
    pub fn vm(&self) -> &'vm VM<'a> {
        self.0.vm()
    }

    pub fn len(&self) -> VMIndex {
        self.fields.len() as VMIndex
    }
}

impl<'a, 'vm, T: Getable<'a, 'vm>> Array<'a, 'vm, T> {
    pub fn get(&self, index: VMInt) -> Option<T> {
        match *self.0 {
            Value::Data(data) => {
                data.fields
                    .get(index as usize)
                    .and_then(|v| T::from_value(self.0.vm(), v.get()))
            }
            _ => None,
        }
    }
}

impl<'a, 'vm, T: VMType> VMType for Array<'a, 'vm, T> where T::Type: Sized
{
    type Type = Array<'static, 'static, T::Type>;
    fn make_type(vm: &VM) -> TcType {
        Type::array(T::make_type(vm))
    }
}


impl<'a, 'vm, T: VMType> Pushable<'a> for Array<'a, 'vm, T> where T::Type: Sized
{
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(*self.0);
        Status::Ok
    }
}

impl<'a: 'vm, 'vm, T> Getable<'a, 'vm> for Array<'a, 'vm, T> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Array<'a, 'vm, T>> {
        Some(Array(vm.root_value(value), PhantomData))
    }
}

impl<'r, T: Any> VMType for Root<'r, T> {
    type Type = T;
}
impl<'a, 'vm, T: Any> Getable<'a, 'vm> for Root<'vm, T> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Root<'vm, T>> {
        match value {
            Value::Userdata(v) => vm.root::<T>(v.data).map(From::from),
            _ => None,
        }
    }
}

impl<'r> VMType for RootStr<'r> {
    type Type = <str as VMType>::Type;
}
impl<'a, 'vm> Getable<'a, 'vm> for RootStr<'vm> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<RootStr<'vm>> {
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

    impl<F: Field, H: VMType, T> FieldList for HList<(F, H), T> where T: FieldList
{
        fn len() -> VMIndex {
            1 + T::len()
        }

        fn field_types(vm: &VM, fields: &mut Vec<types::Field<Symbol, TcType>>) {
            fields.push(types::Field {
                name: vm.symbol(F::name()),
                typ: H::make_type(vm),
            });
            T::field_types(vm, fields);
        }
    }

    pub trait PushableFieldList<'a>: FieldList {
        fn push<'b>(self, vm: &VM<'a>, fields: &mut StackFrame<'a, 'b>);
    }

    impl<'a> PushableFieldList<'a> for () {
        fn push<'b>(self, _: &VM<'a>, _: &mut StackFrame<'a, 'b>) {}
    }

    impl<'a, F: Field, H: Pushable<'a>, T> PushableFieldList<'a> for HList<(F, H), T>
        where T: PushableFieldList<'a>
{
        fn push<'b>(self, vm: &VM<'a>, fields: &mut StackFrame<'a, 'b>) {
            let HList((_, head), tail) = self;
            head.push(vm, fields);
            tail.push(vm, fields);
        }
    }

    impl<A: VMType, F: Field, T: FieldList> VMType for Record<HList<(F, A), T>> where A::Type: Sized
{
        type Type = Record<((&'static str, A::Type),)>;
        fn make_type(vm: &VM) -> TcType {
            let len = HList::<(F, A), T>::len() as usize;
            let mut fields = Vec::with_capacity(len);
            HList::<(F, A), T>::field_types(vm, &mut fields);
            Type::record(Vec::new(), fields)
        }
    }
    impl<'a, A, F, T> Pushable<'a> for Record<HList<(F, A), T>>
        where A: Pushable<'a>,
              F: Field,
              T: PushableFieldList<'a>,
              A::Type: Sized
{
        fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
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
macro_rules! record {
    ($($field: ident => $value: expr),*) => {
        {
            mod _field { types!($($field),*); }
            $crate::api::Record {
                fields: hlist!($($field => $value),*)
            }
        }
    }
}

impl<F: VMType> VMType for Primitive<F> {
    type Type = F::Type;
    fn make_type(vm: &VM) -> TcType {
        F::make_type(vm)
    }
}

impl<'a: 'vm, 'vm, F: FunctionType + VMType> Pushable<'a> for Primitive<F> {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        let extern_function = unsafe {
            // The VM guarantess that it only ever calls this function with itself which should
            // make sure that ignoring the lifetime is safe
            ::std::mem::transmute::<Box<Fn(&'vm VM<'a>) -> Status + 'static>,
                                      Box<Fn(&VM<'a>) -> Status + 'static>>(Box::new(self.function))
        };
        let id = vm.symbol(self.name);
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

fn vm_type<'a, T: ?Sized + VMType>(vm: &'a VM) -> &'a Type<Symbol> {
    vm.get_type::<T::Type>()
}

fn make_type<T: ?Sized + VMType>(vm: &VM) -> TcType {
    <T as VMType>::make_type(vm)
}

/// Type which represents an function in embed_lang
pub struct Function<'a: 'vm, 'vm, F> {
    value: RootedValue<'a, 'vm>,
    _marker: PhantomData<F>,
}

impl<'vm, 'b, F> VMType for Function<'b, 'vm, F> where F: VMType
{
    type Type = F::Type;
    fn make_type(vm: &VM) -> TcType {
        F::make_type(vm)
    }
}

impl<'vm, 'a, F: Any> Pushable<'a> for Function<'a, 'vm, F> where F: VMType
{
    fn push<'b>(self, _: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        stack.push(*self.value);
        Status::Ok
    }
}
impl<'a, 'vm, F> Getable<'a, 'vm> for Function<'a, 'vm, F> {
    fn from_value(vm: &'vm VM<'a>, value: Value<'a>) -> Option<Function<'a, 'vm, F>> {
        Some(Function {
            value: vm.root_value(value),
            _marker: PhantomData,
        })//TODO not type safe
    }
}

impl<'a, 'vm, A, R> Function<'a, 'vm, fn(A) -> R>
    where A: Pushable<'a> + 'static,
          R: VMType + Getable<'a, 'vm> + 'static
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
impl<'a, 'vm, A, B, R> Function<'a, 'vm, fn(A, B) -> R>
    where A: Pushable<'a> + 'static,
          B: Pushable<'a> + 'static,
          R: VMType + Getable<'a, 'vm> + 'static
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
pub trait VMFunction<'a: 'vm, 'vm> {
    fn unpack_and_call(&self, vm: &'vm VM<'a>) -> Status;
}

impl<'s, T: FunctionType> FunctionType for &'s T {
    fn arguments() -> VMIndex {
        T::arguments()
    }
}

impl<'a: 'vm, 'vm, 's, T> VMFunction<'a, 'vm> for &'s T where T: VMFunction<'a, 'vm>
{
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
impl <$($args: VMType,)* R: VMType> VMType for fn ($($args),*) -> R {
    #[allow(non_snake_case)]
    type Type = fn ($($args::Type),*) -> R::Type;
    #[allow(non_snake_case)]
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::function(args, make_type::<R>(vm))
    }
}

impl <'a: 'vm, 'vm, $($args,)* R> Pushable<'a> for fn ($($args),*) -> R
where $($args: Getable<'a, 'vm> + VMType + 'vm,)* R: Pushable<'a> + 'vm {
    fn push<'b>(self, vm: &VM<'a>, stack: &mut StackFrame<'a, 'b>) -> Status {
        let f = Box::new(move |vm| self.unpack_and_call(vm));
        let extern_function = unsafe {
            //The VM guarantess that it only ever calls this function with itself which should
            //make sure that ignoring the lifetime is safe
            ::std::mem::transmute
                    ::<Box<Fn(&'vm VM<'a>) -> Status>,
                       Box<Fn(&VM<'a>) -> Status>>(f)
        };
        let id = vm.symbol("<extern>");
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

impl <'a, 'vm, $($args,)* R: VMType> FunctionType for fn ($($args),*) -> R {
    fn arguments() -> VMIndex {
        count!($($args),*) + R::extra_args()
    }
}

impl <'a: 'vm, 'vm, $($args,)* R> VMFunction<'a, 'vm> for fn ($($args),*) -> R
where $($args: Getable<'a, 'vm> + 'vm,)* R: Pushable<'a> + 'vm {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(&self, vm: &'vm VM<'a>) -> Status {
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

impl <'a, 's, $($args: VMType,)* R: VMType> VMType for Fn($($args),*) -> R + 's {
    type Type = fn ($($args::Type),*) -> R::Type;

    #[allow(non_snake_case)]
    fn make_type(vm: &VM) -> TcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        Type::function(args, make_type::<R>(vm))
    }
}
impl <'a: 'vm, 'vm, 's, $($args,)* R> VMFunction<'a, 'vm> for Fn($($args),*) -> R + 's
where $($args: Getable<'a, 'vm> + 'vm,)* R: Pushable<'a> + 'vm {
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables)]
    fn unpack_and_call(&self, vm: &'vm VM<'a>) -> Status {
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

impl <'a: 'vm, 'vm, 's, $($args,)* R> VMFunction<'a, 'vm> for Box<Fn($($args),*) -> R + 's>
where $($args: Getable<'a, 'vm> + 'vm,)* R: Pushable<'a> + 'vm {
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
