//! The marshalling api
use base::scoped_map::ScopedMap;
use base::symbol::{Symbol, Symbols};
use base::types::{self, ArcType, Type};
use gc::{DataDef, Gc, GcPtr, Move, Traverseable};
use stack::Lock;
use thread::ThreadInternal;
use thread::{self, Context, RootedThread, VmRoot};
use types::{VmIndex, VmInt, VmTag};
use value::{
    ArrayDef, ArrayRepr, Cloner, ClosureData, DataStruct, Def, GcStr, Value, ValueArray, ValueRepr,
};
use vm::{self, RootedValue, Status, Thread};
use {forget_lifetime, Error, Result, Variants};

use std::any::Any;
use std::borrow::Borrow;
use std::cell::Ref;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::marker::PhantomData;
use std::ops::Deref;
use std::result::Result as StdResult;

use futures::{Async, Future};

pub use self::function::*;
pub use self::opaque::{Opaque, OpaqueRef, OpaqueValue};
pub use self::record::Record;
pub use thread::ActiveThread;
pub use value::Userdata;

macro_rules! count {
    () => { 0 };
    ($_e: ident) => { 1 };
    ($_e: ident, $($rest: ident),*) => { 1 + count!($($rest),*) }
}

#[macro_use]
pub mod mac;
pub mod function;
mod opaque;
pub mod record;

#[cfg(feature = "serde")]
pub mod de;
#[cfg(feature = "serde")]
pub mod json;
#[cfg(feature = "serde")]
pub mod ser;
#[cfg(feature = "serde")]
pub mod typ;

#[derive(Copy, Clone, Debug)]
pub enum ValueRef<'a> {
    Byte(u8),
    Int(VmInt),
    Float(f64),
    String(&'a str),
    Data(Data<'a>),
    Array(ArrayRef<'a>),
    Userdata(&'a vm::Userdata),
    Thread(&'a Thread),
    Closure(Closure<'a>),
    Internal,
}

// Need to manually implement PartialEq so that `ValueRef`'s with different lifetimes can be compared
impl<'a, 'b> PartialEq<ValueRef<'b>> for ValueRef<'a> {
    fn eq(&self, other: &ValueRef) -> bool {
        use self::ValueRef::*;

        match (self, other) {
            (&Byte(l), &Byte(r)) => l == r,
            (&Int(l), &Int(r)) => l == r,
            (&Float(l), &Float(r)) => l == r,
            (&String(l), &String(r)) => l == r,
            (&Data(l), &Data(r)) => l == r,
            _ => false,
        }
    }
}

impl<'a> PartialEq<Value> for ValueRef<'a> {
    fn eq(&self, other: &Value) -> bool {
        self == &ValueRef::new(other)
    }
}

impl<'a> ValueRef<'a> {
    pub(crate) fn new(value: &'a Value) -> ValueRef<'a> {
        unsafe { ValueRef::rooted_new(value.get_repr()) }
    }

    pub(crate) unsafe fn rooted_new(value: ValueRepr) -> ValueRef<'a> {
        match value {
            ValueRepr::Byte(i) => ValueRef::Byte(i),
            ValueRepr::Int(i) => ValueRef::Int(i),
            ValueRepr::Float(f) => ValueRef::Float(f),
            ValueRepr::String(s) => ValueRef::String(forget_lifetime(&*s)),
            ValueRepr::Data(data) => ValueRef::Data(Data(DataInner::Data(forget_lifetime(&*data)))),
            ValueRepr::Tag(tag) => ValueRef::Data(Data(DataInner::Tag(tag))),
            ValueRepr::Array(array) => ValueRef::Array(ArrayRef(forget_lifetime(&*array))),
            ValueRepr::Userdata(data) => ValueRef::Userdata(forget_lifetime(&**data)),
            ValueRepr::Thread(thread) => ValueRef::Thread(forget_lifetime(&*thread)),
            ValueRepr::Closure(c) => ValueRef::Closure(Closure(forget_lifetime(&*c))),
            ValueRepr::Function(_) | ValueRepr::PartialApplication(_) => ValueRef::Internal,
        }
    }

    pub fn tag(t: VmTag) -> Self {
        ValueRef::Data(Data(DataInner::Tag(t)))
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Closure<'a>(&'a ClosureData);

impl<'a> Closure<'a> {
    pub fn name(&self) -> &str {
        self.0.function.name.definition_name()
    }
    pub fn upvars(&self) -> impl Iterator<Item = Variants<'a>> {
        ::value::variant_iter(&self.0.upvars)
    }
    pub fn debug_info(&self) -> &::compiler::DebugInfo {
        &self.0.function.debug_info
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
enum DataInner<'a> {
    Tag(VmTag),
    Data(&'a DataStruct),
}

/// Stores values of variants and records.
#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Data<'a>(DataInner<'a>);

impl<'a> Data<'a> {
    /// The tag of this variant. If this value is a variant, the tag is the zero-based
    /// index of the variant that is present, in order of the declaration.
    ///
    /// Use this method to find out what variant you are dealing with, before extracting
    /// data from it.
    ///
    /// ## Examples
    ///
    /// ```gluon
    /// type OneOfFour =
    ///     | First
    ///     | Second
    ///     | Third
    ///     | Fourth
    ///
    /// let val = First // has the tag '0'
    /// let val = Fourth // has the tag '3'
    /// ```
    pub fn tag(&self) -> VmTag {
        match self.0 {
            DataInner::Tag(tag) => tag,
            DataInner::Data(data) => data.tag(),
        }
    }

    /// Returns the number of fields of this value.
    pub fn len(&self) -> usize {
        match self.0 {
            DataInner::Tag(_) => 0,
            DataInner::Data(data) => data.fields.len(),
        }
    }

    /// Retrieves the value of the field at `index`, like `get_variant`, but does not
    /// wrap it in a `Variants` struct.
    pub fn get(&self, index: usize) -> Option<ValueRef<'a>> {
        match self.0 {
            DataInner::Tag(_) => None,
            DataInner::Data(data) => data.fields.get(index).map(ValueRef::new),
        }
    }

    /// Creates an iterator over the fields of this value.
    pub fn iter(&self) -> impl Iterator<Item = Variants<'a>> {
        ::value::variant_iter(self.fields())
    }

    fn fields(&self) -> &'a [Value] {
        match self.0 {
            DataInner::Tag(_) => &[][..],
            DataInner::Data(data) => &data.fields,
        }
    }

    /// Retrieves the value of the field at `index`. This is useful if you cannot
    /// name the field (like in a variant). If the value is a record, use
    /// `lookup_field` instead.
    pub fn get_variant(&self, index: usize) -> Option<Variants<'a>> {
        match self.0 {
            DataInner::Tag(_) => None,
            DataInner::Data(data) => unsafe { data.fields.get(index).map(|v| Variants::new(v)) },
        }
    }

    /// Retrieves the field `name` from this record.
    pub fn lookup_field(&self, thread: &Thread, name: &str) -> Option<Variants<'a>> {
        match self.0 {
            DataInner::Tag(_) => None,
            DataInner::Data(data) => unsafe {
                GcPtr::from_raw(data)
                    .get(thread, name)
                    .ok()
                    .and_then(|x| x)
                    .map(|v| Variants(v.get_value().get_repr(), PhantomData))
            },
        }
    }

    #[doc(hidden)]
    pub fn field_names(&self) -> Vec<::interner::InternedStr> {
        match self.0 {
            DataInner::Tag(_) => Vec::new(),
            DataInner::Data(data) => unsafe {
                GcPtr::from_raw(data).field_map().keys().cloned().collect()
            },
        }
    }
}

/// Marker type representing a hole
pub struct Hole(());

impl VmType for Hole {
    type Type = Hole;

    fn make_type(vm: &Thread) -> ArcType {
        vm.global_env().type_cache().hole()
    }
}

/// Type representing gluon's IO type
#[derive(Debug, PartialEq)]
pub enum IO<T> {
    Value(T),
    Exception(String),
}

impl<T, E> From<StdResult<T, E>> for IO<T>
where
    E: fmt::Display,
{
    fn from(result: StdResult<T, E>) -> IO<T> {
        match result {
            Ok(value) => IO::Value(value),
            Err(err) => IO::Exception(err.to_string()),
        }
    }
}

#[derive(PartialEq)]
pub(crate) struct Unrooted<T: ?Sized>(Value, PhantomData<T>);

impl<T: ?Sized> From<Value> for Unrooted<T> {
    fn from(value: Value) -> Unrooted<T> {
        Unrooted(value, PhantomData)
    }
}

impl<T> fmt::Debug for Unrooted<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: VmType> VmType for Unrooted<T> {
    type Type = T::Type;

    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }

    fn extra_args() -> VmIndex {
        T::extra_args()
    }
}
impl<'vm, T: VmType> Pushable<'vm> for Unrooted<T> {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(self.0);
        Ok(())
    }
}

impl<T> Traverseable for Unrooted<T> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

pub type Generic<T> = OpaqueValue<RootedThread, T>;

/// Module containing types which represent generic variables in gluon's type system
pub mod generic {
    use super::VmType;
    use base::types::ArcType;
    use vm::Thread;

    macro_rules! make_generics {
        ($($i: ident)+) => {
            $(
            #[derive(Clone, Copy, PartialEq, Debug)]
            pub enum $i { }
            impl VmType for $i {
                type Type = $i;
                fn make_type(vm: &Thread) -> ArcType {
                    let s = stringify!($i);
                    let lower  = [s.as_bytes()[0] + 32];
                    let lower_str = ::std::str::from_utf8(&lower).unwrap();
                    vm.global_env().get_generic(lower_str)
                }
            }
            )+
        }
    }
    make_generics!{A B C D E F G H I J K L M N O P Q R X Y Z}
}

fn insert_forall(
    variables: &mut ScopedMap<Symbol, types::Generic<Symbol>>,
    typ: &ArcType,
) -> Option<ArcType> {
    variables.enter_scope();
    let new_type = insert_forall_walker(variables, typ);
    let params: Vec<_> = variables.exit_scope().map(|(_, generic)| generic).collect();

    if !params.is_empty() {
        Some(Type::forall(
            params,
            new_type.unwrap_or_else(|| typ.clone()),
        ))
    } else {
        new_type
    }
}

fn insert_forall_walker(
    variables: &mut ScopedMap<Symbol, types::Generic<Symbol>>,
    typ: &ArcType,
) -> Option<ArcType> {
    match **typ {
        Type::Generic(ref generic) => {
            if variables.get(&generic.id).is_none() {
                variables.insert(generic.id.clone(), generic.clone());
            }
            None
        }
        Type::Record(ref typ) => match **typ {
            Type::ExtendRow { .. } => types::walk_move_type_opt(
                typ,
                &mut types::ControlVisitation(|typ: &ArcType| insert_forall(variables, typ)),
            ).map(|typ| ArcType::from(Type::Record(typ))),
            _ => None,
        },
        _ => types::walk_move_type_opt(
            typ,
            &mut types::ControlVisitation(|typ: &ArcType| insert_forall_walker(variables, typ)),
        ),
    }
}

/// Trait which maps a type in rust to a type in gluon
pub trait VmType {
    /// A version of `Self` which implements `Any` allowing a `TypeId` to be retrieved
    type Type: ?Sized + Any;

    fn make_forall_type(vm: &Thread) -> ArcType {
        let typ = Self::make_type(vm);
        let mut variables = ScopedMap::new();
        insert_forall(&mut variables, &typ).unwrap_or(typ)
    }

    /// Creates an gluon type which maps to `Self` in rust
    fn make_type(vm: &Thread) -> ArcType {
        vm.get_type::<Self::Type>().unwrap_or_else(|| {
            ice!(
                "Expected type to be inserted before get_type call. \
                 Did you forget to call `Thread::register_type`?"
            )
        })
    }

    /// How many extra arguments a function returning this type requires.
    /// Used for abstract types which when used in return position should act like they still need
    /// more arguments before they are called
    fn extra_args() -> VmIndex {
        0
    }
}

/// Trait which allows a possibly asynchronous rust value to be pushed to the virtual machine
pub trait AsyncPushable<'vm> {
    /// Pushes `self` to `stack`. If the call is successful a single element should have been added
    /// to the stack and `Ok(())` should be returned. If the call is unsuccessful `Status:Error`
    /// should be returned and the stack should be left intact.
    ///
    /// If the value must be computed asynchronously `Async::NotReady` must be returned so that
    /// the virtual machine knows it must do more work before the value is available.
    fn async_push(self, context: &mut ActiveThread<'vm>, lock: Lock) -> Result<Async<()>>;

    fn async_status_push(self, context: &mut ActiveThread<'vm>, lock: Lock) -> Status
    where
        Self: Sized,
    {
        match self.async_push(context, lock) {
            Ok(Async::Ready(())) => Status::Ok,
            Ok(Async::NotReady) => Status::Yield,
            Err(err) => {
                let msg = unsafe {
                    GcStr::from_utf8_unchecked(
                        context
                            .context()
                            .alloc_ignore_limit(format!("{}", err).as_bytes()),
                    )
                };
                context.push(ValueRepr::String(msg));
                Status::Error
            }
        }
    }
}

impl<'vm, T> AsyncPushable<'vm> for T
where
    T: Pushable<'vm>,
{
    fn async_push(self, context: &mut ActiveThread<'vm>, lock: Lock) -> Result<Async<()>> {
        context.stack().release_lock(lock);
        self.push(context).map(Async::Ready)
    }
}

/// Trait which allows a rust value to be pushed to the virtual machine
pub trait Pushable<'vm>: AsyncPushable<'vm> {
    /// Pushes `self` to `stack`. If the call is successful a single element should have been added
    /// to the stack and `Ok(())` should be returned. If the call is unsuccessful `Status:Error`
    /// should be returned and the stack should be left intact
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()>;

    fn status_push(self, context: &mut ActiveThread<'vm>) -> Status
    where
        Self: Sized,
    {
        match self.push(context) {
            Ok(()) => Status::Ok,
            Err(err) => {
                let msg = unsafe {
                    GcStr::from_utf8_unchecked(
                        context
                            .context()
                            .alloc_ignore_limit(format!("{}", err).as_bytes()),
                    )
                };
                context.push(ValueRepr::String(msg));
                Status::Error
            }
        }
    }

    unsafe fn marshal_unrooted(self, vm: &'vm Thread) -> Result<Value>
    where
        Self: Sized,
    {
        let mut context = vm.current_context();
        self.push(&mut context)?;
        let value = context.pop().get_value();
        Ok(value)
    }

    fn marshal<T>(self, vm: &'vm Thread) -> Result<RootedValue<T>>
    where
        Self: Sized,
        T: VmRoot<'vm>,
    {
        let mut context = vm.current_context();
        self.push(&mut context)?;
        let variants = context.pop();
        Ok(vm.root_value(*variants))
    }
}

/// Trait which allows rust values to be retrieved from the virtual machine
pub trait Getable<'vm, 'value>: Sized {
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self;
}

pub fn convert<'vm, T, U>(thread: &'vm Thread, t: T) -> Result<U>
where
    T: Pushable<'vm>,
    U: for<'value> Getable<'vm, 'value>,
{
    let mut context = thread.current_context();
    convert_with_active_thread(&mut context, t)
}

fn convert_with_active_thread<'vm, T, U>(context: &mut ActiveThread<'vm>, t: T) -> Result<U>
where
    T: Pushable<'vm>,
    U: for<'value> Getable<'vm, 'value>,
{
    t.push(context)?;
    let thread = context.thread();
    let value = context.pop();
    Ok(U::from_value(thread, *value))
}

impl<'vm, T: vm::Userdata> Pushable<'vm> for T {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let thread = context.thread();
        let context = context.context();
        let data: Box<vm::Userdata> = Box::new(self);
        let userdata = context.alloc_with(thread, Move(data))?;
        context.stack.push(ValueRepr::Userdata(userdata));
        Ok(())
    }
}

impl<'vm, 'value> Getable<'vm, 'value> for ValueRef<'value> {
    fn from_value(_vm: &'vm Thread, value: Variants<'value>) -> Self {
        value.as_ref()
    }
}

impl<'vm, T: ?Sized + VmType> VmType for PhantomData<T> {
    type Type = T::Type;
    fn make_forall_type(vm: &Thread) -> ArcType {
        T::make_forall_type(vm)
    }
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
    fn extra_args() -> VmIndex {
        T::extra_args()
    }
}

/// Wrapper which extracts a `Userdata` value from gluon
#[derive(Debug)]
pub struct UserdataValue<T: ?Sized>(pub T);

impl<T> VmType for UserdataValue<T>
where
    T: ?Sized + VmType,
{
    type Type = T::Type;

    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }

    fn make_forall_type(vm: &Thread) -> ArcType {
        T::make_forall_type(vm)
    }

    fn extra_args() -> VmIndex {
        T::extra_args()
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for UserdataValue<T>
where
    T: vm::Userdata + Clone,
{
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        UserdataValue(<&'value T as Getable<'vm, 'value>>::from_value(vm, value).clone())
    }
}

impl<'vm, T> Pushable<'vm> for UserdataValue<T>
where
    T: vm::Userdata,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        self.0.push(context)
    }
}

impl<'vm, T: ?Sized + VmType> VmType for &'vm T {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for &'value T
where
    T: vm::Userdata,
{
    // Only allow the unsafe version to be used
    fn from_value(_vm: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::Userdata(data) => data.downcast_ref::<T>().unwrap(),
            _ => ice!("ValueRef is not an Userdata"),
        }
    }
}

impl<'vm, 'value> Getable<'vm, 'value> for &'value str {
    fn from_value(_vm: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::String(ref s) => s,
            _ => ice!("ValueRef is not a String"),
        }
    }
}

/// Wrapper type which passes acts as the type `T` but also passes the `VM` to the called function
pub struct WithVM<'vm, T> {
    pub vm: &'vm Thread,
    pub value: T,
}

impl<'vm, T> VmType for WithVM<'vm, T>
where
    T: VmType,
{
    type Type = T::Type;

    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }

    fn extra_args() -> VmIndex {
        T::extra_args()
    }
}

impl<'vm, T> Pushable<'vm> for WithVM<'vm, T>
where
    T: Pushable<'vm>,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        self.value.push(context)
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for WithVM<'vm, T>
where
    T: Getable<'vm, 'value>,
{
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> WithVM<'vm, T> {
        let t = T::from_value(vm, value);
        WithVM { vm, value: t }
    }
}

impl VmType for () {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for () {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Int(0));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for () {
    fn from_value(_: &'vm Thread, _: Variants) -> () {
        ()
    }
}

impl VmType for u8 {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for u8 {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Byte(self));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for u8 {
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> u8 {
        match value.as_ref() {
            ValueRef::Byte(i) => i,
            _ => ice!("ValueRef is not a Byte"),
        }
    }
}

macro_rules! int_impls {
    ($($id: ident)*) => {
        $(
        impl VmType for $id {
            type Type = VmInt;
        }
        impl<'vm> Pushable<'vm> for $id {
            fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
                context.push(ValueRepr::Int(self as VmInt));
                Ok(())
            }
        }
        impl<'vm, 'value> Getable<'vm, 'value> for $id {
            fn from_value(_: &'vm Thread, value: Variants<'value>) -> Self {
                match value.as_ref() {
                    ValueRef::Int(i) => i as $id,
                    _ => ice!("expected ValueRef to be an Int, got {:?}", value.as_ref()),
                }
            }
        }
        )*
    };
}

int_impls!{ i16 i32 i64 u16 u32 u64 usize isize }

impl VmType for f64 {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for f64 {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Float(self));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for f64 {
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> f64 {
        match value.as_ref() {
            ValueRef::Float(f) => f,
            _ => ice!("ValueRef is not a Float"),
        }
    }
}
impl VmType for bool {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        (*vm.global_env()
            .get_env()
            .find_type_info("std.types.Bool")
            .unwrap()).clone()
        .into_type()
    }
}
impl<'vm> Pushable<'vm> for bool {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Tag(if self { 1 } else { 0 }));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for bool {
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> bool {
        match value.as_ref() {
            ValueRef::Data(data) => data.tag() == 1,
            _ => ice!("ValueRef is not a Bool"),
        }
    }
}

impl VmType for Ordering {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        vm.find_type_info("std.types.Ordering")
            .unwrap()
            .clone()
            .into_type()
    }
}
impl<'vm> Pushable<'vm> for Ordering {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let tag = match self {
            Ordering::Less => 0,
            Ordering::Equal => 1,
            Ordering::Greater => 2,
        };
        context.push(ValueRepr::Tag(tag));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for Ordering {
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> Ordering {
        let tag = match value.as_ref() {
            ValueRef::Data(data) => data.tag(),
            _ => ice!("ValueRef is not an Ordering"),
        };
        match tag {
            0 => Ordering::Less,
            1 => Ordering::Equal,
            2 => Ordering::Greater,
            _ => ice!("Ordering has a wrong tag: {}", tag),
        }
    }
}

impl VmType for str {
    type Type = <String as VmType>::Type;
}
impl VmType for String {
    type Type = String;
}
impl<'vm, 's> Pushable<'vm> for &'s String {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&str as Pushable>::push(self, context)
    }
}

impl<'vm, 's> Pushable<'vm> for &'s str {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let thread = context.thread();
        let s = unsafe {
            GcStr::from_utf8_unchecked(context.context().alloc_with(thread, self.as_bytes())?)
        };
        context.push(ValueRepr::String(s));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for String {
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> String {
        match value.as_ref() {
            ValueRef::String(i) => String::from(&i[..]),
            _ => ice!("ValueRef is not a String"),
        }
    }
}
impl<'vm> Pushable<'vm> for String {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&str as Pushable>::push(&self, context)
    }
}

impl VmType for char {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for char {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Int(self as VmInt));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for char {
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> char {
        match value.as_ref() {
            ValueRef::Int(x) => match ::std::char::from_u32(x as u32) {
                Some(ch) => ch,
                None => ice!("Failed conversion from Int to char for: {}", x),
            },
            _ => ice!(
                "expected ValueRef to be an Int (char), got {:?}",
                value.as_ref()
            ),
        }
    }
}

impl<'s, T: VmType> VmType for Ref<'s, T> {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<'s, 'vm, T> Pushable<'vm> for Ref<'s, T>
where
    for<'t> &'t T: Pushable<'vm>,
    T: VmType,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&T as Pushable>::push(&*self, context)
    }
}

impl<'vm, 's, T> Pushable<'vm> for &'s [T]
where
    T: Traverseable + Pushable<'vm> + 's,
    &'s [T]: DataDef<Value = ValueArray>,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let thread = context.thread();
        let result = context.context().alloc_with(thread, self)?;
        context.push(ValueRepr::Array(result));
        Ok(())
    }
}
impl<'vm, 'value, T: Copy + ArrayRepr> Getable<'vm, 'value> for &'value [T] {
    fn from_value(_vm: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::Array(ptr) => ptr.as_slice().unwrap(),
            _ => ice!("ValueRef is not an Array"),
        }
    }
}

impl<T> VmType for [T]
where
    T: VmType,
    T::Type: Sized,
{
    type Type = Vec<T::Type>;

    fn make_type(thread: &Thread) -> ArcType {
        <Vec<T> as VmType>::make_type(thread)
    }
}

impl<T> VmType for Vec<T>
where
    T: VmType,
    T::Type: Sized,
{
    type Type = Vec<T::Type>;

    fn make_type(thread: &Thread) -> ArcType {
        thread.global_env().type_cache().array(T::make_type(thread))
    }
}

impl<'vm, T> Pushable<'vm> for Vec<T>
where
    T: Pushable<'vm>,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let len = self.len() as VmIndex;
        for v in self {
            if v.push(context) == Err(Error::Message("Push error".into())) {
                return Err(Error::Message("Push error".into()));
            }
        }
        let thread = context.thread();
        let result = {
            let Context {
                ref mut gc,
                ref stack,
                ..
            } = *context.context();
            let values = &stack[stack.len() - len..];
            thread::alloc(gc, thread, stack, ArrayDef(values))?
        };
        for _ in 0..len {
            context.pop();
        }
        context.push(ValueRepr::Array(result));
        Ok(())
    }
}

impl<'vm, 'value, T: Getable<'vm, 'value>> Getable<'vm, 'value> for Vec<T> {
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Vec<T> {
        match value.as_ref() {
            ValueRef::Array(data) => data.iter().map(|v| T::from_value(vm, v)).collect(),
            _ => panic!("Expected array"),
        }
    }
}

impl<'s, T: VmType> VmType for *const T {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<'vm, 'value, T: vm::Userdata> Getable<'vm, 'value> for *const T {
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> *const T {
        match value.as_ref() {
            ValueRef::Userdata(data) => {
                let x = data.downcast_ref::<T>().unwrap();
                x as *const T
            }
            _ => ice!("ValueRef is not an Userdata"),
        }
    }
}

impl<'s, T: VmType> VmType for Box<T> {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<'vm, 'value, T: Getable<'vm, 'value>> Getable<'vm, 'value> for Box<T> {
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Box<T> {
        Box::new(T::from_value(vm, value))
    }
}

impl<K, V> VmType for BTreeMap<K, V>
where
    K: VmType,
    K::Type: Sized,
    V: VmType,
    V::Type: Sized,
{
    type Type = BTreeMap<K::Type, V::Type>;

    fn make_type(vm: &Thread) -> ArcType {
        let map_alias = vm
            .find_type_info("std.map.Map")
            .unwrap()
            .clone()
            .into_type();
        Type::app(map_alias, collect![K::make_type(vm), V::make_type(vm)])
    }
}

impl<'vm, K, V> Pushable<'vm> for BTreeMap<K, V>
where
    K: Borrow<str> + VmType,
    K::Type: Sized,
    V: for<'vm2> Pushable<'vm2> + VmType,
    V::Type: Sized,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let thread = context.thread();
        type Map<V2> = OpaqueValue<RootedThread, BTreeMap<String, V2>>;
        let mut map: Map<V> = thread.get_global("std.map.empty")?;
        let mut insert: OwnedFunction<fn(String, V, Map<V>) -> Map<V>> =
            thread.get_global("std.json.de.insert_string")?;

        context.drop();
        for (key, value) in self {
            map = insert.call(key.borrow().to_string(), value, map)?;
        }
        context.restore();

        map.push(context)
    }
}

impl<'vm, 'value, K, V> Getable<'vm, 'value> for BTreeMap<K, V>
where
    K: Getable<'vm, 'value> + Ord,
    V: Getable<'vm, 'value>,
{
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        fn build_map<'vm2, 'value2, K2, V2>(
            map: &mut BTreeMap<K2, V2>,
            vm: &'vm2 Thread,
            value: Variants<'value2>,
        ) where
            K2: Getable<'vm2, 'value2> + Ord,
            V2: Getable<'vm2, 'value2>,
        {
            match value.as_ref() {
                ValueRef::Data(data) => if data.tag() == 1 {
                    let key = K2::from_value(vm, data.get_variant(0).expect("key"));
                    let value = V2::from_value(vm, data.get_variant(1).expect("value"));
                    map.insert(key, value);

                    let left = data.get_variant(2).expect("left");
                    build_map(map, vm, left);

                    let right = data.get_variant(3).expect("right");
                    build_map(map, vm, right);
                },
                _ => ice!("ValueRef is not a Map"),
            }
        }

        let mut map = BTreeMap::new();
        build_map(&mut map, vm, value);
        map
    }
}

impl<T: VmType> VmType for Option<T>
where
    T::Type: Sized,
{
    type Type = Option<T::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let option_alias = vm
            .find_type_info("std.types.Option")
            .unwrap()
            .clone()
            .into_type();
        Type::app(option_alias, collect![T::make_type(vm)])
    }
}

impl<'vm, T: Pushable<'vm>> Pushable<'vm> for Option<T> {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        match self {
            Some(value) => {
                let len = context.stack().len();
                value.push(context)?;
                let arg = [context.pop().get_value()];
                let thread = context.thread();
                let value = context.context().new_data(thread, 1, &arg)?;
                assert!(context.stack().len() == len);
                context.push(value);
            }
            None => context.push(ValueRepr::Tag(0)),
        }
        Ok(())
    }
}
impl<'vm, 'value, T: Getable<'vm, 'value>> Getable<'vm, 'value> for Option<T> {
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Option<T> {
        match value.as_ref() {
            ValueRef::Data(data) => if data.tag() == 0 {
                None
            } else {
                Some(T::from_value(vm, data.get_variant(0).unwrap()))
            },
            _ => ice!("ValueRef is not an Option"),
        }
    }
}

impl<T: VmType, E: VmType> VmType for StdResult<T, E>
where
    T::Type: Sized,
    E::Type: Sized,
{
    type Type = StdResult<T::Type, E::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let result_alias = vm
            .find_type_info("std.types.Result")
            .unwrap()
            .clone()
            .into_type();
        Type::app(result_alias, collect![E::make_type(vm), T::make_type(vm)])
    }
}

impl<'vm, T: Pushable<'vm>, E: Pushable<'vm>> Pushable<'vm> for StdResult<T, E> {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let tag = match self {
            Ok(ok) => {
                ok.push(context)?;
                1
            }
            Err(err) => {
                err.push(context)?;
                0
            }
        };
        let data = {
            let value = context.pop().get_value();
            let thread = context.thread();
            context.context().alloc_with(
                thread,
                Def {
                    tag: tag,
                    elems: &[value],
                },
            )?
        };
        context.push(ValueRepr::Data(data));
        Ok(())
    }
}

impl<'vm, 'value, T: Getable<'vm, 'value>, E: Getable<'vm, 'value>> Getable<'vm, 'value>
    for StdResult<T, E>
{
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> StdResult<T, E> {
        match value.as_ref() {
            ValueRef::Data(data) => match data.tag() {
                0 => Err(E::from_value(vm, data.get_variant(0).unwrap())),
                1 => Ok(T::from_value(vm, data.get_variant(0).unwrap())),
                _ => ice!("ValueRef has a wrong tag: {}", data.tag()),
            },
            _ => ice!("ValueRef is not a StdResult"),
        }
    }
}

/// Wrapper around a `Future` which can be used as a return value to let the virtual machine know
/// that it must resolve the `Future` to receive the value.
pub struct FutureResult<F>(pub F);

impl<F> FutureResult<F> {
    #[inline]
    pub fn new<'vm>(f: F) -> Self
    where
        F: Future<Error = Error> + Send + 'static,
        F::Item: Pushable<'vm>,
    {
        FutureResult(f)
    }
}

impl<F> VmType for FutureResult<F>
where
    F: Future,
    F::Item: VmType,
{
    type Type = <F::Item as VmType>::Type;
    fn make_type(vm: &Thread) -> ArcType {
        <F::Item>::make_type(vm)
    }
    fn extra_args() -> VmIndex {
        <F::Item>::extra_args()
    }
}

impl<'vm, F> AsyncPushable<'vm> for FutureResult<F>
where
    F: Future<Error = Error> + Send + 'static,
    F::Item: Pushable<'vm>,
{
    fn async_push(self, context: &mut ActiveThread<'vm>, lock: Lock) -> Result<Async<()>> {
        unsafe {
            context.context().return_future(self.0, lock);
        }
        Ok(Async::Ready(()))
    }
}

pub enum RuntimeResult<T, E> {
    Return(T),
    Panic(E),
}

impl<T, E> From<StdResult<T, E>> for RuntimeResult<T, E> {
    fn from(result: StdResult<T, E>) -> RuntimeResult<T, E> {
        match result {
            Ok(ok) => RuntimeResult::Return(ok),
            Err(err) => RuntimeResult::Panic(err),
        }
    }
}

impl<T: VmType, E> VmType for RuntimeResult<T, E> {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}
impl<'vm, T: Pushable<'vm>, E: fmt::Display> Pushable<'vm> for RuntimeResult<T, E> {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        match self {
            RuntimeResult::Return(value) => value.push(context),
            RuntimeResult::Panic(err) => Err(Error::Message(format!("{}", err))),
        }
    }
}

impl<T> VmType for IO<T>
where
    T: VmType,
    T::Type: Sized,
{
    type Type = IO<T::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let env = vm.global_env().get_env();
        let alias = env.find_type_info("IO").unwrap().into_owned();
        Type::app(alias.into_type(), collect![T::make_type(vm)])
    }
    fn extra_args() -> VmIndex {
        1
    }
}

impl<'vm, 'value, T: Getable<'vm, 'value>> Getable<'vm, 'value> for IO<T> {
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> IO<T> {
        IO::Value(T::from_value(vm, value))
    }
}

impl<'vm, T: Pushable<'vm>> Pushable<'vm> for IO<T> {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        match self {
            IO::Value(value) => value.push(context),
            IO::Exception(exc) => Err(Error::Message(exc)),
        }
    }
}

impl<'vm> Pushable<'vm> for Variants<'vm> {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(self);
        Ok(())
    }
}

impl<'vm, T> Pushable<'vm> for RootedValue<T>
where
    T: Deref<Target = Thread>,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let value = {
            let thread = context.thread();
            let full_clone = !thread.can_share_values_with(context.gc(), self.vm());
            let mut cloner = Cloner::new(thread, context.gc());
            if full_clone {
                cloner.force_full_clone();
            }
            cloner.deep_clone(&self.get_value())?
        };
        context.push(value);
        Ok(())
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for RootedValue<T>
where
    T: Deref<Target = Thread> + VmRoot<'vm>,
{
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        vm.root_value(value)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ArrayRef<'vm>(&'vm ValueArray);

impl<'vm> ArrayRef<'vm> {
    pub fn get(&self, index: usize) -> Option<Variants<'vm>> {
        if index < self.0.len() {
            Some(self.0.get(index))
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn as_slice<T>(&self) -> Option<&'vm [T]>
    where
        T: ArrayRepr + Copy,
    {
        self.0.as_slice()
    }

    pub fn iter(&self) -> ::value::Iter<'vm> {
        self.0.iter()
    }
}

pub type Array<'vm, T> = OpaqueValue<&'vm Thread, [T]>;

/// Newtype which can be used to push types implementating `AsRef`
pub struct PushAsRef<T, R: ?Sized>(T, PhantomData<R>);

impl<T, R: ?Sized> PushAsRef<T, R> {
    pub fn new(value: T) -> PushAsRef<T, R> {
        PushAsRef(value, PhantomData)
    }
}

impl<T, R: ?Sized> VmType for PushAsRef<T, R>
where
    T: AsRef<R>,
    R: 'static,
    &'static R: VmType,
{
    type Type = <&'static R as VmType>::Type;

    fn make_type(thread: &Thread) -> ArcType {
        <&'static R as VmType>::make_type(thread)
    }
}

impl<'vm, T, R: ?Sized> Pushable<'vm> for PushAsRef<T, R>
where
    T: AsRef<R>,
    for<'a> &'a R: Pushable<'vm>,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        self.0.as_ref().push(context)
    }
}

macro_rules! define_tuple {
    ($($id: ident)+) => {
        impl<$($id),+> VmType for ($($id),+)
        where $($id: VmType),+,
              $($id::Type: Sized),+
        {
            type Type = ($($id::Type),+);

            fn make_type(vm: &Thread) -> ArcType {
                let type_cache = vm.global_env().type_cache();
                type_cache.tuple(
                    &mut Symbols::new(),
                    vec![$( $id::make_type(vm) ),+]
                )
            }
        }

        #[allow(non_snake_case)]
        impl<'vm, 'value, $($id: Getable<'vm, 'value>),+> Getable<'vm, 'value> for ($($id),+) {
            #[allow(unused_assignments)]
            fn from_value(vm: &'vm Thread, value: Variants<'value>) -> ($($id),+) {
                match value.as_ref() {
                    ValueRef::Data(v) => {
                        assert!(v.len() == count!($($id),+));
                        let mut i = 0;
                        ( $(
                            { let a = $id::from_value(vm, v.get_variant(i).unwrap()); i += 1; a }
                        ),+ )
                    }
                    _ => ice!("ValueRef is not a Tuple"),
                }
            }
        }

        #[allow(non_snake_case)]
        impl<'vm, $($id),+> Pushable<'vm> for ($($id),+)
        where $($id: Pushable<'vm>),+
        {
            fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
                let ( $($id),+ ) = self;
                $(
                    $id.push(context)?;
                )+
                let len = count!($($id),+);
                let thread = context.thread();
                let context = context.context();
                let offset = context.stack.len() - len;
                let value = thread::alloc(&mut context.gc,
                                          thread,
                                          &context.stack,
                                          Def {
                                              tag: 0,
                                              elems: &context.stack[offset..],
                                          })?;
                for _ in 0..len {
                    context.stack.pop();
                }
                context.stack.push(ValueRepr::Data(value));
                Ok(())
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
define_tuples! { A B C D E F G H I J K L }

pub struct Map<K, V>(PhantomData<(K, V)>);

impl<K: VmType, V: VmType> VmType for Map<K, V>
where
    K::Type: Sized,
    V::Type: Sized,
{
    type Type = Map<K::Type, V::Type>;

    fn make_type(vm: &Thread) -> ArcType {
        let map_alias = vm
            .find_type_info("std.map.Map")
            .unwrap()
            .clone()
            .into_type();
        Type::app(map_alias, collect![K::make_type(vm), V::make_type(vm)])
    }
}

/// A value that has already been pushed to the stack
pub(crate) struct Pushed<T>(PhantomData<T>);

impl<T> Default for Pushed<T> {
    fn default() -> Self {
        Pushed(PhantomData)
    }
}

impl<T: VmType> VmType for Pushed<T> {
    type Type = T::Type;

    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }

    fn make_forall_type(vm: &Thread) -> ArcType {
        T::make_forall_type(vm)
    }

    fn extra_args() -> VmIndex {
        T::extra_args()
    }
}

impl<'vm, T: VmType> Pushable<'vm> for Pushed<T> {
    fn push(self, _context: &mut ActiveThread<'vm>) -> Result<()> {
        Ok(())
    }
}
