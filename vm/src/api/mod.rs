//! The marshalling api
use std::{
    any::Any,
    borrow::Borrow,
    cell::Ref,
    cmp::Ordering,
    collections::BTreeMap,
    ffi::{OsStr, OsString},
    fmt,
    marker::PhantomData,
    ops::Deref,
    path::{Path, PathBuf},
    result::Result as StdResult,
};

use crate::base::{
    scoped_map::ScopedMap,
    symbol::{Symbol, Symbols},
    types::{self, ArcType, Field, Type},
};
use crate::{
    forget_lifetime,
    gc::{CloneUnrooted, DataDef, GcRef, Move, Trace},
    stack::Lock,
    thread::{RootedThread, ThreadInternal, VmRoot, VmRootInternal},
    types::{VmIndex, VmInt, VmTag},
    value::{ArrayDef, ArrayRepr, ClosureData, DataStruct, Value, ValueArray, ValueRepr},
    vm::{self, RootedValue, Status, Thread},
    Error, Result, Variants,
};
use futures::{task::Poll, Future};

pub use self::{
    function::*,
    opaque::{Opaque, OpaqueRef, OpaqueValue},
    record::Record,
};
pub use crate::{thread::ActiveThread, value::Cloner, value::Userdata};

macro_rules! count {
    () => { 0 };
    ($_e: ident) => { 1 };
    ($_e: ident, $($rest: ident),*) => { 1 + count!($($rest),*) }
}

/// Implements the proxy methods, letting only `from_value` be specified
#[macro_export]
macro_rules! impl_getable_simple {
    () => {
        type Proxy = $crate::Variants<'value>;
        #[inline(always)]
        fn to_proxy(
            _vm: &'vm Thread,
            value: $crate::Variants<'value>,
        ) -> $crate::Result<Self::Proxy> {
            Ok(value)
        }
        #[inline(always)]
        fn from_proxy(vm: &'vm Thread, proxy: &'value mut Self::Proxy) -> Self {
            <Self as Getable<'vm, 'value>>::from_value(vm, proxy.clone())
        }
    };
}

#[macro_use]
pub mod mac;
pub mod function;
mod opaque;
pub mod record;
pub mod scoped;

#[cfg(feature = "serde")]
pub mod de;
#[cfg(feature = "serde")]
pub mod json;
#[cfg(feature = "serde")]
pub mod ser;
#[cfg(feature = "serde")]
pub mod typ;

#[derive(Clone, Debug)]
pub enum ValueRef<'a> {
    Byte(u8),
    Int(VmInt),
    Float(f64),
    String(&'a str),
    Data(Data<'a>),
    Array(GcRef<'a, ValueArray>),
    Userdata(&'a dyn vm::Userdata),
    Thread(&'a Thread),
    Closure(Closure<'a>),
    Internal,
}

// Need to manually implement PartialEq so that `ValueRef`'s with different lifetimes can be compared
impl<'a, 'b> PartialEq<ValueRef<'b>> for ValueRef<'a> {
    fn eq(&self, other: &ValueRef) -> bool {
        use self::ValueRef::*;

        match (self, other) {
            (Byte(l), Byte(r)) => l == r,
            (Int(l), Int(r)) => l == r,
            (Float(l), Float(r)) => l == r,
            (String(l), String(r)) => l == r,
            (Data(l), Data(r)) => l == r,
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
    #[inline]
    pub(crate) fn new(value: &'a Value) -> ValueRef<'a> {
        Variants::new(value).as_ref()
    }

    #[inline]
    pub(crate) unsafe fn rooted_new(value: &ValueRepr) -> ValueRef<'a> {
        match value {
            ValueRepr::Byte(i) => ValueRef::Byte(*i),
            ValueRepr::Int(i) => ValueRef::Int(*i),
            ValueRepr::Float(f) => ValueRef::Float(*f),
            ValueRepr::String(s) => ValueRef::String(forget_lifetime(&*s)),
            ValueRepr::Data(data) => {
                ValueRef::Data(Data(DataInner::Data(GcRef::new(forget_lifetime(data)))))
            }
            ValueRepr::Tag(tag) => ValueRef::Data(Data(DataInner::Tag(*tag))),
            ValueRepr::Array(array) => ValueRef::Array(GcRef::new(forget_lifetime(array))),
            ValueRepr::Userdata(data) => ValueRef::Userdata(forget_lifetime(&***data)),
            ValueRepr::Thread(thread) => ValueRef::Thread(forget_lifetime(&**thread)),
            ValueRepr::Closure(c) => ValueRef::Closure(Closure(forget_lifetime(&**c))),
            ValueRepr::Function(_) | ValueRepr::PartialApplication(_) => ValueRef::Internal,
        }
    }

    #[inline]
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
        crate::value::variant_iter(&self.0.upvars)
    }
    pub fn debug_info(&self) -> &crate::compiler::DebugInfo {
        &self.0.function.debug_info
    }
}

#[derive(Clone, PartialEq, Debug)]
enum DataInner<'a> {
    Tag(VmTag),
    Data(GcRef<'a, DataStruct>),
}

/// Stores values of variants and records.
#[derive(Clone, PartialEq, Debug)]
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
        match &self.0 {
            DataInner::Tag(tag) => *tag,
            DataInner::Data(data) => data.tag(),
        }
    }

    /// Returns the number of fields of this value.
    pub fn len(&self) -> usize {
        match &self.0 {
            DataInner::Tag(_) => 0,
            DataInner::Data(data) => data.fields.len(),
        }
    }

    /// Retrieves the value of the field at `index`, like `get_variant`, but does not
    /// wrap it in a `Variants` struct.
    pub fn get(&self, index: usize) -> Option<ValueRef<'a>> {
        match &self.0 {
            DataInner::Tag(_) => None,
            DataInner::Data(data) => data.as_ref().fields.get(index).map(ValueRef::new),
        }
    }

    /// Creates an iterator over the fields of this value.
    pub fn iter(&self) -> impl Iterator<Item = Variants<'a>> {
        crate::value::variant_iter(self.fields())
    }

    fn fields(&self) -> &'a [Value] {
        match &self.0 {
            DataInner::Tag(_) => &[][..],
            DataInner::Data(data) => &data.as_ref().fields,
        }
    }

    /// Retrieves the value of the field at `index`. This is useful if you cannot
    /// name the field (like in a variant). If the value is a record, use
    /// `lookup_field` instead.
    pub fn get_variant(&self, index: usize) -> Option<Variants<'a>> {
        match &self.0 {
            DataInner::Tag(_) => None,
            DataInner::Data(data) => data.as_ref().fields.get(index).map(Variants::new),
        }
    }

    /// Retrieves the field `name` from this record.
    pub fn lookup_field(&self, thread: &Thread, name: &str) -> Option<Variants<'a>> {
        match &self.0 {
            DataInner::Tag(_) => None,
            DataInner::Data(data) => data.get(thread, name).ok().and_then(|x| x),
        }
    }

    #[doc(hidden)]
    pub fn field_names(&self) -> impl Iterator<Item = &crate::interner::InternedStr> {
        match &self.0 {
            DataInner::Tag(_) => itertools::Either::Left(None.into_iter()),
            DataInner::Data(data) => itertools::Either::Right(data.field_map().keys()),
        }
    }
}

/// Marker type representing a hole
#[derive(Clone)]
pub struct Hole(());

impl VmType for Hole {
    type Type = Hole;

    fn make_type(vm: &Thread) -> ArcType {
        vm.global_env().type_cache().hole()
    }
}

/// Type representing gluon's IO type
#[derive(Debug, PartialEq, Clone)]
pub enum IO<T> {
    Value(T),
    Exception(String),
}

impl<T> IO<T> {
    pub fn into_result(self) -> StdResult<T, String> {
        self.into()
    }
}

impl<T> From<IO<T>> for StdResult<T, String> {
    fn from(io: IO<T>) -> StdResult<T, String> {
        match io {
            IO::Value(x) => Ok(x),
            IO::Exception(x) => Err(x),
        }
    }
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

#[derive(Trace, PartialEq)]
#[gluon(gluon_vm)]
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

    const EXTRA_ARGS: VmIndex = T::EXTRA_ARGS;
}
impl<'vm, T: VmType> Pushable<'vm> for Unrooted<T> {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(self.0);
        Ok(())
    }
}

pub type Generic<T> = OpaqueValue<RootedThread, T>;

/// Module containing types which represent generic variables in gluon's type system
pub mod generic {
    use super::VmType;
    use crate::base::types::ArcType;
    use crate::vm::Thread;

    macro_rules! make_generics {
        ($($i: ident)+) => {
            $(
            #[derive(Clone, Copy, PartialEq, Debug, Trace)]
            #[gluon(gluon_vm)]
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
    make_generics! {A B C D E F G H I J K L M N O P Q R S T U V X Y Z}
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
        // Avoid inserting foralls in the tuple inside the variant row
        Type::Variant(ref row) => types::walk_move_type_opt(
            row,
            &mut types::ControlVisitation(|typ: &ArcType| {
                types::walk_move_type_opt(
                    typ,
                    &mut types::ControlVisitation(|typ: &ArcType| {
                        insert_forall_walker(variables, typ)
                    }),
                )
            }),
        )
        .map(|t| ArcType::from(Type::Variant(t))),

        Type::Record(ref typ) => {
            insert_forall_walker_fields(variables, typ).map(|typ| ArcType::from(Type::Record(typ)))
        }
        _ => types::walk_move_type_opt(
            typ,
            &mut types::ControlVisitation(|typ: &ArcType| insert_forall_walker(variables, typ)),
        ),
    }
}

fn insert_forall_walker_fields(
    variables: &mut ScopedMap<Symbol, types::Generic<Symbol>>,
    typ: &ArcType,
) -> Option<ArcType> {
    match &**typ {
        Type::ExtendRow { fields, rest } => {
            let new_fields = types::walk_move_types(&mut (), fields, |_, field| {
                insert_forall(variables, &field.typ).map(|typ| Field {
                    name: field.name.clone(),
                    typ,
                })
            });
            let new_rest = insert_forall_walker_fields(variables, rest);
            base::merge::merge(fields, new_fields, rest, new_rest, Type::extend_row)
        }
        Type::ExtendTypeRow { types, rest } => insert_forall_walker_fields(variables, rest)
            .map(|rest| Type::extend_type_row(types.clone(), rest)),
        _ => None,
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
    const EXTRA_ARGS: VmIndex = 0;
}

/// Trait which allows a possibly asynchronous rust value to be pushed to the virtual machine
pub trait AsyncPushable<'vm> {
    /// Pushes `self` to `stack`. If the call is successful a single element should have been added
    /// to the stack and `Ok(())` should be returned. If the call is unsuccessful `Status:Error`
    /// should be returned and the stack should be left intact.
    ///
    /// If the value must be computed asynchronously `Poll::Pending` must be returned so that
    /// the virtual machine knows it must do more work before the value is available.
    fn async_push(
        self,
        context: &mut ActiveThread<'vm>,
        lock: Lock,
        frame_index: VmIndex,
    ) -> Poll<Result<()>>;

    fn async_status_push(
        self,
        context: &mut ActiveThread<'vm>,
        lock: Lock,
        frame_index: VmIndex,
    ) -> Status
    where
        Self: Sized,
    {
        match self.async_push(context, lock, frame_index) {
            Poll::Ready(Ok(())) => Status::Ok,
            Poll::Ready(Err(err)) => {
                let mut context = context.context();
                let msg = context.gc.alloc_ignore_limit(format!("{}", err).as_str());
                context.stack.push(Variants::from(msg));
                Status::Error
            }
            Poll::Pending => Status::Yield,
        }
    }
}

impl<'vm, T> AsyncPushable<'vm> for T
where
    T: Pushable<'vm>,
{
    fn async_push(
        self,
        context: &mut ActiveThread<'vm>,
        lock: Lock,
        _: VmIndex,
    ) -> Poll<Result<()>> {
        let result = self.vm_push(context);
        context.stack().release_lock(lock);
        Poll::Ready(result)
    }
}

/// Trait which allows a rust value to be pushed to the virtual machine
pub trait Pushable<'vm>: AsyncPushable<'vm> {
    /// Pushes `self` to `stack`. If the call is successful a single element should have been added
    /// to the stack and `Ok(())` should be returned. If the call is unsuccessful `Status:Error`
    /// should be returned and the stack should be left intact
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()>;

    fn status_push(self, context: &mut ActiveThread<'vm>) -> Status
    where
        Self: Sized,
    {
        match self.vm_push(context) {
            Ok(()) => Status::Ok,
            Err(err) => {
                let mut context = context.context();
                let msg = context.gc.alloc_ignore_limit(format!("{}", err).as_str());
                context.stack.push(Variants::from(msg));
                Status::Error
            }
        }
    }

    unsafe fn marshal_unrooted(self, vm: &'vm Thread) -> Result<Value>
    where
        Self: Sized,
    {
        let mut context = vm.current_context();
        self.vm_push(&mut context)?;
        let value = context.pop().get_value().clone_unrooted();
        Ok(value)
    }

    fn marshal<T>(self, vm: &'vm Thread) -> Result<RootedValue<T>>
    where
        Self: Sized,
        T: VmRoot<'vm>,
    {
        let mut context = vm.current_context();
        self.vm_push(&mut context)?;
        let variants = context.pop();
        Ok(vm.root_value(variants.clone()))
    }
}

/// Trait which allows rust values to be retrieved from the virtual machine
pub trait Getable<'vm, 'value>: Sized {
    type Proxy: 'value;
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self;

    fn to_proxy(vm: &'vm Thread, value: Variants<'value>) -> Result<Self::Proxy>;
    fn from_proxy(vm: &'vm Thread, proxy: &'value mut Self::Proxy) -> Self;
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
    t.vm_push(context)?;
    let thread = context.thread();
    let value = context.pop();
    Ok(U::from_value(thread, (*value).clone()))
}

impl<'vm, T: vm::Userdata> Pushable<'vm> for T {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let mut context = context.context();
        let data: Box<dyn vm::Userdata> = Box::new(self);
        let userdata = alloc!(context, Move(data))?;
        context.stack.push(Variants::from(userdata));
        Ok(())
    }
}

impl<'vm, 'value> Getable<'vm, 'value> for ValueRef<'value> {
    impl_getable_simple!();

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
    const EXTRA_ARGS: VmIndex = T::EXTRA_ARGS;
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

    const EXTRA_ARGS: VmIndex = T::EXTRA_ARGS;
}

impl<'vm, 'value, T> Getable<'vm, 'value> for UserdataValue<T>
where
    T: vm::Userdata + Clone,
{
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        UserdataValue(<&'value T as Getable<'vm, 'value>>::from_value(vm, value).clone())
    }
}

impl<'vm, T> Pushable<'vm> for UserdataValue<T>
where
    T: vm::Userdata,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        self.0.vm_push(context)
    }
}

impl<'vm, T: ?Sized + VmType> VmType for &'vm T {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

pub enum RefProxy<'value, T> {
    Lock(scoped::ReadGuard<'value, T>),
    Ref(&'value T),
}

impl<'vm, 'value, T> Getable<'vm, 'value> for &'value T
where
    T: vm::Userdata,
{
    type Proxy = RefProxy<'value, T>;

    fn to_proxy(_vm: &'vm Thread, value: Variants<'value>) -> Result<Self::Proxy> {
        match value.as_ref() {
            ValueRef::Userdata(data) => data.downcast_ref::<T>().map_or_else(
                || {
                    Ok(RefProxy::Lock(
                        data.downcast_ref::<scoped::Scoped<T, &'static ()>>()
                            .map(|s| s.read())
                            .or_else(|| {
                                data.downcast_ref::<scoped::Scoped<T, &'static mut ()>>()
                                    .map(|s| s.read())
                            })
                            .unwrap()?,
                    ))
                },
                |x| Ok(RefProxy::Ref(x)),
            ),
            x => ice!("ValueRef is not an Userdata: {:?}", x),
        }
    }
    fn from_proxy(_vm: &'vm Thread, proxy: &'value mut Self::Proxy) -> Self {
        match proxy {
            RefProxy::Lock(v) => &*v,
            RefProxy::Ref(v) => v,
        }
    }
    // Only allow the unsafe version to be used
    fn from_value(_vm: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::Userdata(data) => data.downcast_ref::<T>().unwrap(),
            _ => ice!("ValueRef is not an Userdata"),
        }
    }
}

impl<'vm, T: ?Sized + VmType> VmType for &'vm mut T {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for &'value mut T
where
    T: vm::Userdata,
{
    type Proxy = scoped::WriteGuard<'value, T>;

    fn to_proxy(_vm: &'vm Thread, value: Variants<'value>) -> Result<Self::Proxy> {
        match value.as_ref() {
            ValueRef::Userdata(data) => Ok(data
                .downcast_ref::<scoped::Scoped<T, &'static mut ()>>()
                .unwrap()
                .write()?),
            _ => ice!("ValueRef is not an Userdata"),
        }
    }
    fn from_proxy(_vm: &'vm Thread, proxy: &'value mut Self::Proxy) -> Self {
        proxy
    }
    // Only allow the unsafe version to be used
    fn from_value(_vm: &'vm Thread, _value: Variants<'value>) -> Self {
        panic!("Mutable references can only be created via proxies")
    }
}

impl<'vm, 'value> Getable<'vm, 'value> for &'value str {
    impl_getable_simple!();

    fn from_value(_vm: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::String(ref s) => s,
            _ => ice!("ValueRef is not a String: {:?}", value),
        }
    }
}

impl<'vm, 'value> Getable<'vm, 'value> for &'value Path {
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        Path::new(<&'value str>::from_value(vm, value))
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

    const EXTRA_ARGS: VmIndex = T::EXTRA_ARGS;
}

impl<'vm, T> Pushable<'vm> for WithVM<'vm, T>
where
    T: Pushable<'vm>,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        self.value.vm_push(context)
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for WithVM<'vm, T>
where
    T: Getable<'vm, 'value>,
{
    type Proxy = T::Proxy;

    fn to_proxy(vm: &'vm Thread, value: Variants<'value>) -> Result<Self::Proxy> {
        T::to_proxy(vm, value)
    }
    fn from_proxy(vm: &'vm Thread, proxy: &'value mut Self::Proxy) -> Self {
        WithVM {
            vm,
            value: T::from_proxy(vm, proxy),
        }
    }

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> WithVM<'vm, T> {
        let t = T::from_value(vm, value);
        WithVM { vm, value: t }
    }
}

impl VmType for () {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for () {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Int(0));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for () {
    impl_getable_simple!();

    fn from_value(_: &'vm Thread, _: Variants) -> () {
        ()
    }
}

impl VmType for u8 {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for u8 {
    #[inline]
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Byte(self));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for u8 {
    impl_getable_simple!();

    #[inline]
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
            #[inline]
            fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
                context.push(ValueRepr::Int(self as VmInt));
                Ok(())
            }
        }
        impl<'vm, 'value> Getable<'vm, 'value> for $id {
            impl_getable_simple!();

            #[inline]
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

int_impls! { i16 i32 i64 u16 u32 u64 usize isize }

impl VmType for f64 {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for f64 {
    #[inline]
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Float(self));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for f64 {
    impl_getable_simple!();

    #[inline]
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> f64 {
        match value.as_ref() {
            ValueRef::Float(f) => f,
            _ => ice!("ValueRef is not a Float"),
        }
    }
}

impl VmType for f32 {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for f32 {
    #[inline]
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Float(self as f64));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for f32 {
    impl_getable_simple!();

    #[inline]
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::Float(f) => f as f32,
            _ => ice!("ValueRef is not a Float"),
        }
    }
}

impl VmType for bool {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        vm.get_env()
            .find_type_info("std.types.Bool")
            .unwrap()
            .clone()
            .into_type()
    }
}
impl<'vm> Pushable<'vm> for bool {
    #[inline]
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Tag(if self { 1 } else { 0 }));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for bool {
    impl_getable_simple!();

    #[inline]
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
    #[inline]
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
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
    #[inline]
    impl_getable_simple!();

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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&str as Pushable>::vm_push(self, context)
    }
}

impl<'vm, 's> Pushable<'vm> for &'s str {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let mut context = context.context();
        let s = alloc!(context, self)?;
        context.stack.push(Variants::from(s));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for String {
    impl_getable_simple!();

    fn from_value(_: &'vm Thread, value: Variants<'value>) -> String {
        match value.as_ref() {
            ValueRef::String(i) => String::from(&i[..]),
            _ => ice!("ValueRef is not a String: {:?}", value),
        }
    }
}
impl<'vm> Pushable<'vm> for String {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&str as Pushable>::vm_push(&self, context)
    }
}

impl VmType for char {
    type Type = Self;
}
impl<'vm> Pushable<'vm> for char {
    #[inline]
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Int(self as VmInt));
        Ok(())
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for char {
    impl_getable_simple!();

    #[inline]
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

impl VmType for Path {
    type Type = <PathBuf as VmType>::Type;
}

impl VmType for PathBuf {
    type Type = String;
}

impl<'vm, 's> Pushable<'vm> for &'s PathBuf {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&Path as Pushable>::vm_push(self, context)
    }
}

impl<'vm, 's> Pushable<'vm> for &'s Path {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        self.to_str()
            .ok_or_else(|| Error::Message("Path's must be valid UTF-8".into()))?
            .vm_push(context)
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for PathBuf {
    impl_getable_simple!();

    fn from_value(_: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::String(i) => PathBuf::from(&i[..]),
            _ => ice!("ValueRef is not a String"),
        }
    }
}
impl<'vm> Pushable<'vm> for PathBuf {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&Path as Pushable>::vm_push(&self, context)
    }
}

impl VmType for OsStr {
    type Type = <OsString as VmType>::Type;
}

impl VmType for OsString {
    type Type = String;
}

impl<'vm, 's> Pushable<'vm> for &'s OsString {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&OsStr as Pushable>::vm_push(self, context)
    }
}

impl<'vm, 's> Pushable<'vm> for &'s OsStr {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        self.to_str()
            .ok_or_else(|| Error::Message("OsStr's must be valid UTF-8".into()))?
            .vm_push(context)
    }
}
impl<'vm, 'value> Getable<'vm, 'value> for OsString {
    impl_getable_simple!();

    fn from_value(_: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::String(i) => OsString::from(&i[..]),
            _ => ice!("ValueRef is not a String"),
        }
    }
}
impl<'vm> Pushable<'vm> for OsString {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&OsStr as Pushable>::vm_push(&self, context)
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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        <&T as Pushable>::vm_push(&*self, context)
    }
}

impl<'vm, 's, T> Pushable<'vm> for &'s [T]
where
    T: Trace + Pushable<'vm> + 's,
    &'s [T]: DataDef<Value = ValueArray>,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let mut context = context.context();
        let result = alloc!(context, self)?;
        context.stack.push(Variants::from(result));
        Ok(())
    }
}
impl<'vm, 'value, T: Copy + ArrayRepr> Getable<'vm, 'value> for &'value [T] {
    impl_getable_simple!();

    fn from_value(_vm: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::Array(ptr) => ptr.as_ref().as_slice().unwrap(),
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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        Collect::new(self).vm_push(context)
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for Vec<T>
where
    T: Getable<'vm, 'value>,
{
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Vec<T> {
        Collect::<GetableIter<T>>::from_value(vm, value).collect()
    }
}

impl<'s, T: VmType> VmType for *const T {
    type Type = T::Type;
    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }
}

impl<'vm, 'value, T: vm::Userdata> Getable<'vm, 'value> for *const T {
    impl_getable_simple!();

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
    impl_getable_simple!();

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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        to_gluon_map(self, context)
    }
}

impl<'vm, 'value, K, V> Getable<'vm, 'value> for BTreeMap<K, V>
where
    K: Getable<'vm, 'value> + Ord,
    V: Getable<'vm, 'value>,
{
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        let mut map = BTreeMap::new();
        from_gluon_map(&mut map, vm, value);
        map
    }
}

fn to_gluon_map<'vm, K, V>(
    map_iter: impl IntoIterator<Item = (K, V)>,
    context: &mut ActiveThread<'vm>,
) -> Result<()>
where
    K: Borrow<str> + VmType,
    K::Type: Sized,
    V: for<'vm2> Pushable<'vm2> + VmType,
    V::Type: Sized,
{
    let thread = context.thread();
    type Map<V2> = OpaqueValue<RootedThread, BTreeMap<String, V2>>;
    let mut map: Map<V> = thread.get_global("std.map.empty")?;
    let mut insert: OwnedFunction<fn(String, V, Map<V>) -> Map<V>> =
        thread.get_global("std.map.insert_string")?;

    map = context.release_for(|| {
        for (key, value) in map_iter {
            map = insert.call(key.borrow().to_string(), value, map)?;
        }
        Ok::<_, Error>(map)
    })?;

    map.vm_push(context)
}

fn from_gluon_map<'vm2, 'value2, M, K2, V2>(map: &mut M, vm: &'vm2 Thread, value: Variants<'value2>)
where
    M: Extend<(K2, V2)>,
    K2: Getable<'vm2, 'value2> + Ord,
    V2: Getable<'vm2, 'value2>,
{
    match value.as_ref() {
        ValueRef::Data(data) => {
            if data.tag() == 1 {
                let key = K2::from_value(vm, data.get_variant(0).expect("key"));
                let value = V2::from_value(vm, data.get_variant(1).expect("value"));
                map.extend(Some((key, value)));

                let left = data.get_variant(2).expect("left");
                from_gluon_map(map, vm, left);

                let right = data.get_variant(3).expect("right");
                from_gluon_map(map, vm, right);
            }
        }
        _ => ice!("ValueRef is not a Map"),
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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        match self {
            Some(value) => {
                value.vm_push(context)?;
                context.context().push_new_data(1, 1)?;
            }
            None => context.push(ValueRepr::Tag(0)),
        }
        Ok(())
    }
}
impl<'vm, 'value, T: Getable<'vm, 'value>> Getable<'vm, 'value> for Option<T> {
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Option<T> {
        match value.as_ref() {
            ValueRef::Data(data) => {
                if data.tag() == 0 {
                    None
                } else {
                    Some(T::from_value(vm, data.get_variant(0).unwrap()))
                }
            }
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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let tag = match self {
            Ok(ok) => {
                ok.vm_push(context)?;
                1
            }
            Err(err) => {
                err.vm_push(context)?;
                0
            }
        };
        context.context().push_new_data(tag, 1)?;
        Ok(())
    }
}

impl<'vm, 'value, T: Getable<'vm, 'value>, E: Getable<'vm, 'value>> Getable<'vm, 'value>
    for StdResult<T, E>
{
    impl_getable_simple!();

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
    pub fn new<'vm>(f: F) -> Self
    where
        F: Future + Send + 'vm,
        F::Output: Pushable<'vm>,
    {
        FutureResult(f)
    }
}

impl<F> VmType for FutureResult<F>
where
    F: Future,
    F::Output: VmType,
{
    type Type = <F::Output as VmType>::Type;
    fn make_type(vm: &Thread) -> ArcType {
        <F::Output>::make_type(vm)
    }
    const EXTRA_ARGS: VmIndex = F::Output::EXTRA_ARGS;
}

impl<'vm, F> AsyncPushable<'vm> for FutureResult<F>
where
    F: Future + Send + 'vm,
    F::Output: Pushable<'vm>,
{
    fn async_push(
        self,
        context: &mut ActiveThread<'vm>,
        lock: Lock,
        frame_index: VmIndex,
    ) -> Poll<Result<()>> {
        unsafe {
            context.return_future(self.0, lock, frame_index);
        }
        Poll::Ready(Ok(()))
    }
}

#[derive(Clone)]
pub enum RuntimeResult<T, E = String> {
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

    fn make_forall_type(vm: &Thread) -> ArcType {
        T::make_forall_type(vm)
    }

    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }

    const EXTRA_ARGS: VmIndex = T::EXTRA_ARGS;
}
impl<'vm, T: Pushable<'vm>, E: fmt::Display> Pushable<'vm> for RuntimeResult<T, E> {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        match self {
            RuntimeResult::Return(value) => value.vm_push(context),
            RuntimeResult::Panic(err) => Err(Error::Message(format!("{}", err))),
        }
    }
}

impl<T, E> RuntimeResult<T, E> {
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> RuntimeResult<U, E> {
        match self {
            RuntimeResult::Return(ok) => RuntimeResult::Return(f(ok)),
            RuntimeResult::Panic(err) => RuntimeResult::Panic(err),
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
        let env = vm.get_env();
        let alias = env.find_type_info("std.io.IO").unwrap();
        Type::app(alias.into_type(), collect![T::make_type(vm)])
    }

    const EXTRA_ARGS: VmIndex = 1;
}

impl<'vm, 'value, T: Getable<'vm, 'value>> Getable<'vm, 'value> for IO<T> {
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> IO<T> {
        IO::Value(T::from_value(vm, value))
    }
}

impl<'vm, T: Pushable<'vm>> Pushable<'vm> for IO<T> {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        match self {
            IO::Value(value) => value.vm_push(context),
            IO::Exception(exc) => Err(Error::Message(exc)),
        }
    }
}

impl<'vm> Pushable<'vm> for Variants<'vm> {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(self);
        Ok(())
    }
}

impl<'vm, T> Pushable<'vm> for RootedValue<T>
where
    T: VmRootInternal,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let mut context = context.context();
        let full_clone = !context.thread.can_share_values_with(context.gc, self.vm());
        let mut cloner = Cloner::new(context.thread, context.gc);
        if full_clone {
            cloner.force_full_clone();
        }
        let value = cloner.deep_clone(&self.get_value())?;
        context.stack.push(value);
        Ok(())
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for RootedValue<T>
where
    T: Deref<Target = Thread> + VmRoot<'vm>,
{
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        vm.root_value(value)
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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        self.0.as_ref().vm_push(context)
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
            impl_getable_simple!();

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
            fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
                let ( $($id),+ ) = self;
                $(
                    $id.vm_push(context)?;
                )+
                let len = count!($($id),+);
                let thread = context.thread();
                #[allow(unused_assignments)]
                let field_names = {
                    let mut i = 0;
                    [$(thread.global_env().intern(&format!("_{}", { let _ = $id; let x = i; i += 1; x }))?),*]
                };
                context.context().push_new_record(len, &field_names)?;
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

    const EXTRA_ARGS: VmIndex = T::EXTRA_ARGS;
}

impl<'vm, T: VmType> Pushable<'vm> for Pushed<T> {
    fn vm_push(self, _context: &mut ActiveThread<'vm>) -> Result<()> {
        Ok(())
    }
}

pub struct Collect<T>(T);

impl<T> Collect<T> {
    pub fn new(iterable: T) -> Self
    where
        T: IntoIterator,
    {
        Collect(iterable)
    }
}

impl<T> VmType for Collect<T>
where
    T: IntoIterator,
    T::Item: VmType,
    <T::Item as VmType>::Type: Sized,
{
    type Type = Vec<<T::Item as VmType>::Type>;

    fn make_type(vm: &Thread) -> ArcType {
        Vec::<T::Item>::make_type(vm)
    }
}

impl<'vm, T> Pushable<'vm> for Collect<T>
where
    T: IntoIterator,
    T::Item: Pushable<'vm>,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let mut len = 0;
        for v in self.0 {
            v.vm_push(context)?;
            len += 1;
        }
        let mut context = context.context();
        let result = {
            let values = &context.stack[context.stack.len() - len..];
            alloc!(context, ArrayDef(values))?
        };
        context.stack.pop_many(len);
        context.stack.push(Variants::from(result));
        Ok(())
    }
}

impl<T> Iterator for Collect<T>
where
    T: Iterator,
{
    type Item = T::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct GetableIter<'vm, 'value, T> {
    iter: crate::value::Iter<'value>,
    vm: &'vm Thread,
    _marker: PhantomData<fn(&'vm ()) -> T>,
}

impl<'vm, 'value, T> Iterator for GetableIter<'vm, 'value, T>
where
    T: Getable<'vm, 'value>,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.iter.next().map(|value| T::from_value(self.vm, value))
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for Collect<GetableIter<'vm, 'value, T>>
where
    T: Getable<'vm, 'value>,
{
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::Array(data) => Collect::new(GetableIter {
                iter: data.as_ref().iter(),
                vm,
                _marker: PhantomData,
            }),
            _ => panic!("Expected array"),
        }
    }
}

#[derive(Default)]
pub struct Eff<R, T>(PhantomData<(R, T)>);

impl<R, T> VmType for Eff<R, T>
where
    R: VmType,
    R::Type: Sized,
    T: VmType,
    T::Type: Sized,
{
    type Type = Eff<R::Type, T::Type>;

    fn make_type(vm: &Thread) -> ArcType {
        let eff = vm
            .find_type_info("std.effect.Eff")
            .map(|alias| alias.into_type())
            .unwrap_or_else(|err| panic!("{}", err));
        Type::app(eff, collect![R::make_type(vm), T::make_type(vm)])
    }
}
