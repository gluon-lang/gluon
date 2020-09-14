# Marshalling types

An important part of embedding Gluon is translating non-primitive types from Gluon types to
Rust types and vice versa, allowing you to seamlessly implement rich APIs with complex types.
This translation is called _marshalling_.

## Required traits

Gluon provides several traits for safely marshalling types to and from Gluon code:

- [VmType][] provides a mapping between Rust and Gluon types. It specifies the Gluon type
  the implementing Rust type represents. All types that want to cross the Gluon/Rust boundary
  must implement this trait.

- [Getable][]: Types that implement `Getable` can be marshalled from Gluon to Rust. This
  means you can use these types anywhere you are receiving values from Gluon, for example
  as parameters for a function implemented on the Rust side or as return type of a Gluon
  function you want to call from Rust.

- [Pushable][] is the counterpart to `Getable`. It allows implementing types to be marshalled
  to Gluon. Values of these types can returned from embedded Rust functions and be used as
  parameters to Gluon functions.

- [Userdata][] allows a Rust type to be marshalled as completely opaque type. The Gluon code
  will be able to receive and pass values of this type, but cannot inspect it at all. This is
  useful for passing handle-like values, that will be mostly used by the Rust code. `Pushable` is automatically implemented for all types that implement `Userdata`. `Getable` is automatically implemented for `&T where T: Userdata` when used as argument to a Rust function, for places `OpaqueValue` can be used as a smart pointer around a `Userdata` value or the `UserdataValue` extractor can be used to clone the value.

Gluon already provides implementations for the primitive and common standard library types.

## Implementing the marshalling traits for your types

You can implement all of the above traits by hand, but for most cases you can also use the
derive macros in [gluon_codegen][].

You will also have to register the correct Gluon type. If you are marshalling `Userdata`, you
can use `Thread::register_type`, otherwise you will need to provide the complete type definition
in Gluon. When using the `serialization` feature, you can automatically generate the source
code using the `api::typ::make_source` function.

### Using derive macros

Add the `gluon_codegen` crate to your `Cargo.toml` this lets you import and derive the
`VmType`, `Getable`, `Pushable` and `Userdata` traits.

`VmType`, `Getable` and `Pushable` can be implemented on any type which only consists of types which in turn implements
these traits whereas `Userdata` can be derived for any type as long as it is `Debug + Send + Sync` and has a `'static`
lifetime.

Sometimes when deriving `VmType` you do not want to define a new type. In this case you can use the `vm_type` attribute
to point to another, compatible type. See the marshalling example for the complete source for the examples below.

```rust,ignore
// Using `vm_type` to point to compatible type defined in gluon
#[derive(Debug, PartialEq, VmType, Getable)]
#[gluon(vm_type = "std.list.List")]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

// Defines an opaque type with Userdata
#[derive(Userdata, Trace, Clone, Debug, VmType)]
// Lets gluon know that the value can be cloned which can be needed when transferring the value between threads
#[gluon_userdata(clone)]
// Refers to the `WindowHandle` type registered on the Rust side
#[gluon(vm_type = "WindowHandle")]
struct WindowHandle {
    id: Arc<u64>,
    metadata: Arc<str>,
}
```

### Implementing by hand

The following examples will all assume a simple struct `User<T>`, which is defined in a different
crate (You can find the full code in the [marshalling example][]). To implement the marshalling traits,
we have to create a wrapper and implement the traits for it.

```rust,ignore
// defined by a different crate
struct User<T> {
    name: String,
    age: u32,
    data: T,
}
```

#### VmType

`VmType` requires you to specify the Rust type that maps to the correct Gluon type. You can
simply assign `Self`. The heart of the trait is the `make_type` function. To get the correct
Gluon type, you will have to look it up from the vm, using the fully qualified type name:

```rust,ignore
let ty = vm.find_type_info("examples.wrapper.User")
    .expect("Could not find type")
    .into_type();
```

If you have a non generic type, this is all you need. In our case, we will have to apply the
generic type parameters first:

```rust,ignore
let mut vec = AppVec::new();
vec.push(T::make_type(vm));
Type::app(ty, vec)
```

You simply push all parameters to the `AppVec` in the order of their declaration, and then
use `Type::app` to construct the complete type.

#### Getable

`Getable` only has one function you need to implement, `from_value`. It supplies a reference
to the vm and the raw data, from which you have to construct your type. Since we are implementing
`Getable` for a complex type, we are only interested in the `ValueRef::Data` variant.

```rust,ignore
let data = match data.as_ref() {
    ValueRef::Data(data) => data,
    _ => panic!("Value is not a complex type"),
};
```

From `data` we can now extract the individual fields, using `lookup_field` for named fields or
`get_variant` for unnamed fields (like in tuple structs or variants).

```rust,ignore
// once we have the field's value, we construct the correct type
// using its Getable implementation
let name = String::from_value(vm, data.lookup_field(vm, "name").unwrap();
```

In this example we used a struct, but if we wanted to construct an enum, we need to find out
what variant we are dealing with first, using the `tag` method:

```rust,ignore
match data.tag() {
    0 => // build first variant
    1 => // build second variant
    // ...
}
```

#### Pushable

To implement `Pushable`, we need to interact with Gluon's stack directly. The goal is to create
a `Value` that represents our Rust value, and push it on the stack. In order to do that, we need to
push the fields of our type first:

```rust,ignore
self.inner.name.push(vm, ctx)?
self.inner.age.push(vm, ctx)?;
self.inner.data.push(vm, ctx)?;
```

The `ActiveThread` we get passed has a `Context` that allows pushing values, but we can do even better and
use the `record!` macro:

```rust,ignore
(record!{
    name => self.inner.name,
    age => self.inner.age,
    data => self.inner.data,
}).push(ctx)
```

If we were pushing an enum, we would have to use `Context::push_new_data` and manually specify the tag
of the pushed variant as well as its number of fields (zero if it's a variant with no attached data).

```rust,ignore
let val = match an_enum {
    Enum::VariantOne => ctx.context().push_new_data(vm, 0, num_fields_in_variant_one),
    Enum::VariantTwo => ctx.context().push_new_data(vm, 1, num_fields_in_variant_two),
}?;
```

#### Userdata

Implementing `Userdata` is straight forward: we can either `derive` the trait or use the default
implementation since there are no required methods. However, `Userdata` also requires the type to implement
`VmType` and `Trace`. We can use the minimal `VmType` implementation, it already
provides the correct `make_type` function for us:

```rust,ignore
impl<T> VmType for GluonUser<T>
where
    T: 'static + Debug + Sync + Send
{
    type Type = Self;
}
```

The `Trace` implementation can be automatically derived in most cases as it will just call it's methods on every field
of the type. However, this means that it expects that every field also implements `Trace`, if that is not the case you
can opt out of tracing with the `#[gluon_trace(skip)]` attribute. This is fine in many cases but can cause reference
cycles if your userdata stores values managed by Gluon's GC. However if it doesn't it is safe to just use `skip`.

```rust,ignore
// Contains no gluon managed values so skipping the trace causes no issues
#[derive(Trace)]
#[gluon_trace(skip)]
struct SimpleType {
    name: String,
    slot: std::sync::Mutex<i32>,
}

// Here we store a `OpaqueValue` which is managed by gluon's GC. To avoid a reference cycle we must trace
// the field so gluon can find it. `gc::Mutex` is a drop-in replacement for `std::sync::Mutex` which is GC aware.
#[derive(Trace)]
struct Callback(gluon::vm::gc::Mutex<OpaqueValue<RootedThread, fn (i32) -> String>>);
```

## Passing values to and from Gluon

Once your type implements the [required traits](#required-traits), you can simply use it in
any function you want to expose to Gluon.

If you want to receive or return types with generic type parameters that are instantiated on
the Gluon side, you can use the [Opaque][] type together with the marker types in the
[generic][generic_mod] module:

```rust,ignore
// we define Either with type parameters, just like in Gluon
#[derive(Getable, Pushable, VmType)]
enum Either<L, R> {
    Left(L),
    Right(R),
}

// the function takes an Either instantiated with the `Opaque` struct,
// which will handle the generic Gluon values for us
use gluon::vm::api::OpaqueValue;
// The `generic` sub-module provides marker types which mimic generic parameters
use gluon::vm::api::generic::{L, R};

fn flip(
    either: Either<OpaqueValue<RootedThread, L>, OpaqueValue<RootedThread, R>>,
) -> Either<OpaqueValue<RootedThread, R>, OpaqueValue<RootedThread, L>> {
    match either {
        Either::Left(val) => Either::Right(val),
        Either::Right(val) => Either::Left(val),
    }
}
```

Now we can pass `Either` to our Rust function:

```f#,ignore
// Either is defined as:
// type Either l r = | Left l | Right r
let either: forall r . Either String r = Left "hello rust!"

// we can pass the generic Either to the Rust function without an issue
do _ =
    match flip either with
    | Left _ -> error "unreachable!"
    | Right val -> io.println ("Right is: " <> val)

// using an Int instead also works
let either: forall r . Either Int r = Left 42

match flip either with
| Left _ -> error "also unreachable!"
| Right 42 -> io.println "this is the right answer"
| Right _ -> error "wrong answer!"
```

[Getable]: https://docs.rs/gluon_vm/*/gluon_vm/api/trait.Getable.html
[Pushable]: https://docs.rs/gluon_vm/*/gluon_vm/api/trait.Pushable.html
[VmType]: https://docs.rs/gluon_vm/*/gluon_vm/api/trait.VmType.html
[Userdata]: https://docs.rs/gluon_vm/*/gluon_vm/api/trait.Userdata.html
[Opaque]: https://docs.rs/gluon_vm/*/gluon_vm/api/struct.Opaque.html
[generic_mod]: https://docs.rs/gluon_vm/*/gluon_vm/api/generic/index.html
[gluon_codegen]: https://docs.rs/gluon_codegen/0.7.1/gluon_codegen/
[marshalling example]: https://github.com/gluon-lang/gluon/blob/master/examples/marshalling.rs
