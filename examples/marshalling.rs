#[macro_use]
extern crate gluon_codegen;
#[macro_use]
extern crate gluon_vm;

#[macro_use]
extern crate serde_derive;

use std::{collections::HashMap, sync::Arc};

use gluon::{
    base::types::{AppVec, ArcType, Type},
    import, new_vm,
    vm::{
        self,
        api::{
            self,
            generic::{A, L, R},
            ActiveThread, FunctionRef, Getable, Hole, OpaqueRef, OpaqueValue, Pushable,
            UserdataValue, ValueRef, VmType, IO,
        },
        ExternModule, Variants,
    },
    Result, RootedThread, Thread, ThreadExt,
};

#[derive(Debug, Deserialize, Serialize)]
enum Enum {
    A,
    B(i32),
    C(String, String),
}

impl api::VmType for Enum {
    type Type = Self;
    fn make_type(thread: &Thread) -> ArcType {
        thread
            .find_type_info("examples.enum.Enum")
            .unwrap_or_else(|err| panic!("{}", err))
            .clone()
            .into_type()
    }
}

impl<'vm, 'value> api::Pushable<'vm> for Enum {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> vm::Result<()> {
        api::ser::Ser(self).vm_push(context)
    }
}

impl<'vm, 'value> api::Getable<'vm, 'value> for Enum {
    impl_getable_simple!();
    fn from_value(thread: &'vm Thread, value: vm::Variants<'value>) -> Self {
        api::de::De::from_value(thread, value).0
    }
}

field_decl! { unwrap_b, value, key }

// we define Either with type parameters, just like in Gluon
#[derive(Getable, Pushable, VmType)]
enum Either<L, R> {
    Left(L),
    Right(R),
}

fn marshal_enum(thread: &Thread) -> Result<()> {
    let enum_source = api::typ::make_source::<Enum>(&thread)?;
    thread.load_script("examples.enum", &enum_source)?;

    let source = r#"
        let { Enum } = import! "examples/enum.glu"

        let unwrap_b x =
            match x with
            | B y -> y
            | _ -> error "Expected B"

        {
            unwrap_b,
            value = C "hello" "world"
        }
    "#;
    type SourceType<'vm> = record_type! {
        unwrap_b => api::FunctionRef<'vm, fn (Enum) -> i32>,
        value => Enum,
    };
    let (record_p! { mut unwrap_b, value, }, _) =
        thread.run_expr::<SourceType>("example", source)?;
    match value {
        Enum::C(ref a, ref b) => {
            assert_eq!(a, "hello");
            assert_eq!(b, "world");
            println!("`value` evaluated to: {:?}", value)
        }
        _ => panic!("Unexpected result returned"),
    }

    let x = unwrap_b.call(Enum::B(123))?;
    assert_eq!(x, 123);
    println!("`unwrap_b` returned: {}", x);

    Ok(())
}

fn marshal_map<I>(thread: &Thread, iterable: I) -> Result<()>
where
    I: IntoIterator<Item = (String, String)>,
{
    // Load std.map so that we can retrieve the `Map` type through the `VmType` trait
    thread.run_expr::<()>("example", "let _ = import! std.map in ()")?;

    let config_example = r#"
        let array = import! std.array
        let map @ { Map } = import! std.map

        let run config_array =
            let f m entry : Map String String -> (String, String) -> _ =
                map.insert entry._0 entry._1 m
            array.foldable.foldl f map.empty config_array
        run
        "#;
    let mut make_map: FunctionRef<
        fn(Vec<(String, String)>) -> OpaqueValue<RootedThread, api::Map<String, String>>,
    > = thread.run_expr("example", config_example)?.0;

    let entries: Vec<_> = iterable.into_iter().collect();
    let map = make_map.call(entries)?;

    let config_query_example = r#"
        let map = import! std.map

        let run config_map =
            (map.find "key" config_map, map.find "undefined" config_map)
        run
        "#;
    let mut query_map: FunctionRef<
        fn(OpaqueValue<RootedThread, api::Map<String, String>>) -> (Option<String>, Option<String>),
    > = thread.run_expr("example", config_query_example)?.0;

    let tuple = query_map.call(map)?;
    assert_eq!(tuple, (Some("value".to_string()), None));
    println!("Querying the map returned: {:?}", tuple);

    Ok(())
}

// the function takes an Either instantiated with the `Opaque*` struct,
// which will handle the generic Gluon values for us.
//
// We use the `OpaqueRef` alias here since we only need temporary (borrowed) access and it avoids
// the cost of reference counted rooting.
fn flip<'a>(
    either: Either<OpaqueRef<'a, L>, OpaqueRef<'a, R>>,
) -> Either<OpaqueRef<'a, R>, OpaqueRef<'a, L>> {
    match either {
        Either::Left(val) => Either::Right(val),
        Either::Right(val) => Either::Left(val),
    }
}

fn marshal_generic(thread: &Thread) -> Result<()> {
    thread.get_database_mut().run_io(true);

    // define the gluon type that maps to the rust Either
    let src = r#"
        type Either l r = | Left l | Right r
        { Either }
    "#;

    // load the type and then the module containing the rust function
    fn load_mod(thread: &Thread) -> vm::Result<ExternModule> {
        let module = record! {
            flip => primitive!(1, flip),
        };

        ExternModule::new(thread, module)
    }

    thread.load_script("examples.either", src)?;
    import::add_extern_module(&thread, "examples.either.prim", load_mod);

    let script = r#"
        let { Either } = import! examples.either
        let { flip } = import! examples.either.prim
        let { (<>) } = import! std.semigroup
        let io @ { flat_map } = import! std.io

        // Either is defined as:
        // type Either l r = | Left l | Right r
        let either: forall r . Either String r = Left "hello rust!"

        // we can pass the generic Either to the Rust function without an issue
        seq
            match flip either with
            | Left _ -> error "unreachable!"
            | Right val -> io.println ("Right is: " <> val)

        // using an Int instead also works
        let either: forall r . Either Int r = Left 42

        match flip either with
        | Left _ -> error "also unreachable!"
        | Right 42 -> io.println "this is the right answer"
        | Right _ -> error "wrong answer!"
    "#;

    thread.run_expr::<IO<()>>("example", script)?;

    Ok(())
}

// if this were a foreign type, we would not be able to
// directly implement traits for it
#[derive(Debug)]
struct User<T> {
    name: String,
    age: u32,
    data: T,
}

// but it's possible to wrap it and manually implement traits for it
struct GluonUser<T> {
    inner: User<T>,
}

impl<T> VmType for GluonUser<T>
where
    T: 'static + VmType,
{
    type Type = Self;

    fn make_type(thread: &Thread) -> ArcType {
        // get the type defined in Gluon
        let ty = thread
            .find_type_info("examples.wrapper.User")
            .expect("Could not find type")
            .into_type();

        // apply all generic parameters to the type
        let mut vec = AppVec::new();
        vec.push(T::make_type(thread));
        Type::app(ty, vec)
    }
}

impl<'vm, T> Pushable<'vm> for GluonUser<T>
where
    T: Pushable<'vm>,
{
    fn vm_push(self, ctx: &mut ActiveThread<'vm>) -> vm::Result<()> {
        (record! {
            name => self.inner.name,
            age => self.inner.age,
            data => self.inner.data,
        })
        .vm_push(ctx)
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for GluonUser<T>
where
    T: Getable<'vm, 'value>,
{
    impl_getable_simple!();

    fn from_value(thread: &'vm Thread, data: Variants<'value>) -> GluonUser<T> {
        // get the data, it must be a complex type
        let data = match data.as_ref() {
            ValueRef::Data(data) => data,
            _ => panic!("Value is not a complex type"),
        };

        GluonUser {
            inner: User {
                // lookup the fields by name; in case of a tuple variant we
                // would use Data::get_variant instead
                name: String::from_value(thread, data.lookup_field(thread, "name").unwrap()),
                age: u32::from_value(thread, data.lookup_field(thread, "age").unwrap()),
                data: T::from_value(thread, data.lookup_field(thread, "data").unwrap()),
            },
        }
    }
}

fn marshal_wrapper(thread: &Thread) -> Result<()> {
    let src = r#"
        type User a = { name: String, age: Int, data: a }
        { User }
    "#;

    fn load_mod(thread: &Thread) -> vm::Result<ExternModule> {
        let module = record! {
            roundtrip => primitive!(1, |user: GluonUser<OpaqueValue<RootedThread, A>>| {
                println!("name: {}, age: {}", user.inner.name, user.inner.age);
                user
            }),
        };

        ExternModule::new(thread, module)
    }

    thread.load_script("examples.wrapper", src)?;
    import::add_extern_module(&thread, "examples.wrapper.prim", load_mod);

    let script = r#"
        let { User } = import! examples.wrapper
        let { roundtrip } = import! examples.wrapper.prim
        let { assert } = import! std.test

        let actual = { name = "Bob", age = 11, data = True }
        let expected = roundtrip actual

        let _  = assert (actual.name == expected.name)
        let _  = assert (actual.age == expected.age)
        assert (actual.data == expected.data)
    "#;

    thread.run_expr::<()>("example", script)?;

    Ok(())
}

#[derive(Userdata, Trace, Clone, Debug, VmType)]
#[gluon_userdata(clone)]
// Lets gluon know that the value can be cloned which can be needed when transferring the value between threads
#[gluon(vm_type = "WindowHandle")]
struct WindowHandle {
    id: Arc<u64>,
    metadata: Arc<str>,
}

fn load_mod(thread: &gluon::Thread) -> vm::Result<ExternModule> {
    thread.register_type::<WindowHandle>("WindowHandle", &[])?;

    let module = record! {
        type WindowHandle => WindowHandle,
        create_hwnd => primitive!(2, create_hwnd),
        id => primitive!(1, id),
        metadata => primitive!(1, metadata),
        default_hwnd => create_hwnd(0, "default".into()),
    };

    ExternModule::new(thread, module)
}

fn create_hwnd(id: u64, metadata: String) -> WindowHandle {
    WindowHandle {
        id: Arc::new(id),
        metadata: Arc::from(metadata),
    }
}

fn id(hwnd: &WindowHandle) -> u64 {
    *hwnd.id
}

fn metadata(hwnd: &WindowHandle) -> String {
    String::from(&*hwnd.metadata)
}

fn marshal_userdata(thread: &Thread) -> Result<()> {
    gluon::import::add_extern_module(&thread, "hwnd", load_mod);

    // Load the extern module so that the next run_expr call can access the registered type
    thread.run_expr::<OpaqueValue<&Thread, Hole>>("", "import! hwnd")?;

    let script = r#"
        let { assert } = import! std.test
        let { WindowHandle, create_hwnd, id, metadata } = import! hwnd
        let hwnd : WindowHandle = create_hwnd 0 "Window1"
        let _  = assert (id hwnd == 0)
        let _  = assert (metadata hwnd == "Window1")
        hwnd
    "#;

    // `UserdataValue` lets us extract a `Clone` of its inner userdata value
    let (UserdataValue(handle), _) =
        thread.run_expr::<UserdataValue<WindowHandle>>("test", script)?;
    assert_eq!(*handle.id, 0);
    assert_eq!(&*handle.metadata, "Window1");

    // If cloning would be expansive we can instate use `OpaqueValue` to get a smart pointer to the
    // userdata which implements `Deref` for easy access
    let (handle, _) = thread.run_expr::<OpaqueValue<&Thread, WindowHandle>>("test", script)?;
    assert_eq!(*handle.id, 0);
    assert_eq!(&*handle.metadata, "Window1");
    Ok(())
}

#[derive(Debug, PartialEq, VmType, Getable)]
// Deriving `VmType` won't work for a recursive type at the moment so we need to point to a type
// specified in gluon itself
#[gluon(vm_type = "std.list.List")]
enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

fn marshal_recursive(thread: &Thread) -> Result<()> {
    // Load std.list before we try to use it in `VmType for List`
    thread.run_expr::<OpaqueValue<RootedThread, Hole>>("example", "import! std.list")?;

    let source = r#"
        let list = import! std.list
        list.of [1, 2]
        "#;
    let (list, _) = thread.run_expr::<List<i32>>("example", source)?;

    assert_eq!(list, List::Cons(1, List::Cons(2, List::Nil.into()).into()));
    println!("The list {:?}", list);
    Ok(())
}

fn marshal_json(thread: &Thread) -> Result<()> {
    let source = r#"
        let { Eff, ? } = import! std.effect
        let io @ { ? } = import! std.effect.io
        let { Lift, run_lift } = import! std.effect.lift
        let { Error, run_error, ok_or_throw } = import! std.effect.error
        let { (<|) } = import! std.function

        let { Value } = import! std.json
        let de @ { Deserialize, ? } = import! std.json.de

        #[derive(Deserialize, Show)]
        type Nested = {
            float: Float,
        }

        #[derive(Deserialize)]
        type MyValue = {
            bool: Bool,
            string: String,
            nested: Nested,
            array: Array Int,
        }
        let consumer value : Value -> Eff [| error : Error String, lift: Lift IO |] () =
            do my_value = ok_or_throw <| de.run value
            seq io.println ("bool = " ++ show my_value.bool)
            seq io.println ("string = " ++ show my_value.string)
            seq io.println ("nested = " ++ show my_value.nested)
            io.println ("array = " ++ show my_value.array)

        \value -> run_lift <| run_error <| consumer value
        "#;

    thread.run_expr::<OpaqueValue<RootedThread, Hole>>("example", "import! std.json")?;

    let (mut consumer, _) = thread.run_expr::<FunctionRef<
        fn(serde_json::Value) -> IO<std::result::Result<(), String>>,
    >>("example", source)?;
    consumer
        .call(serde_json::json! {{
            "bool": true,
            "string": "hello",
            "nested": {
                "float": 3.14,
            },
            "array": [1, 2, 3]
        }})?
        .into_result()??;

    Ok(())
}

fn main() {
    env_logger::init();
    if let Err(err) = main_() {
        eprintln!("{}", err);
        ::std::process::exit(1);
    }
}

fn main_() -> Result<()> {
    let thread = new_vm();

    marshal_enum(&thread)?;

    let mut map = HashMap::new();
    map.insert("key".to_string(), "value".to_string());
    map.insert("key2".to_string(), "value2".to_string());

    marshal_map(&thread, map)?;

    marshal_generic(&thread)?;

    marshal_wrapper(&thread)?;

    marshal_userdata(&thread)?;

    marshal_recursive(&thread)?;

    marshal_json(&thread)?;

    Ok(())
}
