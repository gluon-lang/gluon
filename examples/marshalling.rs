extern crate gluon;
#[macro_use]
extern crate gluon_vm;

extern crate env_logger;
#[macro_use]
extern crate serde_derive;

use std::collections::HashMap;

use gluon::base::types::ArcType;

use gluon::vm;
use gluon::vm::api::{self, FunctionRef, OpaqueValue};
use gluon::vm::thread::Context;

use gluon::{new_vm, Compiler, Result, RootedThread, Thread};

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
            .unwrap()
            .clone()
            .into_type()
    }
}

impl<'vm> api::Pushable<'vm> for Enum {
    fn push(self, thread: &'vm Thread, context: &mut Context) -> vm::Result<()> {
        api::ser::Ser(self).push(thread, context)
    }
}

impl<'vm> api::Getable<'vm> for Enum {
    fn from_value(thread: &'vm Thread, value: vm::Variants) -> Self {
        api::de::De::from_value(thread, value).0
    }
}

field_decl!{ unwrap_b, value, key }

fn marshal_enum() -> Result<()> {
    let thread = new_vm();

    let enum_source = api::typ::make_source::<Enum>(&thread)?;
    Compiler::new().load_script(&thread, "examples.enum", &enum_source)?;

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
    type SourceType<'thread> = record_type! {
        unwrap_b => api::FunctionRef<'thread, fn (Enum) -> i32>,
        value => Enum
    };
    let (record_p! { mut unwrap_b, value }, _) =
        Compiler::new().run_expr::<SourceType>(&thread, "example", source)?;
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

fn marshal_map<I>(iterable: I) -> Result<()>
where
    I: IntoIterator<Item = (String, String)>,
{
    let thread = new_vm();

    // Load std.map so that we can retrieve the `Map` type through the `VmType` trait
    Compiler::new().run_expr::<()>(&thread, "example", "let _ = import! std.map in ()")?;

    let config_example = r#"
        let array = import! std.array
        let string = import! std.string
        let map @ { Map } = import! std.map

        let string_map = map.make string.ord

        let run config_array =
            let f m entry : Map String String -> (String, String) -> _ =
                string_map.insert entry._0 entry._1 m
            array.foldable.foldl f string_map.empty config_array
        run
        "#;
    let mut make_map: FunctionRef<
        fn(Vec<(String, String)>) -> OpaqueValue<RootedThread, api::Map<String, String>>,
    > = Compiler::new()
        .run_expr(&thread, "example", config_example)?
        .0;

    let entries: Vec<_> = iterable.into_iter().collect();
    let map = make_map.call(entries)?;

    let config_query_example = r#"
        let string = import! std.string
        let map = import! std.map

        let string_map = map.make string.ord

        let run config_map =
            (string_map.find "key" config_map, string_map.find "undefined" config_map)
        run
        "#;
    let mut query_map: FunctionRef<
        fn(OpaqueValue<RootedThread, api::Map<String, String>>) -> (Option<String>, Option<String>),
    > = Compiler::new()
        .run_expr(&thread, "example", config_query_example)?
        .0;

    let tuple = query_map.call(map)?;
    assert_eq!(tuple, (Some("value".to_string()), None));
    println!("Querying the map returned: {:?}", tuple);

    Ok(())
}
fn main() {
    env_logger::init();

    if let Err(err) = marshal_enum() {
        eprintln!("{}", err)
    }

    let mut map = HashMap::new();
    map.insert("key".to_string(), "value".to_string());
    map.insert("key2".to_string(), "value2".to_string());

    if let Err(err) = marshal_map(map) {
        eprintln!("{}", err)
    }
}
