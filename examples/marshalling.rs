extern crate gluon;
#[macro_use]
extern crate gluon_vm;
#[macro_use]
extern crate serde_derive;

use gluon::base::types::ArcType;

use gluon::vm;
use gluon::vm::thread::Context;
use gluon::vm::api;

use gluon::{new_vm, Compiler, Result, Thread};

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


field_decl!{ unwrap_b, value }

fn main_() -> Result<()> {
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
fn main() {
    if let Err(err) = main_() {
        println!("{}", err)
    }
}
