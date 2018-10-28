#[macro_use]
extern crate quick_error;
#[macro_use]
extern crate collect_mac;
extern crate env_logger;
#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_format as format;
extern crate gluon_parser as parser;

#[macro_use]
#[allow(unused_macros)]
mod support;

#[test]
fn simple_effect() {
    let _ = ::env_logger::try_init();
    let text = r#"
let any x = any x

#[implicit]
type Monad (m : Type -> Type) = {
    wrap : forall a . a -> m a,
    flat_map : forall a b . (a -> m b) -> m a -> m b,
}

let flat_map ?m : [Monad m] -> (a -> m b) -> m a -> m b = m.flat_map
let wrap ?m : [Monad m] -> a -> m a = m.wrap

type IO a = { io : a }
type Option a = | None | Some a

type VE w r = | Value w | Effect (r -> VE w r)
type Eff r a = { run_effect : forall w . (a -> VE w r) -> VE w r }
let monad_eff r : r -> Monad (Eff r) = {
    wrap = \x -> { run_effect = \k -> k x },
    flat_map = \f m -> { run_effect = \k -> m.run_effect (\v -> (f v).run_effect k) }
}

let row : { option : Monad Option, io : Monad IO | a } = any ()
let monad = monad_eff row

// Should be `Eff { option : Option | a } Int`
let option_effect : Eff { option : Monad Option | a } Int = any ()
let io_effect : Eff { io : Monad IO | a } Int = any ()

do x = option_effect
do y = io_effect
wrap (x #Int+ y)
"#;
    let result = support::typecheck(text);

    assert_req!(
        result.map(|t| t.to_string()),
        Ok("forall a .\n\
                test.Eff { option : test.Monad test.Option, io : test.Monad test.IO | a } Int".to_string())
    );
}
