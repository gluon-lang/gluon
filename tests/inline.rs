#![cfg(features = "test")]
use support::*;

mod support;

use gluon::{self, query::Compilation, vm::core::tests::check_expr_eq, ThreadExt};

#[tokio::test]
async fn inline_cross_module() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
        let { (+) } = import! std.num
        let { ? } = import! std.int
        1 + 2
    "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let db = thread.get_database();
    let core_expr = db
        .core_expr("test".into())
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[test]
fn inline_with_record_pattern_in_module() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
let f x = x
let m1 = {
    f,
}

let m2 =
    let { f } = m1

    let num = {
        (+) = \l -> l,
    }

    {
        f,
        num,
    }

let { num } = m2
num.(+) 3
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let db = thread.get_database();
    let core_expr = db
        .core_expr("test".into())
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[test]
fn inline_across_two_modules() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
            let { (+) } = import! tests.optimize.inline_through_module
            let { ? } = import! tests.optimize.inline_through_module2
            1 + 2
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let db = thread.get_database();
    let core_expr = db
        .core_expr("test".into())
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[test]
fn prune_prelude() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
            let { (+) } = import! std.prelude
            let { ? } = import! std.int
            in 1 + 2
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let db = thread.get_database();
    let core_expr = db
        .core_expr("test".into())
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[test]
fn prune_factorial() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
            let { (-), (*), (<) } = import! std.prelude
            let { ? } = import! std.int
            let factorial n =
                if n < 2
                then 1
                else n * factorial (n - 1)
            factorial
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let db = thread.get_database();
    let core_expr = db
        .core_expr("test".into())
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        rec let factorial n =
            match (#Int<) n 2 with
            | True -> 1
            | False -> (#Int*) n (factorial ( (#Int-) n 1))
            end
        in
        factorial
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[test]
fn inline_num() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
let mod = import! tests.optimize.inline_num
let no_inline x = if x #Int== 0 then no_inline x else x
mod.(+) (no_inline 1) 2
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let db = thread.get_database();
    let core_expr = db
        .core_expr("test".into())
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}
