#![cfg(feature = "test")]
use support::*;

mod support;

use gluon::{self, query::AsyncCompilation, vm::core::tests::check_expr_eq, ThreadExt};

#[ignore]
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

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[ignore]
#[tokio::test]
async fn inline_with_record_pattern_in_module() {
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

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[ignore]
#[tokio::test]
async fn inline_across_two_modules() {
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

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[ignore]
#[tokio::test]
async fn prune_prelude() {
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

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[ignore]
#[tokio::test]
async fn prune_factorial() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
            let { (-), (*) } = import! std.num
            let { (<) } = import! std.cmp
            let { ? } = import! std.int
            let factorial n =
                if n < 2
                then 1
                else n * factorial (n - 1)
            factorial
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        rec let factorial n =
            match (#Int<) n 2 with
            | True -> 1
            | False ->
                let inline_bind = factorial ( (#Int-) n 1) in
                (#Int*) n  inline_bind
            end
        in
        factorial
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[ignore]
#[tokio::test]
async fn inline_num() {
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

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        rec let no_inline x =
            match (#Int==) x 0 with
            | True -> no_inline x
            | False -> x
            end
        in
        let inline_bind = no_inline 1
        in
        (#Int+) inline_bind 2
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[tokio::test]
#[ignore]
async fn inline_match() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
type Test = | A | B
match A with
| A -> 1
| B -> 2
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        1
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[ignore]
#[tokio::test]
async fn inline_cmp() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
let mod @ { Option } = import! tests.optimize.cmp
let m = mod.mk_ord {
    (<) = Some (\l r -> l #Int< r),
}
m.(<)
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        rec let lt l r = (#Int<) l r
        in lt
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}

#[ignore]
#[tokio::test]
async fn inline_option() {
    let _ = env_logger::try_init();

    let thread = make_vm();
    thread.get_database_mut().set_implicit_prelude(false);

    thread
        .load_script(
            "test",
            r#"
type Option = | None | Some Int
let f opt =
    match opt with
    | Some x -> x
    | None -> 0
f (Some 1)
        "#,
        )
        .unwrap_or_else(|err| panic!("{}", err));

    let mut db = thread.get_database();
    let core_expr = db
        .core_expr("test".into(), None)
        .await
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        1
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}
