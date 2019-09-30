use support::*;

mod support;

use gluon::{self, query::Compilation, vm::core::tests::check_expr_eq, ThreadExt};

#[test]
fn inline_cross_module() {
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
        .unwrap_or_else(|err| panic!("{}", err));
    let expected_str = r#"
        3
    "#;
    check_expr_eq(core_expr.value.expr(), expected_str);
}
