extern crate gluon_base;

use gluon_base::{
    ast::{Arena, Expr, RootExpr},
    mk_ast_arena, pos,
};

fn main() {
    mk_ast_arena!(arena1);
    mk_ast_arena!(arena2);
    //~^ `tag` does not live long enough [E0597]

    let arena2_expr = arena2.alloc(pos::spanned(
        //~^ `arena2` does not live long enough [E0597]
        Default::default(),
        Expr::<String>::Error(None),
    ));

    // Should fail
    RootExpr::new(arena1, arena2_expr);
}
