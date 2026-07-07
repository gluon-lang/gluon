extern crate gluon_base;

use gluon_base::{
    ast::{Arena, Expr, RootExpr},
    mk_ast_arena, pos,
};

fn main() {
    mk_ast_arena!(arena1);
    mk_ast_arena!(arena2);
    //~^ temporary value dropped while borrowed [E0716]
    //~| temporary value dropped while borrowed [E0716]

    let arena2_expr = arena2.alloc(pos::spanned(
        Default::default(),
        Expr::<String>::Error(None),
    ));

    // Should fail
    RootExpr::new(arena1, arena2_expr);
}
