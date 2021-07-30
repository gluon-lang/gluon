use gluon_codegen::Trace;

use {
    base::{
        ast::{
            self, Argument, AstClone, AstType, EmptyEnv, Expr, ExprField, Pattern, SpannedExpr,
            Typed, TypedIdent, ValueBinding,
        },
        pos::{self, BytePos, Span},
        symbol::{Symbol, SymbolData, Symbols},
        types::{self, ArcType, Type, TypeContext, TypeExt},
    },
    check::check_signature,
    vm::{
        api::{generic::A, VmType, IO},
        macros::{self, Macro, MacroExpander, MacroFuture},
    },
};

#[derive(Trace)]
#[gluon(crate_name = "vm")]
pub(crate) struct LiftIo;

impl Macro for LiftIo {
    fn expand<'r, 'a: 'r, 'b: 'r, 'c: 'r, 'ast: 'r>(
        &self,
        env: &'b mut MacroExpander<'a>,
        _symbols: &'c mut Symbols,
        arena: &'b mut ast::OwnedArena<'ast, Symbol>,
        args: &'b mut [SpannedExpr<'ast, Symbol>],
    ) -> MacroFuture<'r, 'ast> {
        Box::pin(async move {
            if args.len() != 2 {
                return Err(macros::Error::message(format!(
                    "`lift_io!` expects 2 argument"
                )));
            }

            let lift = match &args[0].value {
                Expr::Ident(id) => id.clone(),
                _ => {
                    return Err(macros::Error::message(format!(
                        "`lift_io!` expects an identifier as the first argument"
                    )))
                }
            };

            let module = &mut args[1];
            env.run_once(&mut Symbols::new(), arena, module).await;

            let typ = module.env_type_of(&EmptyEnv::default());

            match *typ {
                Type::Record(_) => (),
                _ => {
                    return Err(macros::Error::message(format!(
                        "The second argument to `lift_io!` must be a record. Found: `{}`",
                        typ
                    )))
                }
            }

            let module = (*module).ast_clone(arena.borrow());
            let span = module.span;

            let vm = env.vm;

            let sp = |e| pos::spanned(span, e);

            let mut symbols = Symbols::new();
            let module_bind = TypedIdent {
                name: symbols.symbol(SymbolData::<&str>::from("module_bind")),
                typ: typ.clone(),
            };
            let arena = arena.borrow();
            let out = sp(Expr::let_binding(
                arena,
                ValueBinding {
                    metadata: Default::default(),
                    name: pos::spanned(span, Pattern::Ident(module_bind.clone())),
                    typ: None,
                    resolved_type: typ.clone(),
                    args: &mut [],
                    expr: module,
                },
                sp(Expr::Record {
                    typ: typ.clone(),
                    types: &mut [],
                    exprs: arena.alloc_extend(
                        typ.row_iter()
                            .filter_map(|field| {
                                let mut arg_iter =
                                    field.typ.remove_forall_and_implicit_args().arg_iter();
                                let args = arg_iter.by_ref().count();

                                let action = sp(Expr::Projection(
                                    arena.alloc(sp(Expr::Ident(module_bind.clone()))),
                                    field.name.clone(),
                                    field.typ.clone(),
                                ));

                                if check_signature(
                                    &vm.get_env(),
                                    &arg_iter.typ,
                                    &IO::<A>::make_forall_type(&vm),
                                ) {
                                    let action = lift_action(
                                        arena,
                                        &mut symbols,
                                        sp(Expr::Ident(lift.clone())),
                                        action,
                                        args,
                                        &field.typ,
                                        span,
                                    );
                                    Some(ExprField {
                                        metadata: Default::default(),
                                        name: pos::spanned(span, field.name.clone()),
                                        value: Some(action),
                                    })
                                } else {
                                    None
                                }
                            })
                            .collect::<Vec<_>>(),
                    ),
                    base: Some(arena.alloc(sp(Expr::Ident(module_bind)))),
                }),
            ));

            Ok(out.into())
        })
    }
}

fn lift_action<'ast>(
    mut arena: ast::ArenaRef<'_, 'ast, Symbol>,
    symbols: &mut Symbols,
    lift: SpannedExpr<'ast, Symbol>,
    action: SpannedExpr<'ast, Symbol>,
    args: usize,
    original_type: &ArcType<Symbol>,
    span: Span<BytePos>,
) -> SpannedExpr<'ast, Symbol> {
    if args == 0 {
        pos::spanned(span, Expr::app(arena, lift, vec![action]))
    } else {
        let args = arena.alloc_extend((0..args).map(|i| {
            Argument::explicit(pos::spanned(
                span,
                TypedIdent::new(symbols.simple_symbol(format!("x{}", i))),
            ))
        }));
        let translate_type = move |t| types::translate_type(&mut arena, t);
        // If there are any implicit arguments we need to forward them to the lambda so implicits
        // get resolved correctly
        let typ: AstType<_> = {
            let mut iter = original_type.forall_params();
            let forall_params = arena.alloc_extend(iter.by_ref().cloned());
            let mut iter = original_type.remove_forall().implicit_arg_iter();
            let implicit_args: Vec<_> = iter.by_ref().map(translate_type).collect();
            let mut iter = iter.typ.arg_iter();
            let args: Vec<_> = iter.by_ref().map(translate_type).collect();

            arena.clone().forall(
                forall_params,
                arena
                    .clone()
                    .function_implicit(implicit_args, arena.clone().function(args, arena.hole())),
            )
        };

        let lambda = TypedIdent::new(symbols.simple_symbol("lambda"));
        pos::spanned(
            span,
            Expr::rec_let_bindings(
                arena,
                vec![ValueBinding {
                    name: pos::spanned(span, Pattern::Ident(lambda.clone())),
                    expr: pos::spanned(
                        span,
                        Expr::app(
                            arena,
                            lift,
                            vec![pos::spanned(
                                span,
                                Expr::app(
                                    arena,
                                    action,
                                    args.iter().map(|arg| {
                                        pos::spanned(span, Expr::Ident(arg.name.value.clone()))
                                    }),
                                ),
                            )],
                        ),
                    ),
                    args,
                    typ: Some(typ),
                    resolved_type: Default::default(),
                    metadata: Default::default(),
                }],
                pos::spanned(span, Expr::Ident(lambda)),
            ),
        )
    }
}
