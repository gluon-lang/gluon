use futures::future;

use gluon_codegen::Trace;
use {
    base::{
        ast::{
            Argument, AstType, EmptyEnv, Expr, ExprField, Pattern, SpannedExpr, Typed, TypedIdent,
            ValueBinding,
        },
        pos::{self, BytePos, Span},
        symbol::{Symbol, Symbols},
        types::{self, ArcType, Type, TypeExt},
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
    fn expand<'a>(
        &self,
        env: &mut MacroExpander<'a>,
        mut args: Vec<SpannedExpr<Symbol>>,
    ) -> MacroFuture<'a> {
        if args.len() != 2 {
            return Box::pin(future::err(macros::Error::message(format!(
                "`lift_io!` expects 1 argument"
            ))));
        }

        let mut env = env.fork();

        Box::pin(async move {
            let mut module = args.pop().unwrap();
            let lift = args.pop().unwrap();
            let mut symbols = Symbols::new();
            env.run(&mut symbols, &mut module).await;
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

            let span = module.span;

            let vm = env.vm;

            let out = pos::spanned(
                span,
                Expr::Record {
                    typ: typ.clone(),
                    types: Vec::new(),
                    exprs: typ
                        .row_iter()
                        .filter_map(|field| {
                            let mut arg_iter =
                                field.typ.remove_forall_and_implicit_args().arg_iter();
                            let args = arg_iter.by_ref().count();

                            let action = pos::spanned(
                                span,
                                Expr::Projection(
                                    Box::new(module.clone()),
                                    field.name.clone(),
                                    field.typ.clone(),
                                ),
                            );

                            if check_signature(
                                &vm.get_env(),
                                &arg_iter.typ,
                                &IO::<A>::make_forall_type(&vm),
                            ) {
                                let action = lift_action(
                                    &mut symbols,
                                    lift.clone(),
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
                        .collect(),
                    base: Some(Box::new(module)),
                },
            );
            Ok(out)
        })
    }
}

fn lift_action(
    symbols: &mut Symbols,
    lift: SpannedExpr<Symbol>,
    action: SpannedExpr<Symbol>,
    args: usize,
    original_type: &ArcType<Symbol>,
    span: Span<BytePos>,
) -> SpannedExpr<Symbol> {
    let args: Vec<_> = (0..args)
        .map(|i| {
            Argument::explicit(pos::spanned(
                span,
                TypedIdent::new(symbols.simple_symbol(format!("x{}", i))),
            ))
        })
        .collect();
    if args.is_empty() {
        pos::spanned(span, Expr::app(lift, vec![action]))
    } else {
        let translate_type = |t| types::translate_type(&mut types::NullInterner::default(), t);
        // If there are any implicit arguments we need to forward them to the lambda so implicits
        // get resolved correctly
        let typ: AstType<_> = {
            let mut iter = original_type.forall_params();
            let forall_params: Vec<_> = iter.by_ref().cloned().collect();
            let mut iter = original_type.remove_forall().implicit_arg_iter();
            let implicit_args: Vec<_> = iter.by_ref().map(translate_type).collect();
            let mut iter = iter.typ.arg_iter();
            let args: Vec<_> = iter.by_ref().map(translate_type).collect();

            Type::forall(
                forall_params,
                Type::function_implicit(implicit_args, Type::function(args, Type::hole())),
            )
        };

        let lambda = TypedIdent::new(symbols.simple_symbol("lambda"));
        pos::spanned(
            span,
            Expr::rec_let_bindings(
                vec![ValueBinding {
                    name: pos::spanned(span, Pattern::Ident(lambda.clone())),
                    expr: pos::spanned(
                        span,
                        Expr::app(
                            lift,
                            vec![pos::spanned(
                                span,
                                Expr::app(
                                    action,
                                    args.iter()
                                        .map(|arg| {
                                            pos::spanned(span, Expr::Ident(arg.name.value.clone()))
                                        })
                                        .collect(),
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
