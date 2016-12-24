use std::borrow::Cow;

use types;
use types::{AliasData, AppVec, Type, ArcType, TypeEnv};
use symbol::Symbol;

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        UndefinedType(id: Symbol) {
            description("undefined type")
            display("Type `{}` does not exist.", id)
        }
    }
}

/// Removes type aliases from `typ` until it is an actual type
pub fn remove_aliases(env: &TypeEnv, mut typ: ArcType) -> ArcType {
    while let Ok(Some(new)) = remove_alias(env, &typ) {
        typ = new;
    }
    typ
}

pub fn remove_aliases_cow<'t>(env: &TypeEnv, typ: &'t ArcType) -> Cow<'t, ArcType> {
    match remove_alias(env, typ) {
        Ok(Some(typ)) => Cow::Owned(remove_aliases(env, typ)),
        _ => return Cow::Borrowed(typ),
    }
}

/// Expand `typ` if it is an alias that can be expanded and return the expanded type.
/// Returns `None` if the type is not an alias or the alias could not be expanded.
pub fn remove_alias(env: &TypeEnv, typ: &ArcType) -> Result<Option<ArcType>, Error> {
    let maybe_alias = match **typ {
        Type::Alias(ref alias) if alias.args.is_empty() => Some(alias),
        Type::App(ref alias, ref args) => {
            match **alias {
                Type::Alias(ref alias) if alias.args.len() == args.len() => Some(alias),
                _ => None,
            }
        }
        _ => None,
    };

    match typ.alias_ident() {
        Some(id) => {
            let alias = match maybe_alias {
                Some(alias) => alias,
                None => {
                    env.find_type_info(&id)
                        .map(|a| &**a)
                        .ok_or_else(|| Error::UndefinedType(id.clone()))?
                }
            };

            Ok(type_of_alias(env, alias, typ.unapplied_args()))
        }
        None => Ok(None),
    }
}

/// Returns the type which is aliased by `alias` if it was possible to do a substitution on the
/// type arguments of `alias` using `args`
///
/// Example:
///     alias = Result e t (| Err e | Ok t)
///     args = [Error, Option a]
///     result = | Err Error | Ok (Option a)
pub fn type_of_alias(env: &TypeEnv,
                     alias: &AliasData<Symbol, ArcType>,
                     args: &[ArcType])
                     -> Option<ArcType> {
    let alias_args = &alias.args;
    let mut typ = alias.unresolved_type().clone();

    // It is ok to take the aliased type only if the alias is fully applied or if it
    // the missing argument only appear in order at the end of the alias
    // i.e
    // type Test a b c = Type (a Int) b c
    //
    // Test a b == Type (a Int) b
    // Test a == Type (a Int)
    // Test == ??? (Impossible to do a sane substitution)
    match *typ.clone() {
        Type::App(ref d, ref arg_types) => {
            let allowed_missing_args = arg_types.iter()
                .rev()
                .zip(alias_args.iter().rev())
                .take_while(|&(l, r)| {
                    match **l {
                        Type::Generic(ref g) => g == r,
                        _ => false,
                    }
                })
                .count();
            if alias_args.len() - args.len() <= allowed_missing_args {
                // Remove the args at the end of the aliased type
                let arg_types: AppVec<_> = arg_types.iter()
                    .take(arg_types.len() - (alias_args.len() - args.len()))
                    .cloned()
                    .collect();
                typ = Type::app(d.clone(), arg_types);
            } else {
                return None;
            }
        }
        _ => {
            if args.len() != alias_args.len() {
                return None;
            }
        }
    }

    Some(types::walk_move_type(typ,
                               &mut |typ| {
        match *typ {
            Type::Generic(ref generic) => {
                // Replace the generic variable with the type from the list
                // or if it is not found the make a fresh variable
                alias_args.iter()
                    .zip(args)
                    .find(|&(arg, _)| arg.id == generic.id)
                    .map(|(_, typ)| typ.clone())
            }
            Type::Ident(ref id) => {
                // Replace `Ident` with the alias it resolves to so that a `TypeEnv` is not needed
                // to resolve the type later on
                env.find_type_info(id)
                    .map(|a| a.clone().into_type())
            }
            _ => None,
        }
    }))
}
