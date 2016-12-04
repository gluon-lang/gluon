use std::borrow::Cow;

use types::{Type, ArcType, TypeEnv};
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
        Type::Alias(ref alias) if alias.typ.params().is_empty() => Some(alias),
        Type::App(ref alias, ref args) => {
            match **alias {
                Type::Alias(ref alias) if alias.typ.params().len() == args.len() => Some(alias),
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

            Ok(alias.typ.apply_args(typ.unapplied_args()))
        }
        None => Ok(None),
    }
}
