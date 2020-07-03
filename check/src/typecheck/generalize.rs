use crate::base::{
    ast::{self, MutVisitor, SpannedExpr, SpannedIdent},
    fnv::{FnvMap, FnvSet},
    pos::{BytePos, Span},
    symbol::Symbol,
    types::{self, AppVec, ArcType, BuiltinType, Flags, Generic, Type, TypeContext, TypePtr},
};

use crate::{substitution::Substitution, typ::RcType, typecheck::Typecheck};

pub(crate) struct TypeGeneralizer<'a, 'b: 'a, 'ast> {
    level: u32,
    unbound_variables: FnvMap<u32, RcType>,
    /// We delay updating the substitution until after all recursive bindings have been typechecked
    /// to ensure that they get can figure out which variable got generalized for each binding
    delayed_generalizations: Vec<(u32, RcType)>,
    variable_generator: Option<TypeVariableGenerator>,
    top_type: RcType,
    pub tc: &'a mut Typecheck<'b, 'ast>,
    span: Span<BytePos>,
}

impl<'a, 'b> Drop for TypeGeneralizer<'a, 'b, '_> {
    fn drop(&mut self) {
        for (id, gen) in self.delayed_generalizations.drain(..) {
            self.tc.subs.replace(id, gen);
        }
    }
}

impl<'a, 'b, 'ast> ::std::ops::Deref for TypeGeneralizer<'a, 'b, 'ast> {
    type Target = Typecheck<'b, 'ast>;
    fn deref(&self) -> &Typecheck<'b, 'ast> {
        self.tc
    }
}

impl<'a, 'b> ::std::ops::DerefMut for TypeGeneralizer<'a, 'b, '_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.tc
    }
}

impl<'a, 'b> TypeContext<Symbol, RcType> for TypeGeneralizer<'a, 'b, '_> {
    gluon_base::forward_type_interner_methods!(Symbol, RcType, self_, &self_.tc.subs);
}

impl<'a, 'b, 'ast> TypeGeneralizer<'a, 'b, 'ast> {
    pub(crate) fn new(
        level: u32,
        tc: &'a mut Typecheck<'b, 'ast>,
        typ: &RcType,
        span: Span<BytePos>,
    ) -> Self {
        TypeGeneralizer {
            level,
            unbound_variables: Default::default(),
            delayed_generalizations: Vec::new(),
            variable_generator: None,
            top_type: typ.clone(),
            tc,
            span,
        }
    }

    /// Generalizing updates all variables which are above `level` into "generic variables". A
    /// generic variable is instantiated with a fresh type variable each time it is refered to.
    ///
    /// Generalzing is a crucial part when inferring types as types will otherwise be less general
    /// than they need to. Consider the following expression.
    /// ```f#
    /// let id x = x
    /// in id 2
    /// ```
    /// If the variable in `id` was not generalized before the `id 2` call the variable would be
    /// unified to an `Int` which is not what we want. Generalazing before checking the body of the
    /// `let` basically infers that the variables in `id` does not refer to anything outside the
    /// `let` scope and can thus be "generalized" into `a -> a` which is instantiated with a fresh
    /// type variable in the `id 2` call.
    pub(crate) fn generalize_variables<'i>(
        &mut self,
        args: &mut dyn Iterator<Item = &'i mut SpannedIdent<Symbol>>,
        expr: &mut SpannedExpr<Symbol>,
    ) {
        self.tc.environment.skolem_variables.enter_scope();

        {
            let mut visitor = ReplaceVisitor { generalizer: self };
            visitor.visit_expr(expr);
            for arg in &mut *args {
                visitor.visit_typ(&mut arg.value.typ)
            }
        }

        self.tc.environment.skolem_variables.exit_scope();
    }

    pub(crate) fn generalize_type_top(&mut self, typ: &mut RcType) {
        self.tc.environment.skolem_variables.enter_scope();

        let mut result_type = self.generalize_type(typ);

        self.tc.environment.skolem_variables.exit_scope();

        if result_type.is_none() && !self.unbound_variables.is_empty() {
            result_type = Some(typ.clone());
        }

        result_type = result_type.map(|typ| {
            let delayed_generalizations = &mut self.delayed_generalizations;
            let mut params = self
                .unbound_variables
                .drain()
                .map(|(id, generic)| {
                    let t = match &*generic {
                        Type::Generic(g) => g.clone(),
                        _ => unreachable!(),
                    };
                    delayed_generalizations.push((id, generic));
                    t
                })
                .collect::<Vec<_>>();
            params.sort_unstable_by(|l, r| l.id.declared_name().cmp(r.id.declared_name()));

            self.tc.forall(params, typ)
        });
        if let Some(finished) = result_type {
            *typ = finished;
        }
        debug!("End generalize {}", typ);
    }

    pub(crate) fn generalize_type_mut(&mut self, typ: &mut RcType) {
        if let Some(new_type) = self.generalize_type(typ) {
            *typ = new_type;
        }
    }

    pub(crate) fn generalize_type(&mut self, typ: &RcType) -> Option<RcType> {
        let replacement = self.subs.replace_variable(typ);
        let mut typ = typ;
        if let Some(ref t) = replacement {
            typ = t;
        }
        trace!("GEN: {}", typ);

        if !typ.needs_generalize() {
            trace!("No need to generalize: {}", typ);
            return replacement;
        }

        let new_type = match **typ {
            Type::Variable(ref var) if self.subs.get_level(var.id) >= self.level => {
                let Self {
                    tc,
                    variable_generator,
                    top_type,
                    ..
                } = self;
                let gen = self.unbound_variables.entry(var.id).or_insert_with(|| {
                    let variable_generator = match variable_generator {
                        Some(v) => v,
                        None => {
                            *variable_generator =
                                Some(TypeVariableGenerator::new(&tc.subs, top_type));
                            variable_generator.as_mut().unwrap()
                        }
                    };
                    // Create a prefix if none exists
                    let id = variable_generator.next_variable(tc);

                    let gen: RcType = tc.generic(Generic::new(id.clone(), var.kind.clone()));
                    debug!("Gen {} to {}", var.id, gen);

                    gen
                });

                Some(gen.clone())
            }

            Type::Skolem(ref skolem) => {
                let in_scope = self.environment.skolem_variables.contains_key(&skolem.name);
                if self.subs.get_level(skolem.id) >= self.level {
                    let generic = self.generic(Generic {
                        id: skolem.name.clone(),
                        kind: skolem.kind.clone(),
                    });

                    if !in_scope {
                        self.unbound_variables
                            .insert(skolem.id.clone(), generic.clone());
                    }

                    Some(generic)
                } else {
                    replacement.clone()
                }
            }

            _ => {
                // Ensure that the forall's variables don't look unbound
                if let Type::Forall(ref params, _) = **typ {
                    self.environment.skolem_variables.enter_scope();
                    let mut type_cache = &self.tc.subs;
                    self.tc.environment.skolem_variables.extend(
                        params
                            .iter()
                            .map(|param| (param.id.clone(), type_cache.hole())),
                    );
                }

                let new_type = types::walk_move_type_opt(
                    typ,
                    &mut types::InternerVisitor::control(self, |self_, typ: &RcType| {
                        self_.generalize_type(typ)
                    }),
                )
                .map(|t| unroll_typ(self.tc, &t).unwrap_or(t))
                .or_else(|| replacement.clone());

                if let Type::Forall(..) = **typ {
                    self.environment.skolem_variables.exit_scope();
                }

                new_type
            }
        };

        new_type
    }
}

struct TypeVariableGenerator {
    map: FnvSet<Symbol>,
    name: String,
    i: u32,
}

impl TypeVariableGenerator {
    fn new(subs: &Substitution<RcType>, typ: &RcType) -> TypeVariableGenerator {
        fn gather_foralls(map: &mut FnvSet<Symbol>, subs: &Substitution<RcType>, typ: &RcType) {
            if !typ
                .flags()
                .intersects(Flags::HAS_VARIABLES | Flags::HAS_FORALL)
            {
                return;
            }
            let typ = subs.real(typ);
            if let Type::Forall(ref params, _) = **typ {
                map.extend(params.iter().map(|param| param.id.clone()));
            }
            types::walk_type_(
                typ,
                &mut types::ControlVisitation(|typ: &RcType| {
                    gather_foralls(map, subs, typ);
                }),
            );
        }
        let mut map = FnvSet::default();
        gather_foralls(&mut map, subs, typ);
        TypeVariableGenerator {
            map,
            name: String::new(),
            i: 0,
        }
    }
    /// Generate a generic variable name which is not used in the current scope
    fn next_variable(&mut self, tc: &mut Typecheck) -> Symbol {
        let symbol = if self.name.is_empty() {
            self.next_variable_(tc)
        } else {
            let name = format!("{}{}", self.name, self.i);
            self.i += 1;
            tc.symbols.simple_symbol(&name[..])
        };
        self.map.insert(symbol.clone());
        let hole = tc.hole();
        tc.environment.skolem_variables.insert(symbol.clone(), hole);
        symbol
    }

    fn next_variable_(&mut self, tc: &mut Typecheck) -> Symbol {
        for c in b'a'..(b'z' + 1) {
            self.name.push(c as char);
            let symbol = tc.symbols.simple_symbol(&self.name[..]);
            if !self.map.contains(&symbol) && tc.environment.skolem_variables.get(&symbol).is_none()
            {
                return symbol;
            }
            self.name.pop();
        }
        self.name.push('a');
        self.next_variable_(tc)
    }
}

fn unroll_typ(interner: &mut impl TypeContext<Symbol, RcType>, typ: &RcType) -> Option<RcType> {
    let mut args = AppVec::new();
    let mut current = match **typ {
        Type::App(ref l, ref rest) => {
            // No need to unroll if `l` is not an application as that will just result in returning
            // an application that is identical to `typ`
            match **l {
                Type::App(..) => (),
                _ => return None,
            }
            args.extend(rest.iter().rev().cloned());
            l
        }
        _ => return unroll_record(interner, typ),
    };
    while let Type::App(ref l, ref rest) = **current {
        args.extend(rest.iter().rev().cloned());
        current = l;
    }
    if args.is_empty() {
        None
    } else {
        args.reverse();
        match **current {
            Type::Builtin(BuiltinType::Function) if args.len() == 2 => {
                let ret = args.pop().unwrap();
                Some(interner.function(args, ret))
            }
            _ => Some(interner.app(current.clone(), args)),
        }
    }
}

fn unroll_record(
    interner: &mut impl TypeContext<Symbol, RcType>,
    typ: &Type<Symbol, RcType>,
) -> Option<RcType> {
    let mut new_types = Vec::new();
    let mut new_fields = Vec::new();
    let mut current = match &*typ {
        Type::ExtendRow { fields, rest } => match **rest {
            Type::ExtendRow { .. } | Type::ExtendTypeRow { .. } => {
                new_fields.extend_from_slice(fields);
                rest
            }
            _ => return None,
        },

        Type::ExtendTypeRow { types, rest } => match **rest {
            Type::ExtendRow { .. } | Type::ExtendTypeRow { .. } => {
                new_types.extend_from_slice(types);
                rest
            }
            _ => return None,
        },

        _ => return None,
    };
    loop {
        match &**current {
            Type::ExtendRow { fields, rest } => {
                new_fields.extend_from_slice(fields);
                current = rest;
            }
            Type::ExtendTypeRow { types, rest } => {
                new_types.extend_from_slice(types);
                current = rest;
            }
            _ => break,
        }
    }
    if new_types.is_empty() && new_fields.is_empty() {
        None
    } else {
        Some(interner.extend_full_row(new_types, new_fields, current.clone()))
    }
}

// Replaces all type variables with their inferred types
pub struct ReplaceVisitor<'a: 'c, 'b: 'a, 'c, 'ast> {
    pub(crate) generalizer: &'c mut TypeGeneralizer<'a, 'b, 'ast>,
}

impl<'a, 'b, 'c, 'd> MutVisitor<'d, '_> for ReplaceVisitor<'a, 'b, 'c, '_> {
    type Ident = Symbol;

    fn visit_expr(&mut self, e: &'d mut SpannedExpr<Self::Ident>) {
        self.generalizer.span = e.span;
        ast::walk_mut_expr(self, e);
    }

    fn visit_spanned_typed_ident(&mut self, id: &mut SpannedIdent<Symbol>) {
        self.generalizer.span = id.span;
        self.visit_ident(&mut id.value)
    }
    fn visit_typ(&mut self, typ: &mut ArcType) {
        debug!("Variable generalize {}", typ);
        if let Some(new_type) = self.generalizer.generalize_type(typ) {
            *typ = new_type;
            debug!("End generalize {}", typ);
        } else {
            debug!("End variable generalize");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::base::types::SharedInterner;

    #[test]
    fn unroll_typ_test() {
        let mut interner = SharedInterner::default();

        let i: RcType = interner.int();
        let s: RcType = interner.string();
        assert_eq!(
            unroll_typ(
                &mut &interner,
                &(&interner).app(
                    (&interner).app(i.clone(), collect![s.clone()]),
                    collect![i.clone()]
                )
            ),
            Some(interner.app(i.clone(), collect![s.clone(), i.clone()]))
        );
        assert_eq!(
            unroll_typ(
                &mut &interner,
                &(&interner).app(
                    (&interner).app(i.clone(), collect![i.clone()]),
                    collect![s.clone()]
                )
            ),
            Some(interner.app(i.clone(), collect![i.clone(), s.clone()]))
        );
        let f: RcType = interner.function_builtin();
        assert_eq!(
            unroll_typ(
                &mut &interner,
                &(&interner).app(
                    (&interner).app(f.clone(), collect![i.clone()]),
                    collect![s.clone()]
                )
            ),
            Some(interner.function(vec![i.clone()], s.clone()))
        );
    }
}
