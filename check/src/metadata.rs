use std::collections::BTreeMap;

use base::ast::Visitor;
use base::ast::{
    self, Argument, AstType, Commented, Expr, Pattern, SpannedExpr, SpannedPattern, ValueBinding,
};
use base::fnv::FnvMap;
use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Name, Symbol};
use base::types::row_iter;

struct Environment<'b> {
    env: &'b MetadataEnv,
    stack: FnvMap<Symbol, Metadata>,
}

/// Queries `expr` for the metadata which it contains.
pub fn metadata(
    env: &MetadataEnv,
    expr: &SpannedExpr<Symbol>,
) -> (Metadata, FnvMap<Symbol, Metadata>) {
    struct MetadataVisitor<'b> {
        env: Environment<'b>,
    }

    impl<'b> MetadataVisitor<'b> {
        fn new_binding(&mut self, metadata: Metadata, bind: &ValueBinding<Symbol>) {
            match bind.name.value {
                Pattern::As(ref id, _) => {
                    let mut metadata = bind.metadata.clone().merge(metadata);
                    self.stack_var(id.value.clone(), metadata.clone());
                    self.new_pattern(metadata, &bind.name);
                }
                Pattern::Ident(ref id) => {
                    let mut metadata = bind.metadata.clone().merge(metadata);
                    metadata.args = bind
                        .args
                        .iter()
                        // Ignore generated arguments
                        .filter(|arg| !arg.name.value.name.definition_name().starts_with("__"))
                        .map(|arg| Argument {
                            name: arg.name.value.name.clone(),
                            arg_type: arg.arg_type,
                        })
                        .collect();

                    if let Some(type_metadata) = id
                        .typ
                        .remove_forall_and_implicit_args()
                        .alias_ident()
                        .and_then(|id| self.metadata(id))
                    {
                        let mut type_metadata = type_metadata.clone();
                        // We want the first definition of this value and not the definition of the
                        // type
                        type_metadata.definition = None;
                        metadata.merge_with(type_metadata);
                    }

                    self.stack_var(id.name.clone(), metadata);
                }
                Pattern::Constructor(..)
                | Pattern::Tuple { .. }
                | Pattern::Record { .. }
                | Pattern::Literal(_)
                | Pattern::Error => self.new_pattern(metadata, &bind.name),
            }
        }

        fn new_pattern(&mut self, mut metadata: Metadata, pattern: &SpannedPattern<Symbol>) {
            match pattern.value {
                Pattern::Record {
                    ref fields,
                    ref types,
                    ref typ,
                    ref implicit_import,
                } => {
                    if let Some(ref implicit_import) = *implicit_import {
                        self.stack_var(implicit_import.value.clone(), metadata.clone());
                    }

                    for field in fields {
                        if let Some(m) = metadata.module.remove(field.name.value.as_ref()) {
                            let id = match field.value {
                                Some(ref pat) => match pat.value {
                                    Pattern::Ident(ref id) => &id.name,
                                    _ => return self.new_pattern(m, pat),
                                },
                                None => &field.name.value,
                            };
                            self.stack_var(id.clone(), m);
                        }
                    }
                    for field in types {
                        if let Some(m) = metadata.module.remove(field.name.value.as_ref()) {
                            // FIXME Shouldn't need to insert this metadata twice
                            if let Some(type_field) = typ
                                .type_field_iter()
                                .find(|type_field| type_field.name.name_eq(&field.name.value))
                            {
                                self.stack_var(type_field.typ.name.clone(), m.clone());
                            }

                            let id = field
                                .value
                                .as_ref()
                                .unwrap_or_else(|| &field.name.value)
                                .clone();
                            self.stack_var(id, m);
                        }
                    }
                }
                Pattern::Ident(ref id) => self.stack_var(id.name.clone(), metadata),
                Pattern::As(ref id, ref pat) => {
                    self.stack_var(id.value.clone(), metadata.clone());
                    self.new_pattern(metadata, pat);
                }
                Pattern::Tuple { .. }
                | Pattern::Constructor(..)
                | Pattern::Literal(_)
                | Pattern::Error => (),
            }
        }

        fn stack_var(&mut self, id: Symbol, mut metadata: Metadata) {
            if metadata
                .definition
                .as_ref()
                .map(|definition| {
                    id.declared_name().starts_with(char::is_lowercase)
                        && definition.declared_name().starts_with(char::is_uppercase)
                }).unwrap_or(true)
            {
                metadata.definition = Some(id.clone());
            }

            debug!("Insert {}", id,);
            self.env.stack.insert(id, metadata);
        }

        fn metadata(&self, id: &Symbol) -> Option<&Metadata> {
            debug!("Lookup {}", id);
            self.env
                .stack
                .get(id)
                .or_else(|| self.env.env.get_metadata(id))
        }

        fn metadata_binding(&mut self, bind: &ValueBinding<Symbol>) -> Metadata {
            for arg in &bind.args {
                if let Some(mut type_metadata) = arg
                    .name
                    .value
                    .typ
                    .alias_ident()
                    .and_then(|id| self.metadata(id))
                    .cloned()
                {
                    // We want the first definition of this value and not the definition of the
                    // type
                    type_metadata.definition = None;
                    self.stack_var(arg.name.value.name.clone(), type_metadata);
                }
            }

            self.metadata_expr(&bind.expr)
        }

        fn metadata_expr(&mut self, expr: &SpannedExpr<Symbol>) -> Metadata {
            match expr.value {
                Expr::Ident(ref id) => self
                    .metadata(&id.name)
                    .cloned()
                    .unwrap_or_else(Metadata::default),
                Expr::Record {
                    ref exprs,
                    ref types,
                    ..
                } => {
                    let mut module = BTreeMap::new();
                    for field in exprs {
                        let maybe_metadata = match field.value {
                            Some(ref expr) => {
                                let m = self.metadata_expr(expr);
                                if m.has_data() {
                                    Some(m)
                                } else {
                                    None
                                }
                            }
                            None => self.metadata(&field.name.value).cloned(),
                        };
                        let field_metadata = field.metadata.clone();
                        let maybe_metadata = match maybe_metadata {
                            Some(r) => field_metadata.merge(r),
                            None => field_metadata,
                        };
                        if maybe_metadata.has_data() {
                            let field_name = String::from(field.name.value.as_ref());
                            module.insert(field_name, maybe_metadata);
                        }
                    }
                    for field in types {
                        let maybe_metadata = self.metadata(&field.name.value).cloned();
                        if let Some(metadata) = maybe_metadata {
                            let name = Name::new(field.name.value.as_ref()).name().as_str();
                            module.insert(String::from(name), metadata);
                        }
                    }
                    Metadata {
                        module,
                        ..Metadata::default()
                    }
                }
                Expr::LetBindings(ref bindings, ref expr) => {
                    if bindings.is_recursive() {
                        for bind in bindings {
                            self.new_binding(Metadata::default(), bind);
                        }
                        for bind in bindings {
                            let expr_metadata = self.metadata_binding(&bind);

                            if let Pattern::Ident(ref id) = bind.name.value {
                                if expr_metadata.has_data() {
                                    self.env
                                        .stack
                                        .entry(id.name.clone())
                                        .or_insert_with(Default::default)
                                        .merge_with(expr_metadata);
                                }
                            }
                        }
                    } else {
                        for bind in bindings {
                            let metadata = self.metadata_binding(&bind);
                            self.new_binding(metadata, bind);
                        }
                    }
                    let result = self.metadata_expr(expr);
                    result
                }
                Expr::TypeBindings(ref bindings, ref expr) => {
                    for bind in bindings {
                        let mut type_metadata =
                            Self::metadata_of_type(bind.alias.value.aliased_type());
                        let metadata = type_metadata.map_or_else(
                            || bind.metadata.clone(),
                            |m| m.merge(bind.metadata.clone()),
                        );

                        if metadata.has_data() {
                            // FIXME Shouldn't need to insert this metadata twice
                            self.stack_var(bind.alias.value.name.clone(), metadata.clone());
                            self.stack_var(bind.name.value.clone(), metadata);
                        }
                    }
                    let result = self.metadata_expr(expr);
                    result
                }
                Expr::Projection(ref expr, ref field, _) => {
                    let metadata = self.metadata_expr(expr);
                    metadata
                        .module
                        .get(field.definition_name())
                        .cloned()
                        .unwrap_or_default()
                }
                Expr::MacroExpansion {
                    ref replacement, ..
                } => self.metadata_expr(replacement),
                _ => {
                    ast::walk_expr(self, expr);
                    Metadata::default()
                }
            }
        }

        fn metadata_of_type(typ: &AstType<Symbol>) -> Option<Metadata> {
            let module: BTreeMap<_, _> = row_iter(typ)
                .filter_map(|field| {
                    let field_metadata = Self::metadata_of_type(&field.typ);
                    let field_metadata = match field.typ.comment() {
                        Some(comment) => {
                            let mut metadata = field_metadata.unwrap_or_default();
                            metadata.comment = Some(comment.clone());
                            Some(metadata)
                        }
                        None => field_metadata,
                    };
                    field_metadata.map(|m| (field.name.to_string(), m))
                }).collect();

            if module.is_empty() {
                None
            } else {
                Some(Metadata {
                    module,
                    ..Metadata::default()
                })
            }
        }
    }

    impl<'a, 'b> Visitor<'a> for MetadataVisitor<'b> {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &SpannedExpr<Symbol>) {
            self.metadata_expr(expr);
        }
    }

    let mut visitor = MetadataVisitor {
        env: Environment {
            env: env,
            stack: FnvMap::default(),
        },
    };
    let metadata = visitor.metadata_expr(expr);
    (metadata, visitor.env.stack)
}
