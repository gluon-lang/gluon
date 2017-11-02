use std::collections::BTreeMap;

use base::ast::{self, Expr, Pattern, SpannedExpr, SpannedPattern, ValueBinding};
use base::ast::Visitor;
use base::fnv::FnvMap;
use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Name, Symbol};

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
                    let metadata = bind.comment.as_ref().map_or(metadata, |comment| {
                        Metadata {
                            comment: Some(comment.content.clone()),
                            module: BTreeMap::new(),
                        }
                    });
                    self.stack_var(id.clone(), metadata.clone());
                    self.new_pattern(metadata, &bind.name);
                }
                Pattern::Ident(ref id) => {
                    let metadata = bind.comment.as_ref().map_or(metadata, |comment| {
                        Metadata {
                            comment: Some(comment.content.clone()),
                            module: BTreeMap::new(),
                        }
                    });
                    self.stack_var(id.name.clone(), metadata);
                }
                Pattern::Constructor(..) |
                Pattern::Tuple { .. } |
                Pattern::Record { .. } |
                Pattern::Error => self.new_pattern(metadata, &bind.name),
            }
        }

        fn new_pattern(&mut self, mut metadata: Metadata, pattern: &SpannedPattern<Symbol>) {
            match pattern.value {
                Pattern::Record {
                    ref fields,
                    ref types,
                    ..
                } => {
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
                    self.stack_var(id.clone(), metadata.clone());
                    self.new_pattern(metadata, pat);
                }
                Pattern::Tuple { .. } | Pattern::Constructor(..) | Pattern::Error => (),
            }
        }

        fn stack_var(&mut self, id: Symbol, metadata: Metadata) {
            if metadata.has_data() {
                debug!("Insert {}", id);
                self.env.stack.insert(id, metadata);
            }
        }

        fn metadata(&self, id: &Symbol) -> Option<&Metadata> {
            debug!("Lookup {}", id);
            self.env
                .stack
                .get(id)
                .or_else(|| self.env.env.get_metadata(id))
        }

        fn metadata_expr(&mut self, expr: &SpannedExpr<Symbol>) -> Metadata {
            match expr.value {
                Expr::Ident(ref id) => self.metadata(&id.name)
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
                        let field_metadata = field.comment.clone().map(|comment| {
                            Metadata {
                                comment: Some(comment.content),
                                module: BTreeMap::new(),
                            }
                        });
                        let maybe_metadata = match (field_metadata, maybe_metadata) {
                            (Some(l), Some(r)) => Some(l.merge(r)),
                            (None, Some(x)) | (Some(x), None) => Some(x),
                            (None, None) => None,
                        };
                        if let Some(metadata) = maybe_metadata {
                            module.insert(String::from(field.name.value.as_ref()), metadata);
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
                        comment: None,
                        module: module,
                    }
                }
                Expr::LetBindings(ref bindings, ref expr) => {
                    let is_recursive = bindings.iter().all(|bind| !bind.args.is_empty());
                    if is_recursive {
                        for bind in bindings {
                            self.new_binding(Metadata::default(), bind);
                        }
                        for bind in bindings {
                            self.metadata_expr(&bind.expr);
                        }
                    } else {
                        for bind in bindings {
                            let metadata = self.metadata_expr(&bind.expr);
                            self.new_binding(metadata, bind);
                        }
                    }
                    let result = self.metadata_expr(expr);
                    result
                }
                Expr::TypeBindings(ref bindings, ref expr) => {
                    for bind in bindings {
                        let maybe_metadata = bind.comment.as_ref().map(|comment| {
                            Metadata {
                                comment: Some(comment.content.clone()),
                                module: BTreeMap::new(),
                            }
                        });
                        if let Some(metadata) = maybe_metadata {
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
                        .get(field.as_ref())
                        .cloned()
                        .unwrap_or_default()
                }
                _ => {
                    ast::walk_expr(self, expr);
                    Metadata::default()
                }
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
