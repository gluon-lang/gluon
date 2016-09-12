use std::collections::BTreeMap;

use base::ast::{self, Expr, Pattern, SpannedExpr, SpannedPattern, ValueBinding};
use base::ast::MutVisitor;
use base::metadata::{Metadata, MetadataEnv};
use base::scoped_map::ScopedMap;
use base::symbol::{Name, Symbol};

struct Environment<'b> {
    env: &'b MetadataEnv,
    stack: ScopedMap<Symbol, Metadata>,
}

/// Queries `expr` for the metadata which it contains.
pub fn metadata(env: &MetadataEnv, expr: &mut SpannedExpr<Symbol>) -> Metadata {
    struct MetadataVisitor<'b> {
        env: Environment<'b>,
    }

    impl<'b> MetadataVisitor<'b> {
        fn new_binding(&mut self, metadata: Metadata, bind: &mut ValueBinding<Symbol>) {
            match bind.name.value {
                Pattern::Ident(ref mut id) => {
                    let metadata = bind.comment
                        .as_ref()
                        .map_or(metadata, |comment| {
                            Metadata {
                                comment: Some(comment.clone()),
                                module: BTreeMap::new(),
                            }
                        });
                    self.stack_var(id.name.clone(), metadata);
                }
                _ => self.new_pattern(metadata, &mut bind.name),
            }
        }

        fn new_pattern(&mut self, mut metadata: Metadata, pattern: &mut SpannedPattern<Symbol>) {
            match pattern.value {
                Pattern::Record { ref mut fields, ref mut types, .. } => {
                    for field in fields.iter_mut().chain(types) {
                        if let Some(m) = metadata.module.remove(field.0.as_ref()) {
                            let id = field.1.as_ref().unwrap_or_else(|| &field.0).clone();
                            self.stack_var(id, m);
                        }
                    }
                }
                Pattern::Ident(ref mut id) => {
                    self.stack_var(id.name.clone(), metadata);
                }
                Pattern::Constructor(..) => (),
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

        fn metadata_expr(&mut self, expr: &mut SpannedExpr<Symbol>) -> Metadata {
            match expr.value {
                Expr::Ident(ref mut id) => {
                    self.metadata(&id.name).cloned().unwrap_or_else(Metadata::default)
                }
                Expr::Record { ref mut exprs, ref mut types, .. } => {
                    let mut module = BTreeMap::new();
                    for &mut (ref id, ref mut maybe_expr) in exprs {
                        let maybe_metadata = match *maybe_expr {
                            Some(ref mut expr) => {
                                let m = self.metadata_expr(expr);
                                if m.has_data() { Some(m) } else { None }
                            }
                            None => self.metadata(id).cloned(),
                        };
                        if let Some(metadata) = maybe_metadata {
                            module.insert(String::from(id.as_ref()), metadata);
                        }
                    }
                    for &mut (ref id, _) in types {
                        let maybe_metadata = self.metadata(id).cloned();
                        if let Some(metadata) = maybe_metadata {
                            let name = Name::new(id.as_ref()).name().as_str();
                            module.insert(String::from(name), metadata);
                        }
                    }
                    Metadata {
                        comment: None,
                        module: module,
                    }
                }
                Expr::LetBindings(ref mut bindings, ref mut expr) => {
                    self.env.stack.enter_scope();
                    let is_recursive = bindings.iter().all(|bind| !bind.args.is_empty());
                    if is_recursive {
                        for bind in bindings.iter_mut() {
                            self.new_binding(Metadata::default(), bind);
                        }
                        for bind in bindings {
                            self.env.stack.enter_scope();
                            self.metadata_expr(&mut bind.expr);
                            self.env.stack.exit_scope();
                        }
                    } else {
                        for bind in bindings {
                            let metadata = self.metadata_expr(&mut bind.expr);
                            self.new_binding(metadata, bind);
                        }
                    }
                    let result = self.metadata_expr(expr);
                    self.env.stack.exit_scope();
                    result
                }
                Expr::TypeBindings(ref mut bindings, ref mut expr) => {
                    self.env.stack.enter_scope();
                    for bind in bindings.iter_mut() {
                        let maybe_metadata = bind.comment.as_ref().map(|comment| {
                            Metadata {
                                comment: Some(comment.clone()),
                                module: BTreeMap::new(),
                            }
                        });
                        if let Some(metadata) = maybe_metadata {
                            self.stack_var(bind.name.clone(), metadata);
                        }
                    }
                    let result = self.metadata_expr(expr);
                    self.env.stack.exit_scope();
                    result
                }
                _ => {
                    ast::walk_mut_expr(self, expr);
                    Metadata::default()
                }
            }
        }
    }

    impl<'b> MutVisitor for MetadataVisitor<'b> {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &mut SpannedExpr<Symbol>) {
            self.metadata_expr(expr);
        }
    }

    let mut visitor = MetadataVisitor {
        env: Environment {
            env: env,
            stack: ScopedMap::new(),
        },
    };
    visitor.metadata_expr(expr)
}
