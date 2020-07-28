use std::{collections::BTreeMap, sync::Arc};

#[cfg(feature = "serde_derive")]
use serde_derive::{Deserialize, Serialize};

use crate::base::{
    ast::{
        self, Argument, AstType, Expr, HasMetadata, Pattern, PatternField, SpannedExpr,
        SpannedPattern, ValueBinding, Visitor,
    },
    fnv::FnvMap,
    metadata::{BaseMetadata, Metadata, MetadataEnv},
    symbol::{Name, Symbol},
    types::{row_iter, TypeExt},
};

struct Environment<'b> {
    env: &'b dyn MetadataEnv,
    stack: FnvMap<Symbol, Arc<Metadata>>,
}

trait ArcMetadata: Into<Arc<Metadata>> {
    fn into_owned(self) -> Metadata;
    fn definition(&self) -> Option<&Symbol>;
    fn has_data(&self) -> bool;
}

impl ArcMetadata for Arc<Metadata> {
    fn into_owned(self) -> Metadata {
        Arc::try_unwrap(self).unwrap_or_else(|arc| (*arc).clone())
    }
    fn definition(&self) -> Option<&Symbol> {
        self.definition.as_ref()
    }
    fn has_data(&self) -> bool {
        Metadata::has_data(self)
    }
}

impl ArcMetadata for Metadata {
    fn into_owned(self) -> Metadata {
        self
    }
    fn definition(&self) -> Option<&Symbol> {
        self.definition.as_ref()
    }
    fn has_data(&self) -> bool {
        Metadata::has_data(self)
    }
}

impl ArcMetadata for MaybeMetadata {
    fn into_owned(self) -> Metadata {
        match self {
            MaybeMetadata::Empty => Metadata::default(),
            MaybeMetadata::Data(d) => d.into_owned(),
        }
    }
    fn definition(&self) -> Option<&Symbol> {
        match self {
            MaybeMetadata::Empty => None,
            MaybeMetadata::Data(d) => d.definition(),
        }
    }
    fn has_data(&self) -> bool {
        match self {
            MaybeMetadata::Empty => false,
            MaybeMetadata::Data(d) => d.has_data(),
        }
    }
}

#[derive(Clone, Debug)]
enum MaybeMetadata {
    Empty,
    Data(Arc<Metadata>),
}

impl Default for MaybeMetadata {
    fn default() -> Self {
        MaybeMetadata::Empty
    }
}

impl From<Option<Arc<Metadata>>> for MaybeMetadata {
    fn from(m: Option<Arc<Metadata>>) -> Self {
        match m {
            None => Default::default(),
            Some(d) => MaybeMetadata::Data(d),
        }
    }
}

impl From<MaybeMetadata> for Arc<Metadata> {
    fn from(m: MaybeMetadata) -> Self {
        match m {
            MaybeMetadata::Empty => Default::default(),
            MaybeMetadata::Data(d) => d.clone(),
        }
    }
}

impl MaybeMetadata {
    fn merge_base(metadata: &BaseMetadata, other: &MaybeMetadata) -> MaybeMetadata {
        if metadata.has_data() {
            match other {
                MaybeMetadata::Empty => MaybeMetadata::Data(Arc::new(metadata.to_metadata())),
                MaybeMetadata::Data(other) => {
                    MaybeMetadata::Data(Arc::new(metadata.to_metadata().merge_ref(other)))
                }
            }
        } else {
            other.clone()
        }
    }

    fn get_module(&self, key: &str) -> Option<&Arc<Metadata>> {
        match self {
            MaybeMetadata::Empty => None,
            MaybeMetadata::Data(d) => d.module.get(key),
        }
    }
}

/// Queries `expr` for the metadata which it contains.
pub fn metadata(
    env: &dyn MetadataEnv,
    expr: &SpannedExpr<Symbol>,
) -> (Arc<Metadata>, FnvMap<Symbol, Arc<Metadata>>) {
    struct MetadataVisitor<'b> {
        env: Environment<'b>,
    }

    impl<'b> MetadataVisitor<'b> {
        fn new_binding(&mut self, metadata: MaybeMetadata, bind: &ValueBinding<Symbol>) {
            match bind.name.value {
                Pattern::As(ref id, _) => {
                    let metadata = MaybeMetadata::merge_base(&bind.metadata, &metadata);
                    self.stack_var(id.value.clone(), metadata.clone());
                    self.new_pattern(metadata, &bind.name);
                }
                Pattern::Ident(ref id) => {
                    let mut metadata =
                        MaybeMetadata::merge_base(&bind.metadata, &metadata).into_owned();
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
                        // We want the first definition of this value and not the definition of the
                        // type
                        let metadata_definition = metadata.definition.take();
                        metadata.merge_with_ref(&type_metadata);
                        metadata.definition = metadata_definition;
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

        fn new_pattern(&mut self, metadata: MaybeMetadata, pattern: &SpannedPattern<Symbol>) {
            match pattern.value {
                Pattern::Record {
                    ref fields,
                    ref typ,
                    ref implicit_import,
                } => {
                    if let Some(ref implicit_import) = *implicit_import {
                        self.stack_var(implicit_import.value.clone(), metadata.clone());
                    }

                    for field in &**fields {
                        match field {
                            PatternField::Value { name, value } => {
                                if let Some(m) = metadata.get_module(name.value.as_ref()) {
                                    let id = match value {
                                        Some(pat) => match pat.value {
                                            Pattern::Ident(ref id) => &id.name,
                                            _ => {
                                                return self.new_pattern(
                                                    MaybeMetadata::Data(m.clone()),
                                                    pat,
                                                );
                                            }
                                        },
                                        None => &name.value,
                                    };
                                    self.stack_var(id.clone(), m.clone());
                                }
                            }
                            PatternField::Type { name } => {
                                if let Some(m) = metadata.get_module(name.value.as_ref()) {
                                    // TODO Shouldn't need to insert this metadata twice
                                    if let Some(type_field) = typ
                                        .type_field_iter()
                                        .find(|type_field| type_field.name.name_eq(&name.value))
                                    {
                                        self.stack_var(type_field.typ.name.clone(), m.clone());
                                    }

                                    let id = name.value.clone();
                                    self.stack_var(id, m.clone());
                                }
                            }
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

        fn stack_var(&mut self, id: Symbol, metadata: impl ArcMetadata) {
            let arc_metadata = if metadata
                .definition()
                .as_ref()
                .map(|definition| {
                    id.declared_name().starts_with(char::is_lowercase)
                        && definition.declared_name().starts_with(char::is_uppercase)
                })
                .unwrap_or(true)
            {
                let mut metadata = metadata.into_owned();
                metadata.definition = Some(id.clone());
                metadata.into()
            } else {
                metadata.into()
            };

            debug!("Insert {}", id,);
            self.env.stack.insert(id, arc_metadata);
        }

        fn metadata(&self, id: &Symbol) -> Option<Arc<Metadata>> {
            debug!("Lookup {}", id);
            self.env
                .stack
                .get(id)
                .cloned()
                .or_else(|| self.env.env.get_metadata(id))
        }

        fn metadata_binding(&mut self, bind: &ValueBinding<Symbol>) -> MaybeMetadata {
            for arg in &*bind.args {
                if let Some(type_metadata) = arg
                    .name
                    .value
                    .typ
                    .alias_ident()
                    .and_then(|id| self.metadata(id))
                {
                    let mut type_metadata =
                        Arc::try_unwrap(type_metadata).unwrap_or_else(|arc| (*arc).clone());
                    // We want the first definition of this value and not the definition of the
                    // type
                    type_metadata.definition = None;
                    self.stack_var(arg.name.value.name.clone(), type_metadata);
                }
            }

            self.metadata_expr(&bind.expr)
        }

        fn metadata_expr(&mut self, expr: &SpannedExpr<Symbol>) -> MaybeMetadata {
            match expr.value {
                Expr::Ident(ref id) => self.metadata(&id.name).into(),
                Expr::Record {
                    ref exprs,
                    ref types,
                    ..
                } => {
                    let mut module = BTreeMap::new();

                    for field in &**exprs {
                        let maybe_metadata = match field.value {
                            Some(ref expr) => self.metadata_expr(expr),
                            None => self.metadata(&field.name.value).into(),
                        };
                        let maybe_metadata =
                            MaybeMetadata::merge_base(&field.metadata, &maybe_metadata);
                        if let MaybeMetadata::Data(metadata) = maybe_metadata {
                            let field_name = String::from(field.name.value.as_pretty_str());
                            module.insert(field_name, metadata);
                        }
                    }

                    for field in &**types {
                        let maybe_metadata = self.metadata(&field.name.value);
                        if let MaybeMetadata::Data(metadata) = maybe_metadata.into() {
                            let name = Name::new(field.name.value.as_pretty_str()).name().as_str();
                            module.insert(String::from(name), metadata);
                        }
                    }

                    if module.is_empty() {
                        MaybeMetadata::Empty
                    } else {
                        MaybeMetadata::Data(Arc::new(Metadata {
                            module,
                            ..Metadata::default()
                        }))
                    }
                }
                Expr::LetBindings(ref bindings, ref expr) => {
                    if bindings.is_recursive() {
                        for bind in bindings {
                            self.new_binding(Default::default(), bind);
                        }
                        for bind in bindings {
                            let expr_metadata = self.metadata_binding(&bind);

                            if let Pattern::Ident(ref id) = bind.name.value {
                                if let MaybeMetadata::Data(expr_metadata) = expr_metadata {
                                    Arc::make_mut(
                                        self.env
                                            .stack
                                            .entry(id.name.clone())
                                            .or_insert_with(Default::default),
                                    )
                                    .merge_with_ref(&expr_metadata);
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
                    for bind in &**bindings {
                        let type_metadata = Self::metadata_of_type(bind.alias.value.aliased_type());
                        let metadata = type_metadata.map_or_else(
                            || bind.metadata.to_metadata(),
                            |m| m.merge_with_base(&bind.metadata),
                        );

                        if metadata.has_data() {
                            // TODO Shouldn't need to insert this metadata twice
                            self.stack_var(bind.alias.value.name.clone(), metadata.clone());
                            self.stack_var(bind.name.value.clone(), metadata);
                        }
                    }
                    let result = self.metadata_expr(expr);
                    result
                }
                Expr::Projection(ref expr, ref field, _) => {
                    let metadata = self.metadata_expr(expr);
                    metadata.get_module(field.definition_name()).cloned().into()
                }
                Expr::MacroExpansion {
                    ref replacement, ..
                } => self.metadata_expr(replacement),
                Expr::Tuple { ref elems, .. } if elems.len() == 1 => self.metadata_expr(&elems[0]),
                _ => {
                    ast::walk_expr(self, expr);
                    Default::default()
                }
            }
        }

        fn metadata_of_type(typ: &AstType<Symbol>) -> Option<Metadata> {
            let module: BTreeMap<_, _> = row_iter(typ)
                .filter_map(|field| {
                    let field_metadata = Self::metadata_of_type(&field.typ);
                    let field_metadata = match field.typ.metadata() {
                        Some(other_metadata) => {
                            let mut metadata = field_metadata.unwrap_or_default();
                            metadata.merge_with_ref(other_metadata);
                            Some(metadata)
                        }
                        None => field_metadata,
                    };
                    field_metadata
                        .map(|m| (String::from(field.name.value.as_pretty_str()), Arc::new(m)))
                })
                .collect();

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

    impl<'a, 'b> Visitor<'a, '_> for MetadataVisitor<'b> {
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
    let metadata = visitor.metadata_expr(expr).into();
    (metadata, visitor.env.stack)
}
