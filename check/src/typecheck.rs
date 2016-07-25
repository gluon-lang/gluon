//! The main typechecking interface which is responsible for typechecking expressions, patterns,
//! etc. Only checks which need to be aware of expressions are handled here the actual unifying and
//! checking of types are done in the `unify_type` and `kindcheck` modules.
use std::fmt;
use std::mem;

use base::scoped_map::ScopedMap;
use base::ast::{self, Typed, DisplayEnv, MutVisitor};
use base::types::{self, RcKind, Type, Generic, Kind};
use base::error::Errors;
use base::symbol::{Symbol, SymbolRef, SymbolModule, Symbols};
use base::types::{KindEnv, TypeEnv, PrimitiveEnv, TcIdent, Alias, AliasData, TcType};
use base::instantiate::{self, Instantiator};
use kindcheck::{self, KindCheck};
use substitution::Substitution;
use unify::Error as UnifyError;
use unify;

use self::TypeError::*;

type ErrType = ast::ASTType<String>;


/// Type representing a single error when checking a type
#[derive(Debug, PartialEq)]
pub enum TypeError<I> {
    /// Variable has not been defined before it was used
    UndefinedVariable(I),
    /// Attempt to call a type which is not a function
    NotAFunction(ast::ASTType<I>),
    /// Type has not been defined before it was used
    UndefinedType(I),
    /// Type were expected to have a certain field
    UndefinedField(ast::ASTType<I>, I),
    /// Constructor type was found in a pattern but did not have the expected number of arguments
    PatternError(ast::ASTType<I>, usize),
    /// Errors found when trying to unify two types
    Unification(ast::ASTType<I>, ast::ASTType<I>, Vec<::unify_type::Error<I>>),
    /// Error were found when trying to unify the kinds of two types
    KindError(kindcheck::Error<I>),
    /// Errors found during renaming (overload resolution)
    Rename(::rename::RenameError),
    /// Multiple types were declared with the same name in the same expression
    DuplicateTypeDefinition(I),
    /// Type is not a type which has any fields
    InvalidFieldAccess(ast::ASTType<I>),
    /// Expected to find a record with the following fields
    UndefinedRecord {
        fields: Vec<I>,
    },
    /// Found a case expression without any alternatives
    EmptyCase,
}

impl<I> From<kindcheck::Error<I>> for TypeError<I>
    where I: PartialEq + Clone
{
    fn from(e: kindcheck::Error<I>) -> TypeError<I> {
        match e {
            UnifyError::Other(::kindcheck::KindError::UndefinedType(name)) => UndefinedType(name),
            e => KindError(e),
        }
    }
}

impl<I> From<::rename::RenameError> for TypeError<I> {
    fn from(e: ::rename::RenameError) -> TypeError<I> {
        TypeError::Rename(e)
    }
}

impl<I: fmt::Display + AsRef<str>> fmt::Display for TypeError<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TypeError::*;
        match *self {
            UndefinedVariable(ref name) => write!(f, "Undefined variable `{}`", name),
            NotAFunction(ref typ) => write!(f, "`{}` is not a function", typ),
            UndefinedType(ref name) => write!(f, "Type `{}` is not defined", name),
            UndefinedField(ref typ, ref field) => {
                write!(f, "Type `{}` does not have the field `{}`", typ, field)
            }
            Unification(ref expected, ref actual, ref errors) => {
                try!(writeln!(f,
                              "Expected the following types to be equal\nExpected: {}\nFound: \
                               {}\n{} errors were found during unification:",
                              expected,
                              actual,
                              errors.len()));
                if errors.is_empty() {
                    return Ok(());
                }
                for error in &errors[..errors.len() - 1] {
                    try!(::unify_type::fmt_error(error, f));
                    try!(writeln!(f, ""));
                }
                ::unify_type::fmt_error(errors.last().unwrap(), f)
            }
            PatternError(ref typ, expected_len) => {
                write!(f, "Type {} has {} to few arguments", typ, expected_len)
            }
            KindError(ref err) => ::kindcheck::fmt_kind_error(err, f),
            Rename(ref err) => write!(f, "{}", err),
            DuplicateTypeDefinition(ref id) => {
                write!(f,
                       "Type '{}' has been already been defined in this module",
                       id)
            }
            InvalidFieldAccess(ref typ) => {
                write!(f,
                       "Type '{}' is not a type which allows field accesses",
                       typ)
            }
            UndefinedRecord { ref fields } => {
                try!(write!(f, "No type found with the following fields: "));
                try!(write!(f, "{}", fields[0]));
                for field in &fields[1..] {
                    try!(write!(f, ", {}", field));
                }
                Ok(())
            }
            EmptyCase => write!(f, "`case` expression with no alternatives"),
        }
    }
}

type TcResult<T> = Result<T, TypeError<Symbol>>;

struct Environment<'a> {
    /// The global environment which the typechecker extracts types from
    environment: &'a (PrimitiveEnv + 'a),
    /// Stack allocated variables
    stack: ScopedMap<Symbol, TcType>,
    /// Types which exist in some scope (`type Test = ... in ...`)
    stack_types: ScopedMap<Symbol, (TcType, Alias<Symbol, TcType>)>,
}

impl<'a> KindEnv for Environment<'a> {
    fn find_kind(&self, type_name: &SymbolRef) -> Option<RcKind> {
        self.stack_types
            .get(type_name)
            .map(|&(_, ref alias)| {
                let mut kind = Kind::star();
                for arg in alias.args.iter().rev() {
                    kind = Kind::function(arg.kind.clone(), kind);
                }
                kind
            })
            .or_else(|| self.environment.find_kind(type_name))
    }
}

impl<'a> TypeEnv for Environment<'a> {
    fn find_type(&self, id: &SymbolRef) -> Option<&TcType> {
        self.stack.get(id).or_else(|| self.environment.find_type(id))
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, TcType>> {
        self.stack_types
            .get(id)
            .map(|&(_, ref alias)| alias)
            .or_else(|| self.environment.find_type_info(id))
    }

    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        self.stack_types
            .iter()
            .find(|&(_, &(_, ref alias))| {
                match alias.typ {
                    Some(ref typ) => {
                        match **typ {
                            Type::Record { fields: ref record_fields, .. } => {
                                fields.iter()
                                    .all(|name| record_fields.iter().any(|f| f.name.name_eq(name)))
                            }
                            _ => false,
                        }
                    }
                    None => false,
                }
            })
            .map(|t| (&(t.1).0, (t.1).1.typ.as_ref().unwrap()))
            .or_else(|| self.environment.find_record(fields))
    }
}

impl<'a> PrimitiveEnv for Environment<'a> {
    fn get_bool(&self) -> &TcType {
        self.environment.get_bool()
    }
}

/// Type returned from the main typecheck function to make sure that nested `type` and `let`
/// expressions dont overflow the stack
enum TailCall {
    Type(TcType),
    /// Returned from typechecking a `let` or `type` expresion to indicate that the expression body
    /// should be typechecked now.
    TailCall,
}

/// Struct which provides methods to typecheck expressions.
pub struct Typecheck<'a> {
    environment: Environment<'a>,
    symbols: SymbolModule<'a>,
    /// Mapping from the fresh symbol generated during typechecking to the symbol that was assigned
    /// during typechecking
    original_symbols: ScopedMap<Symbol, Symbol>,
    subs: Substitution<TcType>,
    inst: Instantiator,
    errors: Errors<ast::Spanned<TypeError<Symbol>>>,
}

/// Error returned when unsuccessfully typechecking an expression
pub type Error = Errors<ast::Spanned<TypeError<Symbol>>>;

impl<'a> Typecheck<'a> {
    /// Create a new typechecker which typechecks expressions in `module`
    pub fn new(module: String,
               symbols: &'a mut Symbols,
               environment: &'a (PrimitiveEnv + 'a))
               -> Typecheck<'a> {
        let symbols = SymbolModule::new(module, symbols);
        Typecheck {
            environment: Environment {
                environment: environment,
                stack: ScopedMap::new(),
                stack_types: ScopedMap::new(),
            },
            symbols: symbols,
            original_symbols: ScopedMap::new(),
            subs: Substitution::new(),
            inst: Instantiator::new(),
            errors: Errors::new(),
        }
    }

    fn error(&mut self, span: ast::Span, error: TypeError<Symbol>) -> TcType {
        self.errors.error(ast::Spanned {
            span: span,
            value: error,
        });
        self.subs.new_var()
    }

    fn bool(&self) -> TcType {
        self.environment.get_bool().clone()
    }

    fn find_at(&mut self, span: ast::Span, id: &Symbol) -> TcType {
        match self.find(id) {
            Ok(typ) => typ,
            Err(err) => self.error(span, err),
        }
    }

    fn find(&mut self, id: &Symbol) -> TcResult<TcType> {
        let symbols = &mut self.symbols;
        let subs = &mut self.subs;
        let inst = &mut self.inst;
        self.environment
            .find_type(&id)
            .ok_or_else(|| UndefinedVariable(id.clone()))
            .map(|typ| {
                let typ = subs.set_type(typ.clone());
                let typ = inst.instantiate(&typ, |_| subs.new_var());
                debug!("Find {} : {}",
                       symbols.string(id),
                       types::display_type(symbols, &typ));
                typ
            })
    }

    fn find_record(&self, fields: &[Symbol]) -> TcResult<(&TcType, &TcType)> {
        self.environment
            .find_record(fields)
            .ok_or(UndefinedRecord { fields: fields.to_owned() })
    }

    fn find_type_info(&self, id: &Symbol) -> TcResult<&Alias<Symbol, TcType>> {
        self.environment
            .find_type_info(id)
            .ok_or_else(|| UndefinedType(id.clone()))
    }

    fn stack_var(&mut self, id: Symbol, typ: TcType) {
        self.environment.stack.insert(id, typ);
    }

    fn stack_type(&mut self, id: Symbol, alias: &Alias<Symbol, TcType>) {
        // Insert variant constructors into the local scope
        if let Some(ref real_type) = alias.typ {
            if let Type::Variants(ref variants) = **real_type {
                for (name, typ) in variants.iter().cloned() {
                    let symbol = self.symbols.symbol(name.as_ref());
                    self.original_symbols.insert(symbol, name.clone());
                    self.stack_var(name, typ);
                }
            }
        }
        let generic_args = alias.args.iter().cloned().map(Type::generic).collect();
        let typ = Type::<_, TcType>::app(alias.as_ref().clone(), generic_args);
        {
            // FIXME: Workaround so that both the types name in this module and its global
            // name are imported. Without this aliases may not be traversed properly
            self.environment
                .stack_types
                .insert(alias.name.clone(), (typ.clone(), alias.clone()));
        }
        self.environment.stack_types.insert(id, (typ, alias.clone()));
    }

    fn enter_scope(&mut self) {
        self.environment.stack.enter_scope();
        self.environment.stack_types.enter_scope();
        self.original_symbols.enter_scope();
    }

    fn exit_scope(&mut self) {
        self.environment.stack.exit_scope();
        self.environment.stack_types.exit_scope();
        self.original_symbols.exit_scope();
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
    fn generalize_variables(&mut self, level: u32, expr: &mut ast::LExpr<TcIdent>) {
        // Replace all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b: 'a> {
            level: u32,
            tc: &'a mut Typecheck<'b>,
        }
        impl<'a, 'b> MutVisitor for ReplaceVisitor<'a, 'b> {
            type T = TcIdent;
            fn visit_identifier(&mut self, id: &mut TcIdent) {
                id.typ = self.tc.finish_type(self.level, id.typ.clone());
            }
        }
        let mut stack = mem::replace(&mut self.environment.stack, ScopedMap::new());
        for (_, vec) in stack.iter_mut() {
            for typ in vec {
                *typ = self.finish_type(level, typ.clone());
            }
        }
        mem::swap(&mut self.environment.stack, &mut stack);
        ReplaceVisitor {
                level: level,
                tc: self,
            }
            .visit_expr(expr);
    }

    /// Typecheck `expr`. If successful the type of the expression will be returned and all
    /// identifiers in `expr` will be filled with the inferred type
    pub fn typecheck_expr(&mut self, expr: &mut ast::LExpr<TcIdent>) -> Result<TcType, Error> {
        self.typecheck_expr_expected(expr, None)
    }

    pub fn typecheck_expr_expected(&mut self,
                                   expr: &mut ast::LExpr<TcIdent>,
                                   expected_type: Option<&TcType>)
                                   -> Result<TcType, Error> {
        self.subs.clear();
        self.environment.stack.clear();

        let mut typ = self.typecheck(expr);
        if let Some(expected) = expected_type {
            let span = expr.span(&ast::TcIdentEnvWrapper(&self.symbols));
            let expected = self.instantiate(expected);
            typ = self.unify_span(span, &expected, typ)
        }
        typ = self.finish_type(0, typ);
        typ = types::walk_move_type(typ, &mut unroll_app);
        self.generalize_variables(0, expr);
        if self.errors.has_errors() {
            Err(mem::replace(&mut self.errors, Errors::new()))
        } else {
            match ::rename::rename(&mut self.symbols, &self.environment, expr) {
                Ok(()) => {
                    debug!("Typecheck result: {}", typ);
                    Ok(typ)
                }
                Err(errors) => {
                    for ast::Spanned { span, value } in errors.errors {
                        self.errors.error(ast::Spanned {
                            span: span,
                            value: value.into(),
                        });
                    }
                    Err(mem::replace(&mut self.errors, Errors::new()))
                }
            }
        }
    }

    /// Main typechecking function. Returns the type of the expression if typechecking was
    /// successful
    fn typecheck(&mut self, mut expr: &mut ast::LExpr<TcIdent>) -> TcType {
        fn moving<T>(t: T) -> T {
            t
        }
        // How many scopes that have been entered in this "tailcall" loop
        let mut scope_count = 0;
        let returned_type;
        loop {
            match self.typecheck_(expr) {
                Ok(tailcall) => {
                    match tailcall {
                        TailCall::TailCall => {
                            // Call typecheck_ again with the next expression
                            expr = match moving(expr).value {
                                ast::Expr::Let(_, ref mut new_expr) |
                                ast::Expr::Type(_, ref mut new_expr) => new_expr,
                                _ => panic!("Only Let and Type expressions can tailcall"),
                            };
                            scope_count += 1;
                        }
                        TailCall::Type(typ) => {
                            returned_type = typ;
                            break;
                        }
                    }
                }
                Err(err) => {
                    returned_type = self.subs.new_var();
                    self.errors.error(ast::Spanned {
                        span: expr.span(&ast::TcIdentEnvWrapper(&self.symbols)),
                        value: err,
                    });
                    break;
                }
            }
        }
        for _ in 0..scope_count {
            self.exit_scope();
        }
        returned_type
    }

    fn typecheck_(&mut self,
                  expr: &mut ast::LExpr<TcIdent>)
                  -> Result<TailCall, TypeError<Symbol>> {
        match expr.value {
            ast::Expr::Identifier(ref mut id) => {
                if let Some(new) = self.original_symbols.get(&id.name) {
                    id.name = new.clone();
                }
                id.typ = try!(self.find(id.id()));
                Ok(TailCall::Type(id.typ.clone()))
            }
            ast::Expr::Literal(ref lit) => {
                Ok(TailCall::Type(match *lit {
                    ast::LiteralEnum::Integer(_) => Type::int(),
                    ast::LiteralEnum::Byte(_) => Type::byte(),
                    ast::LiteralEnum::Float(_) => Type::float(),
                    ast::LiteralEnum::String(_) => Type::string(),
                    ast::LiteralEnum::Char(_) => Type::char(),
                }))
            }
            ast::Expr::Call(ref mut func, ref mut args) => {
                let mut func_type = self.typecheck(&mut **func);
                for arg in args.iter_mut() {
                    let f = Type::function(vec![self.subs.new_var()], self.subs.new_var());
                    func_type = try!(self.unify(&f, func_type));
                    func_type = match func_type.as_function() {
                        Some((arg_ty, ret_ty)) => {
                            let actual = self.typecheck(arg);
                            let span = arg.span(&ast::TcIdentEnvWrapper(&self.symbols));
                            self.unify_span(span, arg_ty, actual);
                            ret_ty.clone()
                        }
                        None => return Err(NotAFunction(func_type.clone())),
                    };
                }
                Ok(TailCall::Type(func_type))
            }
            ast::Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = self.typecheck(&mut **pred);
                let span = pred.span(&ast::TcIdentEnvWrapper(&self.symbols));
                let bool_type = self.bool();
                self.unify_span(span, &bool_type, pred_type);
                let true_type = self.typecheck(&mut **if_true);
                let false_type = match *if_false {
                    Some(ref mut if_false) => self.typecheck(&mut **if_false),
                    None => Type::unit(),
                };
                // Both branches must unify to the same type
                self.unify(&true_type, false_type).map(TailCall::Type)
            }
            ast::Expr::BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = self.typecheck(&mut **lhs);
                let rhs_type = self.typecheck(&mut **rhs);
                let op_name = String::from(self.symbols.string(&op.name));
                let result = if op_name.starts_with('#') {
                    // Handle primitives
                    let arg_type = try!(self.unify(&lhs_type, rhs_type));
                    let offset;
                    let prim_type: TcType = if op_name[1..].starts_with("Int") {
                        offset = "Int".len();
                        Type::int()
                    } else if op_name[1..].starts_with("Float") {
                        offset = "Float".len();
                        Type::float()
                    } else if op_name[1..].starts_with("Char") {
                        offset = "Char".len();
                        Type::char()
                    } else if op_name[1..].starts_with("Byte") {
                        offset = "Byte".len();
                        Type::byte()
                    } else {
                        panic!("ICE: Unknown primitive type")
                    };
                    op.typ = Type::function(vec![prim_type.clone(), prim_type.clone()],
                                            prim_type.clone());
                    let typ = try!(self.unify(&prim_type, arg_type));
                    match &op_name[1 + offset..] {
                        "+" | "-" | "*" | "/" => Ok(typ),
                        "==" | "<" => Ok(self.bool()),
                        _ => Err(UndefinedVariable(op.name.clone())),
                    }
                } else {
                    match &*op_name {
                        "&&" | "||" => {
                            try!(self.unify(&lhs_type, rhs_type.clone()));
                            op.typ = Type::function(vec![self.bool(), self.bool()], self.bool());
                            self.unify(&self.bool(), lhs_type)
                        }
                        _ => {
                            op.typ = try!(self.find(op.id()));
                            let func_type = Type::function(vec![lhs_type, rhs_type],
                                                           self.subs.new_var());
                            let ret =
                                try!(self.unify(&op.typ, func_type)).as_function()
                                    .and_then(|(_, ret)| ret.as_function())
                                    .map(|(_, ret)| ret.clone())
                                    .expect("ICE: unify binop");

                            Ok(ret)
                        }
                    }
                };
                result.map(TailCall::Type)
            }
            ast::Expr::Tuple(ref mut exprs) => {
                assert!(exprs.len() == 0);
                Ok(TailCall::Type(Type::unit()))
            }
            ast::Expr::Match(ref mut expr, ref mut alts) => {
                let typ = self.typecheck(&mut **expr);
                let mut expected_alt_type = None;

                for alt in alts.iter_mut() {
                    self.enter_scope();
                    self.typecheck_pattern(&mut alt.pattern, typ.clone());
                    let mut alt_type = self.typecheck(&mut alt.expression);
                    self.exit_scope();
                    // All alternatives must unify to the same type
                    if let Some(ref expected) = expected_alt_type {
                        alt_type = try!(self.unify(expected, alt_type));
                    }
                    expected_alt_type = Some(alt_type);
                }
                expected_alt_type.ok_or(EmptyCase)
                    .map(TailCall::Type)
            }
            ast::Expr::Let(ref mut bindings, _) => {
                self.enter_scope();
                let level = self.subs.var_id();
                let is_recursive = bindings.iter().all(|bind| !bind.arguments.is_empty());
                // When the decfinitions are allowed to be mutually recursive
                if is_recursive {
                    for bind in bindings.iter_mut() {
                        let mut typ = self.subs.new_var();
                        if let Some(ref mut type_decl) = bind.typ {
                            *type_decl = self.refresh_symbols_in_type(type_decl.clone());
                            try!(self.kindcheck(type_decl, &mut []));
                            let decl = self.instantiate(type_decl);
                            typ = self.unify_span(bind.name.span(), &decl, typ);
                        }
                        self.typecheck_pattern(&mut bind.name, typ);
                        if let ast::Expr::Lambda(ref mut lambda) = bind.expression.value {
                            if let ast::Pattern::Identifier(ref name) = bind.name.value {
                                lambda.id.name = name.name.clone();
                            }
                        }
                    }
                }
                let mut types = Vec::new();
                for bind in bindings.iter_mut() {
                    // Functions which are declared as `let f x = ...` are allowed to be self
                    // recursive
                    let mut typ = if bind.arguments.is_empty() {
                        if let Some(ref mut type_decl) = bind.typ {
                            *type_decl = self.refresh_symbols_in_type(type_decl.clone());
                            try!(self.kindcheck(type_decl, &mut []));
                        }
                        self.typecheck(&mut bind.expression)
                    } else {
                        let function_type = match bind.typ {
                            Some(ref typ) => self.instantiate(typ),
                            None => self.subs.new_var(),
                        };
                        self.typecheck_lambda(function_type,
                                              &mut bind.arguments,
                                              &mut bind.expression)
                    };
                    debug!("let {:?} : {}",
                           bind.name,
                           types::display_type(&self.symbols, &typ));
                    if let Some(ref type_decl) = bind.typ {
                        typ = self.unify_span(bind.name.span(), type_decl, typ);
                    }
                    if !is_recursive {
                        // Merge the type declaration and the actual type
                        self.generalize_variables(level, &mut bind.expression);
                        self.typecheck_pattern(&mut bind.name, typ);
                    } else {
                        types.push(typ);
                    }
                }
                if is_recursive {
                    for (typ, bind) in types.into_iter().zip(bindings.iter_mut()) {
                        // Merge the variable we bound to the name and the type inferred
                        // in the expression
                        self.unify_span(bind.name.span(), &bind.type_of().clone(), typ);
                    }
                }
                // Once all variables inside the let has been unified we can quantify them
                debug!("Generalize {}", level);
                for bind in bindings {
                    self.generalize_variables(level, &mut bind.expression);
                    self.finish_binding(level, bind);
                }
                debug!("Typecheck `in`");
                Ok(TailCall::TailCall)
            }
            ast::Expr::FieldAccess(ref mut expr, ref mut field_access) => {
                let mut typ = self.typecheck(&mut **expr);
                debug!("FieldAccess {} . {:?}",
                       types::display_type(&self.symbols, &typ),
                       self.symbols.string(&field_access.name));
                self.subs.make_real(&mut typ);
                if let Type::Variable(_) = *typ {
                    // Attempt to find a record with `field_access` since inferring to a record
                    // with only `field_access` as the field is probably useless
                    let (record_type, _) = try!(self.find_record(&[field_access.name.clone()])
                        .map(|t| (t.0.clone(), t.1.clone())));
                    let record_type = self.instantiate(&record_type);
                    typ = try!(self.unify(&record_type, typ));
                }
                let record = self.remove_aliases(typ.clone());
                match *record {
                    Type::Record { ref fields, .. } => {
                        let field_type = fields.iter()
                            .find(|field| field.name.name_eq(field_access.id()))
                            .map(|field| field.typ.clone());
                        field_access.typ = match field_type {
                            Some(typ) => self.instantiate(&typ),
                            None => {
                                return Err(UndefinedField(typ.clone(), field_access.name.clone()))
                            }
                        };
                        Ok(TailCall::Type(field_access.typ.clone()))
                    }
                    _ => Err(InvalidFieldAccess(record.clone())),
                }
            }
            ast::Expr::Array(ref mut a) => {
                let mut expected_type = self.subs.new_var();
                for expr in &mut a.expressions {
                    let typ = self.typecheck(expr);
                    let span = expr.span(&ast::TcIdentEnvWrapper(&self.symbols));
                    expected_type = self.unify_span(span, &expected_type, typ);
                }
                a.id.typ = Type::array(expected_type);
                Ok(TailCall::Type(a.id.typ.clone()))
            }
            ast::Expr::Lambda(ref mut lambda) => {
                let loc = format!("lambda:{}", expr.location);
                lambda.id.name = self.symbols.symbol(loc);
                let function_type = self.subs.new_var();
                let typ =
                    self.typecheck_lambda(function_type, &mut lambda.arguments, &mut lambda.body);
                lambda.id.typ = typ.clone();
                Ok(TailCall::Type(typ))
            }
            ast::Expr::Type(ref mut bindings, ref expr) => {
                self.enter_scope();
                // Rename the types so they get a name which is distinct from types from other
                // modules
                for bind in bindings.iter_mut() {
                    let s = String::from(self.symbols.string(&bind.alias.name));
                    let new = self.symbols.scoped_symbol(&s);
                    self.original_symbols.insert(bind.alias.name.clone(), new.clone());
                    // Rename the aliase's name to its global name
                    Alias::make_mut(&mut bind.alias).name = new;
                }
                for bind in bindings.iter_mut() {
                    let typ = Alias::make_mut(&mut bind.alias)
                        .typ
                        .as_mut()
                        .expect("Expected binding to have an aliased type");
                    *typ = self.refresh_symbols_in_type(typ.clone());
                }
                {
                    let subs = Substitution::new();
                    let mut check = KindCheck::new(&self.environment, &self.symbols, subs);
                    // Setup kind variables for all type variables and insert the types in the
                    // this type expression into the kindcheck environment
                    for bind in bindings.iter_mut() {
                        // Create the kind for this binding
                        // Test a b: 2 -> 1 -> *
                        // and bind the same variables to the arguments of the type binding
                        // ('a' and 'b' in the example)
                        let mut id_kind = check.star_kind();
                        let alias = Alias::make_mut(&mut bind.alias);
                        for gen in alias.args.iter_mut().rev() {
                            gen.kind = check.subs.new_var();
                            id_kind = Kind::function(gen.kind.clone(), id_kind);
                        }
                        check.add_local(alias.name.clone(), id_kind);
                    }

                    // Kindcheck all the types in the environment
                    for bind in bindings.iter_mut() {
                        check.set_variables(&bind.alias.args);
                        let typ = Alias::make_mut(&mut bind.alias)
                            .typ
                            .as_mut()
                            .expect("Expected binding to have an aliased type");
                        try!(check.kindcheck_type(typ));
                    }

                    // All kinds are now inferred so replace the kinds store in the AST
                    for bind in bindings.iter_mut() {
                        let alias = Alias::make_mut(&mut bind.alias);
                        if let Some(ref mut typ) = alias.typ {
                            *typ = check.finalize_type(typ.clone());
                        }
                        for arg in &mut alias.args {
                            *arg = check.finalize_generic(&arg);
                        }
                    }
                }

                // Finally insert the declared types into the global scope
                for bind in bindings {
                    let args = &bind.alias.args;
                    debug!("HELP {} \n{:?}", self.symbols.string(&bind.name), args);
                    if self.environment.stack_types.get(&bind.name).is_some() {
                        self.errors.error(ast::Spanned {
                            span: expr.span(&ast::TcIdentEnvWrapper(&self.symbols)),
                            value: DuplicateTypeDefinition(bind.name.clone()),
                        });
                    } else {
                        self.stack_type(bind.name.clone(), &bind.alias);
                    }
                }
                Ok(TailCall::TailCall)
            }
            ast::Expr::Record { typ: ref mut id, ref mut types, exprs: ref mut fields } => {
                let types = try!(types.iter_mut()
                    .map(|&mut (ref mut symbol, ref mut typ)| {
                        if let Some(ref mut typ) = *typ {
                            *typ = self.refresh_symbols_in_type(typ.clone());
                        }
                        let alias = try!(self.find_type_info(symbol));

                        Ok(types::Field {
                            name: symbol.clone(),
                            typ: alias.clone(),
                        })
                    })
                    .collect::<TcResult<Vec<_>>>());
                let fields = try!(fields.iter_mut()
                    .map(|field| {
                        match field.1 {
                                Some(ref mut expr) => Ok(self.typecheck(expr)),
                                None => self.find(&field.0),
                            }
                            .map(|typ| {
                                types::Field {
                                    name: field.0.clone(),
                                    typ: typ,
                                }
                            })
                    })
                    .collect::<TcResult<Vec<_>>>());
                let result = self.find_record(&fields.iter()
                        .map(|f| f.name.clone())
                        .collect::<Vec<_>>())
                    .map(|t| (t.0.clone(), t.1.clone()));
                let (id_type, record_type) = match result {
                    Ok(x) => x,
                    Err(_) => {
                        id.typ = Type::record(types.clone(), fields);
                        return Ok(TailCall::Type(id.typ.clone()));
                    }
                };
                let id_type = self.instantiate(&id_type);
                let record_type = self.instantiate_(&record_type);
                try!(self.unify(&Type::record(types, fields), record_type));
                id.typ = id_type.clone();
                Ok(TailCall::Type(id_type.clone()))
            }
            ast::Expr::Block(ref mut exprs) => {
                let (last, exprs) = exprs.split_last_mut().expect("Expr in block");
                for expr in exprs {
                    self.typecheck(expr);
                }
                Ok(TailCall::Type(self.typecheck(last)))
            }
        }
    }

    fn typecheck_lambda(&mut self,
                        function_type: TcType,
                        arguments: &mut [TcIdent],
                        body: &mut ast::LExpr<TcIdent>)
                        -> TcType {
        self.enter_scope();
        let mut arg_types = Vec::new();
        {
            let mut iter1 = function_arg_iter(self, function_type);
            let mut iter2 = arguments.iter_mut();
            while let (Some(arg_type), Some(arg)) = (iter1.next(), iter2.next()) {
                arg.typ = arg_type;
                arg_types.push(arg.typ.clone());
                iter1.tc.stack_var(arg.name.clone(), arg.typ.clone());
            }
        }
        let body_type = self.typecheck(body);
        self.exit_scope();
        Type::function(arg_types, body_type)
    }

    fn typecheck_pattern(&mut self,
                         pattern: &mut ast::LPattern<TcIdent>,
                         match_type: TcType)
                         -> TcType {
        let span = pattern.span();
        match pattern.value {
            ast::Pattern::Constructor(ref mut id, ref mut args) => {
                if let Some(new) = self.original_symbols.get(&id.name) {
                    id.name = new.clone();
                }
                // Find the enum constructor and return the types for its arguments
                let ctor_type = self.find_at(span, &id.name);
                let return_type = match self.typecheck_pattern_rec(args, ctor_type) {
                    Ok(return_type) => return_type,
                    Err(err) => self.error(span, err),
                };
                self.unify_span(span, &match_type, return_type)
            }
            ast::Pattern::Record { ref mut id, types: ref mut associated_types, ref fields } => {
                id.typ = match_type.clone();
                let mut match_type = self.remove_alias(match_type);
                let mut types = Vec::new();
                let new_type = match *match_type {
                    Type::Record { fields: ref expected_fields, .. } => {
                        for pattern_field in fields {
                            let found_field = expected_fields.iter()
                                .find(|expected_field| {
                                    pattern_field.0
                                        .name_eq(&expected_field.name)
                                });
                            let expected_field = match found_field {
                                Some(expected) => expected,
                                None => {
                                    self.error(span,
                                               UndefinedField(match_type.clone(),
                                                              pattern_field.0.clone()));
                                    continue;
                                }
                            };
                            let var = self.subs.new_var();
                            types.push(var.clone());
                            self.unify_span(span, &var, expected_field.typ.clone());
                        }
                        None
                    }
                    _ => {
                        let fields: Vec<_> = fields.iter().map(|t| t.0.clone()).collect();
                        // actual_type is the record (not hidden behind an alias)
                        let (mut typ, mut actual_type) = match self.find_record(&fields)
                            .map(|t| (t.0.clone(), t.1.clone())) {
                            Ok(typ) => typ,
                            Err(_) => {
                                let fields = fields.iter()
                                    .map(|field| {
                                        types::Field {
                                            name: field.clone(),
                                            typ: self.subs.new_var(),
                                        }
                                    })
                                    .collect();
                                let t = Type::record(Vec::new(), fields);
                                (t.clone(), t)
                            }
                        };
                        typ = self.instantiate_(&typ);
                        actual_type = self.instantiate_(&actual_type);
                        self.unify_span(span, &match_type, typ);
                        match *actual_type {
                            Type::Record { fields: ref record_types, .. } => {
                                types.extend(record_types.iter().map(|f| f.typ.clone()));
                            }
                            _ => {
                                panic!("Expected record found {}",
                                       types::display_type(&self.symbols, &match_type))
                            }
                        }
                        Some(actual_type)
                    }
                };
                match_type = new_type.unwrap_or(match_type);
                for (field, field_type) in fields.iter().zip(types) {
                    let name = match field.1 {
                        Some(ref bind_name) => bind_name,
                        None => &field.0,
                    };
                    self.stack_var(name.clone(), field_type);
                }
                match *match_type {
                    Type::Record { ref types, .. } => {
                        for field in associated_types.iter_mut() {
                            let name = match field.1 {
                                Some(ref bind_name) => bind_name.clone(),
                                None => field.0.clone(),
                            };
                            // The `types` in the record type should have a type matching the
                            // `name`
                            let field_type = types.iter()
                                .find(|field| field.name.name_eq(&name));
                            match field_type {
                                Some(field_type) => {
                                    // This forces refresh_type to remap the name a type was given
                                    // in this module to its actual name
                                    self.original_symbols
                                        .insert(name.clone(), field_type.typ.name.clone());
                                    self.stack_type(name, &field_type.typ);
                                }
                                None => {
                                    self.error(span, UndefinedField(match_type.clone(), name));
                                }
                            }
                        }
                    }
                    _ => panic!("Expected a record"),
                }
                match_type
            }
            ast::Pattern::Identifier(ref mut id) => {
                self.stack_var(id.id().clone(), match_type.clone());
                id.typ = match_type.clone();
                match_type
            }
        }
    }

    fn typecheck_pattern_rec(&mut self, args: &[TcIdent], typ: TcType) -> TcResult<TcType> {
        if args.len() == 0 {
            return Ok(typ);
        }
        match typ.as_function() {
            Some((arg, ret)) => {
                self.stack_var(args[0].id().clone(), arg.clone());
                self.typecheck_pattern_rec(&args[1..], ret.clone())
            }
            None => {
                Err(PatternError(typ.clone(), args.len()))
            },
        }
    }

    fn kindcheck(&self, typ: &mut TcType, args: &mut [Generic<Symbol>]) -> TcResult<()> {
        let subs = Substitution::new();
        let mut check = super::kindcheck::KindCheck::new(&self.environment, &self.symbols, subs);
        check.set_variables(args);
        try!(check.kindcheck_type(typ));
        Ok(())
    }

    fn finish_binding(&mut self, level: u32, bind: &mut ast::Binding<TcIdent>) {
        match bind.name.value {
            ast::Pattern::Identifier(ref mut id) => {
                id.typ = self.finish_type(level, id.typ.clone());
                debug!("{}: {}",
                       self.symbols.string(&id.name),
                       types::display_type(&self.symbols, &id.typ));
                self.intersect_type(level, &id.name, &id.typ);
            }
            ast::Pattern::Record { ref id, ref mut fields, .. } => {
                debug!("{{ .. }}: {}",
                       types::display_type(&self.symbols,
                                           &bind.expression
                                               .env_type_of(&self.environment)));
                let record_type = self.remove_alias(id.typ.clone());
                with_pattern_types(fields, &record_type, |field_name, field_type| {
                    self.intersect_type(level, field_name, field_type);
                });
            }
            ast::Pattern::Constructor(ref id, ref arguments) => {
                debug!("{}: {}",
                       self.symbols.string(&id.name),
                       types::display_type(&self.symbols,
                                           &bind.expression
                                               .env_type_of(&self.environment)));
                for arg in arguments {
                    self.intersect_type(level, &arg.name, &arg.typ);
                }
            }
        }
    }

    fn intersect_type(&mut self, level: u32, symbol: &Symbol, symbol_type: &TcType) {
        let mut typ = None;
        if let Some(existing_types) = self.environment.stack.get_all(symbol) {
            if existing_types.len() >= 2 {
                let existing_type = &existing_types[existing_types.len() - 2];
                debug!("Intersect\n{} <> {}",
                       types::display_type(&self.symbols, existing_type),
                       types::display_type(&self.symbols, symbol_type));
                let mut state = ::unify_type::State::new(&self.environment);
                let result =
                    unify::intersection(&self.subs, &mut state, existing_type, symbol_type);
                debug!("Intersect result {}", result);
                typ = Some(result);
            }
        }
        if let Some(typ) = typ {
            *self.environment.stack.get_mut(&symbol).unwrap() = self.finish_type(level, typ);
        }
    }

    /// Finish a type by replacing all unbound type variables above `level` with generics
    fn finish_type(&mut self, level: u32, typ: TcType) -> TcType {
        let generic = {
            let vars = self.inst.named_variables.borrow();
            let max_var = vars.keys()
                .fold("a",
                      |max, current| ::std::cmp::max(max, self.symbols.string(&current)));
            String::from(max_var)
        };
        let mut i = 0;
        self.finish_type_(level, &generic, &mut i, typ)
    }

    fn finish_type_(&mut self, level: u32, generic: &str, i: &mut i32, typ: TcType) -> TcType {
        types::walk_move_type(typ,
                              &mut |typ| {
            let replacement = self.subs
                .replace_variable(typ)
                .map(|t| self.finish_type_(level, generic, i, t));
            let mut typ = typ;
            if let Some(ref t) = replacement {
                debug!("{} ==> {}",
                       types::display_type(&self.symbols, &typ),
                       types::display_type(&self.symbols, t));
                typ = &**t;
            }
            match *typ {
                Type::Variable(ref var) if self.subs.get_level(var.id) > level => {
                    let generic = format!("{}{}", generic, i);
                    *i += 1;
                    let id = self.symbols.symbol(generic);
                    let gen: TcType = Type::generic(Generic {
                        kind: var.kind.clone(),
                        id: id.clone(),
                    });
                    self.subs.insert(var.id, gen.clone());
                    self.inst
                        .named_variables
                        .borrow_mut()
                        .insert(id, gen.clone());
                    Some(gen)
                }
                _ => unroll_app(typ).or(replacement.clone()),
            }
        })
    }

    fn refresh_symbols_in_type(&mut self, typ: TcType) -> TcType {
        let mut f = |typ: &Type<Symbol, TcType>| {
            match *typ {
                Type::Alias(ref alias) => {
                    self.original_symbols
                        .get(&alias.name)
                        .or_else(|| {
                            self.environment
                                .find_type_info(&alias.name)
                                .map(|found_alias| &found_alias.name)
                        })
                        .cloned()
                        .map(|new_id| {
                            Type::alias(new_id,
                                        alias.args.clone(),
                                        alias.typ.clone().expect("Type"))
                        })
                }
                Type::Id(ref id) => {
                    // Substitute the Id by its alias if possible
                    let new_id = self.original_symbols
                        .get(id)
                        .unwrap_or(id);
                    self.environment
                        .find_type_info(new_id)
                        .map(|alias| alias.clone().into_type())
                        .or_else(|| if id == new_id {
                            None
                        } else {
                            Some(Type::id(new_id.clone()))
                        })
                }
                Type::Variants(ref variants) => {
                    let iter = || {
                        variants.iter()
                            .map(|var| self.original_symbols.get(&var.0))
                    };
                    if iter().any(|opt| opt.is_some()) {
                        // If any of the variants requires a symbol replacement
                        // we create a new type
                        Some(Type::variants(iter()
                            .zip(variants.iter())
                            .map(|(new, old)| {
                                match new {
                                    Some(new) => (new.clone(), old.1.clone()),
                                    None => old.clone(),
                                }
                            })
                            .collect()))
                    } else {
                        None
                    }
                }
                _ => None,
            }
        };
        types::walk_move_type(typ, &mut f)
    }

    fn unify_span(&mut self, span: ast::Span, expected: &TcType, actual: TcType) -> TcType {
        match self.unify(expected, actual) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.error(ast::Spanned {
                    span: span,
                    value: err,
                });
                self.subs.new_var()
            }
        }
    }

    fn unify(&self, expected: &TcType, mut actual: TcType) -> TcResult<TcType> {
        debug!("Unify {} <=> {}",
               types::display_type(&self.symbols, expected),
               types::display_type(&self.symbols, &actual));
        let mut state = ::unify_type::State::new(&self.environment);
        match unify::unify(&self.subs, &mut state, expected, &actual) {
            Ok(typ) => Ok(self.subs.set_type(typ)),
            Err(errors) => {
                let mut expected = expected.clone();
                expected = self.subs.set_type(expected);
                actual = self.subs.set_type(actual);
                debug!("Error '{:?}' between:\n>> {}\n>> {}",
                       errors,
                       types::display_type(&self.symbols, &expected),
                       types::display_type(&self.symbols, &actual));
                Err(TypeError::Unification(expected, actual, apply_subs(&self.subs, errors.errors)))
            }
        }
    }

    fn remove_alias(&self, typ: TcType) -> TcType {
        instantiate::remove_alias(&self.environment, typ)
    }

    fn remove_aliases(&self, typ: TcType) -> TcType {
        instantiate::remove_aliases(&self.environment, typ)
    }

    fn type_of_alias(&self,
                     id: &AliasData<Symbol, TcType>,
                     arguments: &[TcType])
                     -> Result<Option<TcType>, ::unify_type::Error<Symbol>> {
        Ok(instantiate::type_of_alias(id, arguments))
    }

    fn instantiate(&mut self, typ: &TcType) -> TcType {
        let subs = &mut self.subs;
        self.inst.instantiate(typ, |_| subs.new_var())
    }

    fn instantiate_(&mut self, typ: &TcType) -> TcType {
        let subs = &mut self.subs;
        self.inst.instantiate_(typ, |_| subs.new_var())
    }
}

fn with_pattern_types<F>(fields: &[(Symbol, Option<Symbol>)], typ: &TcType, mut f: F)
    where F: FnMut(&Symbol, &TcType)
{
    if let Type::Record { fields: ref field_types, .. } = **typ {
        for field in fields {
            // If the field in the pattern does not exist (undefined field error) then skip it as
            // the error itself will already have been reported
            if let Some(associated_type) = field_types.iter()
                .find(|type_field| type_field.name.name_eq(&field.0)) {
                f(&field.0, &associated_type.typ);
            }
        }
    }
}

fn apply_subs(subs: &Substitution<TcType>,
              error: Vec<::unify_type::Error<Symbol>>)
              -> Vec<::unify_type::Error<Symbol>> {
    use unify::Error::*;
    error.into_iter()
        .map(|error| {
            match error {
                TypeMismatch(expected, actual) => {
                    TypeMismatch(subs.set_type(expected), subs.set_type(actual))
                }
                Occurs(var, typ) => Occurs(var, subs.set_type(typ)),
                Other(::unify_type::TypeError::UndefinedType(id)) => {
                    Other(::unify_type::TypeError::UndefinedType(id))
                }
                Other(::unify_type::TypeError::FieldMismatch(expected, actual)) => {
                    UnifyError::Other(::unify_type::TypeError::FieldMismatch(expected, actual))
                }
                Other(::unify_type::TypeError::SelfRecursive(t)) => {
                    UnifyError::Other(::unify_type::TypeError::SelfRecursive(t))
                }
            }
        })
        .collect()
}


pub fn extract_generics(args: &[TcType]) -> Vec<Generic<Symbol>> {
    args.iter()
        .map(|arg| {
            match **arg {
                Type::Generic(ref gen) => gen.clone(),
                _ => {
                    panic!("The type on the lhs of a type binding did not have all generic \
                            arguments")
                }
            }
        })
        .collect()
}

fn get_alias_app<'a>(env: &'a TypeEnv,
                     typ: &'a TcType)
                     -> Option<(&'a AliasData<Symbol, TcType>, &'a [TcType])> {
    match **typ {
        Type::Alias(ref alias) => Some((alias, &[][..])),
        Type::App(ref alias, ref args) => {
            match **alias {
                Type::Alias(ref alias) => Some((alias, args)),
                _ => None,
            }
        }
        _ => {
            typ.as_alias()
                .and_then(|(id, args)| env.find_type_info(id).map(|alias| (&**alias, &args[..])))
        }
    }
}

struct FunctionArgIter<'a, 'b: 'a> {
    tc: &'a mut Typecheck<'b>,
    typ: TcType,
}

impl<'a, 'b> Iterator for FunctionArgIter<'a, 'b> {
    type Item = TcType;
    fn next(&mut self) -> Option<TcType> {
        loop {
            let (arg, new) = match self.typ.as_function() {
                Some((arg, ret)) => (Some(arg.clone()), ret.clone()),
                None => {
                    match get_alias_app(&self.tc.environment, &self.typ) {
                        Some((alias, args)) => {
                            match self.tc.type_of_alias(alias, args) {
                                Ok(Some(typ)) => (None, typ.clone()),
                                Ok(None) => return None,
                                Err(_) => return Some(self.tc.subs.new_var()),
                            }
                        }
                        None => return Some(self.tc.subs.new_var()),
                    }
                }
            };
            self.typ = new;
            if let Some(arg) = arg {
                return Some(arg);
            }
        }
    }
}

fn function_arg_iter<'a, 'b>(tc: &'a mut Typecheck<'b>, typ: TcType) -> FunctionArgIter<'a, 'b> {
    FunctionArgIter { tc: tc, typ: typ }
}

/// Removes layers of `Type::App`.
///
/// Example:
///
/// ```
/// extern crate gluon_base;
/// extern crate gluon_check;
///
/// use gluon_base::types::{Type, TcType, BuiltinType};
/// use gluon_check::typecheck::unroll_app;
///
/// # fn main() {
/// let i: TcType = Type::int();
/// let s: TcType = Type::string();
/// assert_eq!(unroll_app(&*Type::app(Type::app(i.clone(), vec![s.clone()]), vec![i.clone()])),
///            Some(Type::app(i.clone(), vec![s.clone(), i.clone()])));
/// assert_eq!(unroll_app(&*Type::app(Type::app(i.clone(), vec![i.clone()]), vec![s.clone()])),
///            Some(Type::app(i.clone(), vec![i.clone(), s.clone()])));
/// let f: TcType = Type::builtin(BuiltinType::Function);
/// assert_eq!(unroll_app(&*Type::app(Type::app(f.clone(), vec![i.clone()]), vec![s.clone()])),
///            Some(Type::function(vec![i.clone()], s.clone())));
/// # }
/// ```
pub fn unroll_app(typ: &Type<Symbol>) -> Option<TcType> {
    let mut args = Vec::new();
    let mut current = match *typ {
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
        _ => return None,
    };
    while let Type::App(ref l, ref rest) = **current {
        args.extend(rest.iter().rev().cloned());
        current = l;
    }
    if args.is_empty() {
        None
    } else {
        args.reverse();
        Some(Type::app(current.clone(), args))
    }
}

