use std::fmt;
use std::mem;

use base::scoped_map::ScopedMap;
use base::ast;
use base::ast::{Typed, DisplayEnv, MutVisitor};
use base::types;
use base::types::{RcKind, Type, Generic, Kind};
use base::error::Errors;
use base::symbol::{Symbol, SymbolModule, Symbols};
use base::types::{KindEnv, TypeEnv, PrimitiveEnv, TcIdent, Alias, TcType};
use instantiate::{AliasInstantiator, Instantiator, unroll_app};
use kindcheck;
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

impl<I> From<kindcheck::Error<I>> for TypeError<I> where I: PartialEq + Clone
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
    environment: &'a (PrimitiveEnv + 'a),
    stack: ScopedMap<Symbol, TcType>,
    stack_types: ScopedMap<Symbol, (TcType, Alias<Symbol, TcType>)>,
}

impl<'a> KindEnv for Environment<'a> {
    fn find_kind(&self, type_name: &Symbol) -> Option<RcKind> {
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
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
        self.stack.get(id).or_else(|| self.environment.find_type(id))
    }

    fn find_type_info(&self, id: &Symbol) -> Option<&Alias<Symbol, TcType>> {
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
                                      .all(|name| {
                                          record_fields.iter().any(|f| f.name.name_eq(name))
                                      })
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

enum TailCall {
    Type(TcType),
    TailCall,
}

/// Struct which provides methods to typecheck expressions.
pub struct Typecheck<'a> {
    environment: Environment<'a>,
    symbols: SymbolModule<'a>,
    /// Mapping from the fresh symbol generated during typechecking to the symbol that was assigned
    /// during typechecking
    original_symbols: ScopedMap<Symbol, Symbol>,
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
            inst: Instantiator::new(),
            errors: Errors::new(),
        }
    }

    fn bool(&self) -> TcType {
        self.environment.get_bool().clone()
    }

    fn find(&mut self, id: &Symbol) -> TcResult<TcType> {
        let symbols = &mut self.symbols;
        let inst = &mut self.inst;
        self.environment
            .find_type(&id)
            .ok_or_else(|| UndefinedVariable(id.clone()))
            .map(|typ| {
                let typ = inst.set_type(typ.clone());
                let typ = inst.instantiate(&typ);
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

    fn stack_type(&mut self,
                  id: Symbol,
                  typ: TcType,
                  generics: Vec<Generic<Symbol>>,
                  real_type: Option<TcType>) {
        // Insert variant constructors into the local scope
        if let Some(ref real_type) = real_type {
            if let Type::Variants(ref variants) = **real_type {
                for (name, typ) in variants.iter().cloned() {
                    let symbol = self.symbols.symbol(name.as_ref());
                    self.original_symbols.insert(symbol, name.clone());
                    self.stack_var(name, typ);
                }
            }
        }
        let mut alias = Alias {
            name: id.clone(),
            args: generics,
            typ: real_type,
        };
        {
            let alias_id = match *typ {
                Type::Id(ref alias_id) => alias_id,
                Type::Data(ref alias_id, _) => {
                    match **alias_id {
                        Type::Id(ref alias_id) => alias_id,
                        _ => unreachable!(),
                    }
                }
                _ => unreachable!(),
            };
            alias.name = alias_id.clone();
            // FIXME: Workaround so that both the types name in this module and its global
            // name are imported. Without this aliases may not be traversed properly
            self.environment
                .stack_types
                .insert(alias_id.clone(), (typ.clone(), alias.clone()));
        }
        self.environment.stack_types.insert(id, (typ, alias));
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
        self.inst.subs.clear();
        self.environment.stack.clear();

        let mut typ = self.typecheck(expr).unwrap();
        if self.errors.has_errors() {
            Err(mem::replace(&mut self.errors, Errors::new()))
        } else {
            typ = self.finish_type(0, typ);
            typ = types::walk_move_type(typ, &mut unroll_app);
            self.generalize_variables(0, expr);
            match ::rename::rename(&mut self.symbols, &self.environment, expr) {
                Ok(()) => Ok(typ),
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

    fn typecheck(&mut self, mut expr: &mut ast::LExpr<TcIdent>) -> TcResult<TcType> {
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
                    returned_type = self.inst.subs.new_var();
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
        Ok(returned_type)
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
                    ast::LiteralEnum::Float(_) => Type::float(),
                    ast::LiteralEnum::String(_) => Type::string(),
                    ast::LiteralEnum::Char(_) => Type::char(),
                }))
            }
            ast::Expr::Call(ref mut func, ref mut args) => {
                let mut func_type = try!(self.typecheck(&mut **func));
                for arg in args.iter_mut() {
                    let f = Type::function(vec![self.inst.subs.new_var()],
                                           self.inst.subs.new_var());
                    func_type = try!(self.unify(&f, func_type));
                    func_type = match *func_type {
                        Type::Function(ref arg_type, ref ret) => {
                            assert!(arg_type.len() == 1);
                            let actual = try!(self.typecheck(arg));
                            let span = arg.span(&ast::TcIdentEnvWrapper(&self.symbols));
                            self.unify_span(span, &arg_type[0], actual);
                            ret.clone()
                        }
                        _ => return Err(NotAFunction(func_type.clone())),
                    };
                }
                Ok(TailCall::Type(func_type))
            }
            ast::Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut **pred));
                try!(self.unify(&self.bool(), pred_type));
                let true_type = try!(self.typecheck(&mut **if_true));
                let false_type = match *if_false {
                    Some(ref mut if_false) => try!(self.typecheck(&mut **if_false)),
                    None => Type::unit(),
                };
                self.unify(&true_type, false_type).map(TailCall::Type)
            }
            ast::Expr::BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut **lhs));
                let rhs_type = try!(self.typecheck(&mut **rhs));
                let op_name = String::from(self.symbols.string(&op.name));
                let result = if op_name.starts_with('#') {
                    let arg_type = try!(self.unify(&lhs_type, rhs_type));
                    let offset;
                    let typ = if op_name[1..].starts_with("Int") {
                        offset = "Int".len();
                        op.typ = Type::function(vec![Type::int(), Type::int()], Type::int());
                        try!(self.unify(&Type::int(), arg_type))
                    } else if op_name[1..].starts_with("Float") {
                        offset = "Float".len();
                        op.typ = Type::function(vec![Type::float(), Type::float()], Type::float());
                        try!(self.unify(&Type::float(), arg_type))
                    } else {
                        panic!("ICE: Unknown primitive type")
                    };
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
                                                           self.inst.subs.new_var());
                            match *try!(self.unify(&op.typ, func_type)) {
                                Type::Function(_, ref return_type) => {
                                    match **return_type {
                                        Type::Function(_, ref return_type) => {
                                            Ok(return_type.clone())
                                        }
                                        _ => panic!("ICE: unify binop"),
                                    }
                                }
                                _ => panic!("ICE: unify binop"),
                            }
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
                let typ = try!(self.typecheck(&mut **expr));
                let mut expected_alt_type = None;

                for alt in alts.iter_mut() {
                    self.enter_scope();
                    try!(self.typecheck_pattern(&mut alt.pattern, typ.clone()));
                    let mut alt_type = try!(self.typecheck(&mut alt.expression));
                    self.exit_scope();
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
                let level = self.inst.subs.var_id();
                let is_recursive = bindings.iter().all(|bind| !bind.arguments.is_empty());
                if is_recursive {
                    for bind in bindings.iter_mut() {
                        let mut typ = self.inst.subs.new_var();
                        if let Some(ref mut type_decl) = bind.typ {
                            *type_decl = self.refresh_symbols_in_type(type_decl.clone());
                            try!(self.kindcheck(type_decl, &mut []));
                            let decl = self.inst.instantiate(type_decl);
                            typ = try!(self.unify(&decl, typ));
                        }
                        try!(self.typecheck_pattern(&mut bind.name, typ));
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
                        try!(self.typecheck(&mut bind.expression))
                    } else {
                        let function_type = match bind.typ {
                            Some(ref typ) => typ.clone(),
                            None => self.inst.subs.new_var(),
                        };
                        try!(self.typecheck_lambda(function_type,
                                                   &mut bind.arguments,
                                                   &mut bind.expression))
                    };
                    debug!("let {:?} : {}",
                           bind.name,
                           types::display_type(&self.symbols, &typ));
                    if let Some(ref type_decl) = bind.typ {
                        typ = try!(self.unify(type_decl, typ));
                    }
                    if !is_recursive {
                        // Merge the type declaration and the actual type
                        self.generalize_variables(level, &mut bind.expression);
                        try!(self.typecheck_pattern(&mut bind.name, typ));
                    } else {
                        types.push(typ);
                    }
                }
                if is_recursive {
                    for (typ, bind) in types.into_iter().zip(bindings.iter_mut()) {
                        // Merge the variable we bound to the name and the type inferred
                        // in the expression
                        try!(self.unify(&bind.type_of().clone(), typ));
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
                let mut typ = try!(self.typecheck(&mut **expr));
                debug!("FieldAccess {} . {:?}",
                       types::display_type(&self.symbols, &typ),
                       self.symbols.string(&field_access.name));
                self.inst.subs.make_real(&mut typ);
                if let Type::Variable(_) = *typ {
                    let (record_type, _) = try!(self.find_record(&[field_access.name.clone()])
                                                    .map(|t| (t.0.clone(), t.1.clone())));
                    let record_type = self.inst.instantiate(&record_type);
                    typ = try!(self.unify(&record_type, typ));
                }
                let record = self.remove_aliases(typ.clone());
                match *record {
                    Type::Record { ref fields, .. } => {
                        let field_type = fields.iter()
                                               .find(|field| field.name.name_eq(field_access.id()))
                                               .map(|field| field.typ.clone());
                        field_access.typ = match field_type {
                            Some(typ) => self.inst.instantiate(&typ),
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
                let mut expected_type = self.inst.subs.new_var();
                for expr in &mut a.expressions {
                    let typ = try!(self.typecheck(expr));
                    expected_type = try!(self.unify(&expected_type, typ));
                }
                a.id.typ = Type::array(expected_type);
                Ok(TailCall::Type(a.id.typ.clone()))
            }
            ast::Expr::Lambda(ref mut lambda) => {
                let loc = format!("lambda:{}", expr.location);
                lambda.id.name = self.symbols.symbol(loc);
                let function_type = self.inst.subs.new_var();
                let typ = try!(self.typecheck_lambda(function_type,
                                                     &mut lambda.arguments,
                                                     &mut lambda.body));
                lambda.id.typ = typ.clone();
                Ok(TailCall::Type(typ))
            }
            ast::Expr::Type(ref mut bindings, ref expr) => {
                self.enter_scope();
                for bind in bindings.iter_mut() {
                    let s = String::from(self.symbols.string(&bind.alias.name));
                    let new = self.symbols.scoped_symbol(&s);
                    self.original_symbols.insert(bind.alias.name.clone(), new.clone());
                    // Rename the aliase's name to its global name
                    bind.alias.name = new;
                }
                for bind in bindings.iter_mut() {
                    let typ = bind.alias
                                  .typ
                                  .as_mut()
                                  .expect("Expected binding to have an aliased type");
                    *typ = self.refresh_symbols_in_type(typ.clone());
                }
                {
                    let subs = Substitution::new();
                    let mut check = super::kindcheck::KindCheck::new(&self.environment,
                                                                     &self.symbols,
                                                                     subs);
                    // Setup kind variables for all type variables and insert the types in the
                    // this type expression into the kindcheck environment
                    for bind in bindings.iter_mut() {
                        // Create the kind for this binding
                        // Test a b: 2 -> 1 -> *
                        // and bind the same variables to the arguments of the type binding
                        // ('a' and 'b' in the example)
                        let mut id_kind = check.star();
                        for gen in bind.alias.args.iter_mut().rev() {
                            gen.kind = check.subs.new_var();
                            id_kind = Kind::function(gen.kind.clone(), id_kind);
                        }
                        check.add_local(bind.alias.name.clone(), id_kind);
                    }

                    // Kindcheck all the types in the environment
                    for bind in bindings.iter_mut() {
                        check.set_variables(&bind.alias.args);
                        let typ = bind.alias
                                      .typ
                                      .as_mut()
                                      .expect("Expected binding to have an aliased type");
                        try!(check.kindcheck_type(typ));
                    }

                    // All kinds are now inferred so replace the kinds store in the AST
                    for bind in bindings.iter_mut() {
                        if let Some(ref mut typ) = bind.alias.typ {
                            *typ = check.finalize_type(typ.clone());
                        }
                        for arg in &mut bind.alias.args {
                            *arg = check.finalize_generic(&arg);
                        }
                    }
                }

                // Finally insert the declared types into the global scope
                for bind in bindings {
                    let args = &bind.alias.args;
                    let generic_args = args.iter().cloned().map(Type::generic).collect();
                    let name = Type::<_, TcType>::data(Type::id(bind.alias
                                                                    .name
                                                                    .clone()),
                                                       generic_args);
                    debug!("HELP {} \n{:?}", self.symbols.string(&bind.name), args);
                    if self.environment.stack_types.get(&bind.name).is_some() {
                        self.errors.error(ast::Spanned {
                            span: expr.span(&ast::TcIdentEnvWrapper(&self.symbols)),
                            value: DuplicateTypeDefinition(bind.name.clone()),
                        });
                    } else {
                        self.stack_type(bind.name.clone(),
                                        name.clone(),
                                        args.clone(),
                                        bind.alias.typ.clone());
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
                                                Some(ref mut expr) => self.typecheck(expr),
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
                let (id_type, record_type) = match self.find_record(&fields.iter()
                                                                           .map(|f| {
                                                                               f.name.clone()
                                                                           })
                                                                           .collect::<Vec<_>>())
                                                       .map(|t| (t.0.clone(), t.1.clone())) {
                    Ok(x) => x,
                    Err(_) => {
                        id.typ = Type::record(types.clone(), fields);
                        return Ok(TailCall::Type(id.typ.clone()));
                    }
                };
                let id_type = self.inst.instantiate(&id_type);
                let record_type = self.inst.instantiate_(&record_type);
                try!(self.unify(&Type::record(types, fields), record_type));
                id.typ = id_type.clone();
                Ok(TailCall::Type(id_type.clone()))
            }
            ast::Expr::Block(ref mut exprs) => {
                let (last, exprs) = exprs.split_last_mut().expect("Expr in block");
                for expr in exprs {
                    try!(self.typecheck(expr));
                }
                self.typecheck(last).map(TailCall::Type)
            }
        }
    }

    fn typecheck_lambda(&mut self,
                        function_type: TcType,
                        arguments: &mut [TcIdent],
                        body: &mut ast::LExpr<TcIdent>)
                        -> TcResult<TcType> {
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
        let body_type = try!(self.typecheck(body));
        self.exit_scope();
        Ok(Type::function(arg_types, body_type))
    }

    fn typecheck_pattern(&mut self,
                         pattern: &mut ast::LPattern<TcIdent>,
                         match_type: TcType)
                         -> TcResult<TcType> {
        match pattern.value {
            ast::Pattern::Constructor(ref mut id, ref mut args) => {
                if let Some(new) = self.original_symbols.get(&id.name) {
                    id.name = new.clone();
                }
                // Find the enum constructor and return the types for its arguments
                let ctor_type = try!(self.find(&id.name));
                let return_type = try!(self.typecheck_pattern_rec(args, ctor_type));
                self.unify(&match_type, return_type)
            }
            ast::Pattern::Record { ref mut id, types: ref mut associated_types, ref fields } => {
                id.typ = match_type.clone();
                let mut match_type = self.remove_alias(match_type);
                let mut types = Vec::new();
                let new_type = match *match_type {
                    Type::Record { fields: ref expected_fields, .. } => {
                        for pattern_field in fields {
                            let expected_field = try!(expected_fields.iter()
                                                    .find(|expected_field| {
                                                        pattern_field.0
                                                                     .name_eq(&expected_field.name)
                                                    })
                                                    .ok_or_else(|| {
                                                        UndefinedField(match_type.clone(),
                                                                       pattern_field.0.clone())
                                                    }));
                            let var = self.inst.subs.new_var();
                            types.push(var.clone());
                            try!(self.unify(&var, expected_field.typ.clone()));
                        }
                        None
                    }
                    _ => {
                        let fields: Vec<_> = fields.iter().map(|t| t.0.clone()).collect();
                        // actual_type is the record (not hidden behind an alias)
                        let (mut typ, mut actual_type) = match self.find_record(&fields)
                                                                   .map(|t| {
                                                                       (t.0.clone(), t.1.clone())
                                                                   }) {
                            Ok(typ) => typ,
                            Err(_) => {
                                let fields = fields.iter()
                                                   .map(|field| {
                                                       types::Field {
                                                           name: field.clone(),
                                                           typ: self.inst.subs.new_var(),
                                                       }
                                                   })
                                                   .collect();
                                let t = Type::record(Vec::new(), fields);
                                (t.clone(), t)
                            }
                        };
                        typ = self.inst.instantiate_(&typ);
                        actual_type = self.inst.instantiate_(&actual_type);
                        try!(self.unify(&match_type, typ));
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
                                    let args = field_type.typ
                                                         .args
                                                         .iter()
                                                         .cloned()
                                                         .map(Type::generic)
                                                         .collect();
                                    let alias_type = Type::data(Type::id(field_type.typ
                                                                                   .name
                                                                                   .clone()),
                                                                args);
                                    // This forces refresh_type to remap the name a type was given
                                    // in this module to its actual name
                                    self.original_symbols
                                        .insert(name.clone(), field_type.typ.name.clone());
                                    self.stack_type(name,
                                                    alias_type,
                                                    field_type.typ.args.clone(),
                                                    field_type.typ.typ.clone());
                                }
                                None => return Err(UndefinedField(match_type.clone(), name)),
                            }
                        }
                    }
                    _ => panic!("Expected a record"),
                }
                Ok(match_type)
            }
            ast::Pattern::Identifier(ref mut id) => {
                self.stack_var(id.id().clone(), match_type.clone());
                id.typ = match_type.clone();
                Ok(match_type)
            }
        }
    }

    fn typecheck_pattern_rec(&mut self, args: &[TcIdent], typ: TcType) -> TcResult<TcType> {
        if args.len() == 0 {
            return Ok(typ);
        }
        match *typ {
            Type::Function(ref argument_types, ref return_type) => {
                assert!(argument_types.len() == 1);
                self.stack_var(args[0].id().clone(), argument_types.last().unwrap().clone());
                self.typecheck_pattern_rec(&args[1..], return_type.clone())
            }
            _ => Err(PatternError(typ.clone(), args.len())),
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
        if let Some(existing_types) = self.environment.stack.get_all(&symbol) {
            if existing_types.len() >= 2 {
                let existing_type = &existing_types[existing_types.len() - 2];
                let mut alias = AliasInstantiator::new(&self.inst, &self.environment);
                debug!("Intersect\n{} <> {}",
                       types::display_type(&self.symbols, existing_type),
                       types::display_type(&self.symbols, symbol_type));
                typ = Some(unify::intersection(&self.inst.subs,
                                               &mut alias,
                                               existing_type,
                                               symbol_type));
            }
        }
        if let Some(typ) = typ {
            *self.environment.stack.get_mut(&symbol).unwrap() = self.finish_type(level, typ);
        }
    }

    fn finish_type(&mut self, level: u32, typ: TcType) -> TcType {
        let generic = {
            let vars = self.inst.named_variables.borrow();
            let max_var = vars.keys()
                              .fold("a", |max, current| {
                                  ::std::cmp::max(max, self.symbols.string(&current))
                              });
            String::from(max_var)
        };
        let mut i = 0;
        types::walk_move_type(typ,
                              &mut |typ| {
                                  let replacement = self.inst.replace_variable(typ);
                                  let mut typ = typ;
                                  if let Some(ref t) = replacement {
                                      debug!("{} ==> {}",
                                             types::display_type(&self.symbols, &typ),
                                             types::display_type(&self.symbols, t));
                                      typ = &**t;
                                  }
                                  match *typ {
                                      Type::Variable(ref var) if self.inst.subs.get_level(var.id) >
                                                                 level => {
                                          let generic = format!("{}{}", generic, i);
                                          i += 1;
                                          let id = self.symbols.symbol(generic);
                                          let gen: TcType = Type::generic(Generic {
                                              kind: var.kind.clone(),
                                              id: id.clone(),
                                          });
                                          self.inst.subs.insert(var.id, gen.clone());
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
        let mut f = |typ: &Type<_, TcType>| {
            match *typ {
                Type::Id(ref id) => {
                    self.original_symbols
                        .get(&id)
                        .or_else(|| self.environment.find_type_info(id).map(|alias| &alias.name))
                        .cloned()
                        .map(Type::id)
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
                self.inst.subs.new_var()
            }
        }
    }

    fn unify(&self, expected: &TcType, mut actual: TcType) -> TcResult<TcType> {
        debug!("Unify {} <=> {}",
               types::display_type(&self.symbols, expected),
               types::display_type(&self.symbols, &actual));
        let mut alias = AliasInstantiator::new(&self.inst, &self.environment);
        match unify::unify(&self.inst.subs, &mut alias, expected, &actual) {
            Ok(typ) => Ok(self.inst.set_type(typ)),
            Err(errors) => {
                let mut expected = expected.clone();
                expected = self.inst.set_type(expected);
                actual = self.inst.set_type(actual);
                debug!("Error '{:?}' between:\n>> {}\n>> {}",
                       errors,
                       types::display_type(&self.symbols, &expected),
                       types::display_type(&self.symbols, &actual));
                Err(TypeError::Unification(expected, actual, apply_subs(&self.inst, errors.errors)))
            }
        }
    }

    fn remove_alias(&self, typ: TcType) -> TcType {
        AliasInstantiator::new(&self.inst, &self.environment).remove_alias(typ)
    }

    fn remove_aliases(&self, typ: TcType) -> TcType {
        AliasInstantiator::new(&self.inst, &self.environment).remove_aliases(typ)
    }

    fn type_of_alias(&self,
                     id: &Symbol,
                     arguments: &[TcType])
                     -> Result<Option<TcType>, ::unify_type::Error<Symbol>> {
        AliasInstantiator::new(&self.inst, &self.environment).type_of_alias(id, arguments)
    }
}

fn with_pattern_types<F>(fields: &[(Symbol, Option<Symbol>)], typ: &TcType, mut f: F)
    where F: FnMut(&Symbol, &TcType)
{
    if let Type::Record { fields: ref field_types, .. } = **typ {
        for field in fields {
            let associated_type = field_types.iter()
                                             .find(|type_field| type_field.name.name_eq(&field.0))
                                             .expect("Associated type to exist in record");
            f(&field.0, &associated_type.typ);
        }
    }
}

fn apply_subs(inst: &Instantiator,
              error: Vec<::unify_type::Error<Symbol>>)
              -> Vec<::unify_type::Error<Symbol>> {
    use unify::Error::*;
    error.into_iter()
         .map(|error| {
             match error {
                 TypeMismatch(expected, actual) => {
                     TypeMismatch(inst.set_type(expected), inst.set_type(actual))
                 }
                 Occurs(var, typ) => Occurs(var, inst.set_type(typ)),
                 Other(::unify_type::TypeError::UndefinedType(id)) => {
                     Other(::unify_type::TypeError::UndefinedType(id))
                 }
                 Other(::unify_type::TypeError::FieldMismatch(expected, actual)) => {
                     UnifyError::Other(::unify_type::TypeError::FieldMismatch(expected, actual))
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

struct FunctionArgIter<'a, 'b: 'a> {
    tc: &'a mut Typecheck<'b>,
    typ: TcType,
}

impl<'a, 'b> Iterator for FunctionArgIter<'a, 'b> {
    type Item = TcType;
    fn next(&mut self) -> Option<TcType> {
        loop {
            let (arg, new) = match *self.typ {
                Type::Function(ref args, ref ret) => (Some(args[0].clone()), ret.clone()),
                Type::Data(ref id, ref args) => {
                    match **id {
                        Type::Id(ref id) => {
                            match self.tc.type_of_alias(id, args) {
                                Ok(Some(typ)) => (None, typ.clone()),
                                Ok(None) => return None,
                                Err(_) => return Some(self.tc.inst.subs.new_var()),
                            }
                        }
                        _ => return Some(self.tc.inst.subs.new_var()),
                    }
                }
                _ => return Some(self.tc.inst.subs.new_var()),
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
