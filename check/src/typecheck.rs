use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::rc::Rc;

use scoped_map::ScopedMap;
use base::ast;
use base::ast::{ASTType, MutVisitor};
use base::interner::{Interner, InternedStr};
use base::gc::Gc;
use kindcheck;
use substitution::{Substitution, Substitutable, Variable};
use error::Errors;
use ::Typed;

use self::TypeError::*;

pub use base::ast::{TypeVariable, Type, Kind};

pub type TcIdent = ::ast::TcIdent<InternedStr>;

pub type TcType = ast::ASTType<InternedStr>;

#[derive(Debug, PartialEq)]
enum TypeError {
    UndefinedVariable(InternedStr),
    NotAFunction(TcType),
    UndefinedType(InternedStr),
    UndefinedField(TcType, InternedStr),
    IndexError(TcType),
    PatternError(TcType, usize),
    Unification(TcType, TcType, UnificationError),
    KindError(kindcheck::Error),
    StringError(&'static str)
}

#[derive(Debug, PartialEq)]
enum UnificationError {
    TypeMismatch(TcType, TcType),
    Occurs(TypeVariable, TcType),
    UndefinedType(InternedStr)
}

fn apply_subs(tc: &Typecheck, error: UnificationError) -> UnificationError {
    match error {
        UnificationError::TypeMismatch(expected, actual) => {
            UnificationError::TypeMismatch(tc.set_type(expected), tc.set_type(actual))
        }
        UnificationError::Occurs(var, typ) => {
            UnificationError::Occurs(var, tc.set_type(typ))
        }
        UnificationError::UndefinedType(id) => UnificationError::UndefinedType(id)
    }
}

impl From<kindcheck::Error> for TypeError {
    fn from(e: kindcheck::Error) -> TypeError {
        KindError(e)
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TypeError::*;
        use self::UnificationError::{TypeMismatch, Occurs};
        match *self {
            UndefinedVariable(name) => write!(f, "Undefined variable `{}`", name),
            NotAFunction(ref typ) => write!(f, "`{}` is not a function", typ),
            UndefinedType(name) => write!(f, "Type `{}` is not defined", name),
            UndefinedField(ref typ, ref field) => write!(f, "Type `{}` does not have the field `{}`", typ, field),
            Unification(ref expected, ref actual, TypeMismatch(ref l, ref r)) =>
                write!(f, "Expected: {}\nFound: {} does not unify\n(Expected: {}\nFound: {})", expected, actual, l, r),
            Unification(ref expected, ref actual, Occurs(ref var, ref typ)) =>
                write!(f, "Variable `{}` occurs in `{}`\n(Expected: {}\nFound: {})", var, typ, expected, actual),
            Unification(ref expected, ref actual, UnificationError::UndefinedType(id)) =>
                write!(f, "Type `{}` does not exist. \n(Expected: {}\nFound: {})", id, expected, actual),
            IndexError(ref typ) => write!(f, "Type {} cannot be indexed", typ),
            PatternError(ref typ, expected_len) => write!(f, "Type {} has {} to few arguments", typ, expected_len),
            KindError(ref err) => write!(f, "{}", err),
            StringError(name) => write!(f, "{}", name),
        }
    }
}

pub type TcResult = Result<TcType, TypeError>;
pub type UnificationResult = Result<(), UnificationError>;

impl Variable for ast::TypeVariable {
    fn get_id(&self) -> u32 {
        self.id
    }
}

impl Substitutable for TcType {
    type Variable = ast::TypeVariable;

    fn new(id: u32) -> TcType {
        Type::variable(ast::TypeVariable::new(id))
    }

    fn from_variable(var: ast::TypeVariable) -> TcType {
        Type::variable(var)
    }

    fn get_var(&self) -> Option<&ast::TypeVariable> {
        match **self {
            Type::Variable(ref var) => Some(var),
            _ => None
        }
    }

    fn occurs(&self, subs: &Substitution<TcType>, var: &ast::TypeVariable) -> bool {
        let mut occurs = false;
        walk_real_type(subs, self, &mut |typ| {
            if occurs { return }
            if let Type::Variable(ref other) = *typ {
                if var == other {
                    occurs = true;
                    return
                }
                subs.update_level(var.id, other.id);
            }
        });
        occurs
    }
}

#[derive(Debug)]
pub struct TypeInfos {
    pub id_to_type: HashMap<InternedStr, (Vec<ast::Generic<InternedStr>>, TcType)>,
    pub type_to_id: HashMap<TcType, TcType>
}
impl TypeEnv for TypeInfos {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType> {
        self.id_to_type.iter()
            .filter_map(|(_, &(_, ref typ))| {
                match **typ {
                    Type::Variants(ref variants) => variants.iter().find(|v| v.0 == *id),
                    _ => None
                }
            })
            .next()
            .map(|x| &x.1)
    }

    fn find_type_info(&self, id: &InternedStr) -> Option<(&[ast::Generic<InternedStr>], Option<&TcType>)> {
        self.id_to_type.get(id)
            .map(|&(ref args, ref typ)| (&args[..], Some(typ)))
    }
    fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)> {
        self.id_to_type.iter()
            .find(|&(_, &(_, ref typ))| {
                match **typ {
                    Type::Record(ref record_fields) => {
                        fields.iter().all(|&name| record_fields.iter().any(|f| f.name == name))
                    }
                    _ => false
                }
            })
            .and_then(|t| self.type_to_id.get(&(t.1).1).map(|id_type| (id_type, &(t.1).1)))
    }
}

impl TypeInfos {
    pub fn new() -> TypeInfos {
        TypeInfos {
            id_to_type: HashMap::new(),
            type_to_id: HashMap::new()
        }
    }

    pub fn extend(&mut self, other: TypeInfos) {
        let TypeInfos { id_to_type, type_to_id } = other;
        self.id_to_type.extend(id_to_type);
        self.type_to_id.extend(type_to_id);
    }
}

pub trait TypeEnv {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType>;
    fn find_type_info(&self, id: &InternedStr) -> Option<(&[ast::Generic<InternedStr>], Option<&TcType>)>;
    fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)>;
}

impl <'a, T: ?Sized + TypeEnv> TypeEnv for &'a T {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType> {
        (**self).find_type(id)
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<(&[ast::Generic<InternedStr>], Option<&TcType>)> {
        (**self).find_type_info(id)
    }
    fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)> {
        (**self).find_record(fields)
    }
}

impl <T: TypeEnv, U: TypeEnv> TypeEnv for (T, U) {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType> {
        let &(ref outer, ref inner) = self;
        inner.find_type(id)
            .or_else(|| outer.find_type(id))
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<(&[ast::Generic<InternedStr>], Option<&TcType>)> {
        let &(ref outer, ref inner) = self;
        inner.find_type_info(id)
            .or_else(|| outer.find_type_info(id))
    }
    fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)> {
        let &(ref outer, ref inner) = self;
        inner.find_record(fields)
            .or_else(|| outer.find_record(fields))
    }
}

pub struct Typecheck<'a> {
    environment: Option<&'a (TypeEnv + 'a)>,
    interner: &'a mut Interner,
    gc: &'a mut Gc,
    pub type_infos: TypeInfos,
    stack: ScopedMap<InternedStr, TcType>,
    subs: Substitution<TcType>,
    errors: Errors<ast::Located<TypeError>>
}

pub type StringErrors = Errors<ast::Located<TypeError>>;

impl <'a> TypeEnv for Typecheck<'a> {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType> {
        let stack = &self.stack;
        let environment = &self.environment;
        let type_infos = &self.type_infos;
        match stack.find(id) {
            Some(x) => Some(x),
            None => type_infos.find_type(id)
                .or_else(|| environment.and_then(|e| e.find_type(id)))
        }
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<(&[ast::Generic<InternedStr>], Option<&TcType>)> {
        self.type_infos.find_type_info(id)
            .or_else(|| self.environment.and_then(|e| e.find_type_info(id)))
    }
    fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)> {
        self.type_infos.find_record(fields)
            .or_else(|| self.environment.and_then(|e| e.find_record(fields)))
    }
}

impl <'a> Typecheck<'a> {
    
    pub fn new(interner: &'a mut Interner, gc: &'a mut Gc) -> Typecheck<'a> {
        Typecheck {
            environment: None,
            interner: interner,
            gc: gc,
            type_infos: TypeInfos::new(),
            stack: ScopedMap::new(),
            subs: Substitution::new(),
            errors: Errors::new()
        }
    }

    fn find(&mut self, id: &InternedStr) -> TcResult {
        let t: Option<&TcType> = {
            let stack = &self.stack;
            let environment = &self.environment;
            let type_infos = &self.type_infos;
            match stack.find(id) {
                Some(x) => Some(x),
                None => type_infos.find_type(id)
                    .or_else(|| environment.and_then(|e| e.find_type(id)))
            }
        };
        match t {
            Some(typ) => {
                let x = self.subs.instantiate(typ);
                debug!("Find {} : {}", id, x);
                Ok(x)
            }
            None => Err(UndefinedVariable(id.clone()))
        }
    }

    fn find_record(&self, fields: &[InternedStr]) -> Result<(&TcType, &TcType), TypeError> {
        TypeEnv::find_record(self, fields)
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(StringError("Expected fields")))
    }

    fn find_type_info(&self, id: &InternedStr) -> Result<(&[ast::Generic<InternedStr>], Option<&TcType>), TypeError> {
        TypeEnv::find_type_info(self, id)
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(UndefinedType(id.clone())))
    }
    
    fn stack_var(&mut self, id: InternedStr, typ: TcType) {
        self.stack.insert(id, typ);
    }

    pub fn add_environment(&mut self, env: &'a TypeEnv) {
        self.environment = Some(env);
    }

    fn generalize_variables(&mut self, level: u32, expr: &mut ast::LExpr<TcIdent>) {
        //Replace all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b:'a> { level: u32, tc: &'a mut Typecheck<'b> }
        impl <'a, 'b> MutVisitor for ReplaceVisitor<'a, 'b> {
            type T = TcIdent;
            fn visit_identifier(&mut self, id: &mut TcIdent) {
                id.typ = self.tc.finish_type(self.level, id.typ.clone());
            }
        }
        let mut stack = mem::replace(&mut self.stack, ScopedMap::new());
        for (_, vec) in stack.iter_mut() {
            for typ in vec {
                *typ = self.finish_type(level, typ.clone());
            }
        }
        mem::swap(&mut self.stack, &mut stack);
        ReplaceVisitor { level: level, tc: self }.visit_expr(expr);
    }

    pub fn typecheck_expr(&mut self, expr: &mut ast::LExpr<TcIdent>) -> Result<TcType, StringErrors> {
        self.subs.clear();
        self.stack.clear();

        let mut typ = match self.typecheck(expr) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.error(ast::Located { location: expr.location, value: err });
                return Err(mem::replace(&mut self.errors, Errors::new()));
            }
        };
        if self.errors.has_errors() {
            Err(mem::replace(&mut self.errors, Errors::new()))
        }
        else {
            typ = self.finish_type(0, typ);
            typ = ast::walk_move_type(typ, &mut unroll_app);
            self.generalize_variables(0, expr);
            Ok(typ)
        }
    }
    
    fn typecheck(&mut self, expr: &mut ast::LExpr<TcIdent>) -> TcResult {
        match self.typecheck_(expr) {
            Ok(typ) => Ok(typ),
            Err(err) => {
                self.errors.error(ast::Located { location: expr.location, value: err });
                Ok(self.subs.new_var())
            }
        }
    }
    fn typecheck_(&mut self, expr: &mut ast::LExpr<TcIdent>) -> TcResult {
        match expr.value {
            ast::Expr::Identifier(ref mut id) => {
                id.typ = try!(self.find(id.id()));
                Ok(id.typ.clone())
            }
            ast::Expr::Literal(ref lit) => {
                Ok(match *lit {
                    ast::Integer(_) => Type::int(),
                    ast::Float(_) => Type::float(),
                    ast::String(_) => Type::string(),
                    ast::Bool(_) => Type::bool()
                })
            }
            ast::Expr::Call(ref mut func, ref mut args) => {
                let mut func_type = try!(self.typecheck(&mut**func));
                for arg in args.iter_mut() {
                    let f = Type::function(vec![self.subs.new_var()], self.subs.new_var());
                    func_type = try!(self.unify(&f, func_type));
                    func_type = match *func_type {
                        Type::Function(ref arg_type, ref ret) => {
                            assert!(arg_type.len() == 1);
                            let actual = try!(self.typecheck(arg));
                            try!(self.unify(&arg_type[0], actual));
                            ret.clone()
                        }
                        _ => return Err(NotAFunction(func_type.clone()))
                    };
                }
                Ok(func_type)
            }
            ast::Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut**pred));
                try!(self.unify(&Type::bool(), pred_type));
                let true_type = try!(self.typecheck(&mut**if_true));
                let false_type = match *if_false {
                    Some(ref mut if_false) => try!(self.typecheck(&mut**if_false)),
                    None => Type::unit()
                };
                self.unify(&true_type, false_type)
            }
            ast::Expr::BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut**lhs));
                let rhs_type = try!(self.typecheck(&mut**rhs));
                if op.name.starts_with("#") {
                    let arg_type = try!(self.unify(&lhs_type, rhs_type));
                    let offset;
                    let typ = if op.name[1..].starts_with("Int") {
                        offset = "Int".len();
                        op.typ = Type::function(vec![Type::int(), Type::int()], Type::int());
                        try!(self.unify(&Type::int(), arg_type))
                    }
                    else if op.name[1..].starts_with("Float") {
                        offset = "Float".len();
                        op.typ = Type::function(vec![Type::float(), Type::float()], Type::float());
                        try!(self.unify(&Type::float(), arg_type))
                    }
                    else {
                        panic!("ICE: Unknown primitive type")
                    };
                    match &op.name[1+offset..] {
                        "+" | "-" | "*" => Ok(typ),
                        "==" | "<" => Ok(Type::bool().clone()),
                        _ => Err(UndefinedVariable(op.name.clone()))
                    }
                }
                else {
                    match &op.name[..] {
                        "&&" | "||" => {
                            try!(self.unify(&lhs_type, rhs_type.clone()));
                            self.unify(&Type::bool(), lhs_type)
                        }
                        _ => {
                            op.typ = try!(self.find(op.id()));
                            let func_type = Type::function(vec![lhs_type, rhs_type], self.subs.new_var());
                            match *try!(self.unify(&op.typ, func_type)) {
                                Type::Function(_, ref return_type) => 
                                    match **return_type {
                                        Type::Function(_, ref return_type) => Ok(return_type.clone()),
                                        _ => panic!("ICE: unify binop")
                                    },
                                _ => panic!("ICE: unify binop")
                            }
                        }
                    }
                }
            }
            ast::Expr::Tuple(ref mut exprs) => {
                assert!(exprs.len() == 0);
                Ok(Type::unit())
            }
            ast::Expr::Match(ref mut expr, ref mut alts) => {
                let typ = try!(self.typecheck(&mut**expr));
                let mut expected_alt_type = None;

                for alt in alts.iter_mut() {
                    self.stack.enter_scope();
                    try!(self.typecheck_pattern(&mut alt.pattern, typ.clone()));
                    let mut alt_type = try!(self.typecheck(&mut alt.expression));
                    self.stack.exit_scope();
                    if let Some(ref expected) = expected_alt_type {
                        alt_type = try!(self.unify(expected, alt_type));
                    }
                    expected_alt_type = Some(alt_type);
                }
                expected_alt_type
                    .ok_or(StringError("No alternative in case expression"))
            }
            ast::Expr::Let(ref mut bindings, ref mut body) => {
                self.stack.enter_scope();
                let level = self.subs.var_id();
                let is_recursive = bindings.iter().all(|bind| bind.arguments.len() > 0);
                if is_recursive {
                    for bind in bindings.iter_mut() {
                        let mut typ = self.subs.new_var();
                        if let Some(ref mut type_decl) = bind.typ {
                            try!(self.kindcheck(type_decl, &mut []));
                            let decl = self.subs.instantiate(type_decl);
                            typ = try!(self.unify(&decl, typ));
                        }
                        try!(self.typecheck_pattern(&mut bind.name, typ));
                        if let ast::Expr::Lambda(ref mut lambda) = bind.expression.value {
                            if let ast::Pattern::Identifier(ref name) = bind.name {
                                lambda.id.name = name.name;
                            }
                        }
                    }
                }
                let mut types = Vec::new();
                for bind in bindings.iter_mut() {
                    //Functions which are declared as `let f x = ...` are allowed to be self recursive
                    let mut typ = if bind.arguments.len() != 0 {
                        let function_type = match bind.typ {
                            Some(ref typ) => typ.clone(),
                            None => self.subs.new_var()
                        };
                        try!(self.typecheck_lambda(function_type,
                                                   &mut bind.arguments,
                                                   &mut bind.expression))
                    }
                    else {
                        if let Some(ref mut type_decl) = bind.typ {
                            try!(self.kindcheck(type_decl, &mut []));
                        }
                        try!(self.typecheck(&mut bind.expression))
                    };
                    debug!("let {:?} : {}", bind.name, typ);
                    if let Some(ref type_decl) = bind.typ {
                        typ = try!(self.unify(type_decl, typ));
                    }
                    if !is_recursive {
                        //Merge the type declaration and the actual type
                        self.generalize_variables(level, &mut bind.expression);
                        try!(self.typecheck_pattern(&mut bind.name, typ));
                    }
                    else {
                        types.push(typ);
                    }
                }
                if is_recursive {
                    for (typ, bind) in types.into_iter().zip(bindings.iter_mut()) {
                        //Merge the variable we bound to the name and the type inferred
                        //in the expression
                        try!(self.unify(&bind.type_of().clone(), typ));
                    }
                }
                //Once all variables inside the let has been unified we can quantify them
                debug!("Generalize {}", level);
                for bind in bindings {
                    self.generalize_variables(level, &mut bind.expression);
                    match bind.name {
                        ast::Pattern::Identifier(ref mut _id) => {
                            _id.typ = self.finish_type(level, _id.typ.clone());
                            debug!("{}: {}", _id.name, _id.typ);
                        }
                        ast::Pattern::Record(_) => debug!("{{ .. }}: {}", bind.expression.type_of()),
                        ast::Pattern::Constructor(ref _id, _) => debug!("{}: {}", _id.name, bind.expression.type_of())
                    }
                }
                debug!("Typecheck `in`");
                let result = self.typecheck(body);
                self.stack.exit_scope();
                result
            }
            ast::Expr::FieldAccess(ref mut expr, ref mut field_access) => {
                let mut typ = try!(self.typecheck(&mut **expr));
                debug!("FieldAccess {} . {}", typ, field_access.name);
                self.subs.make_real(&mut typ);
                if let Type::Variable(_) = *typ {
                    let (record_type, _) = try!(self.find_record(&[field_access.name])
                                              .map(|t| (t.0.clone(), t.1.clone())));
                    let record_type = self.subs.instantiate(&record_type);
                    typ = try!(self.unify(&record_type, typ));
                }
                let record = match *typ {
                    Type::Data(ast::TypeConstructor::Data(id), ref arguments) => {
                        self.find_type_info(&id)
                            .ok()
                            .and_then(|t| t.1.map(|typ| (t.0, typ.clone())))
                            .map(|(generic_args, typ)| {
                                self.subs.instantiate_with(typ, arguments, generic_args)
                            })
                            .unwrap_or_else(|| typ.clone())
                    }
                    Type::App(ref f, _) => {
                        match **f {
                            Type::Data(ast::TypeConstructor::Data(id), ref arguments) => {
                                self.find_type_info(&id)
                                    .ok()
                                    .and_then(|t| t.1.map(|typ| (t.0, typ.clone())))
                                    .map(|(generic_args, typ)| {
                                        self.subs.instantiate_with(typ, arguments, generic_args)
                                    })
                                    .unwrap_or_else(|| typ.clone())
                            }
                            _ => typ.clone()
                        }
                    }
                    _ => typ.clone()
                };
                match *record {
                    Type::Record(ref fields) => {
                        let field_type = fields.iter()
                            .find(|field| field.name == *field_access.id())
                            .map(|field| field.typ.clone());
                        field_access.typ = match field_type {
                            Some(typ) => self.subs.instantiate(&typ),
                            None => return Err(UndefinedField(typ.clone(), field_access.name.clone()))
                        };
                        Ok(field_access.typ.clone())
                    }
                    Type::Data(ast::TypeConstructor::Data(_), _) => Err(StringError("Field access on data")),
                    Type::Data(ast::TypeConstructor::Builtin(..), _) | Type::Builtin(..) => {
                        Err(StringError("Field access on builtin type"))
                    }
                    Type::Function(..) => Err(StringError("Field access on function")),
                    Type::Generic(..) => Err(StringError("Field acces on generic")),
                    Type::Variable(..) => Err(StringError("Field access on variable")),
                    Type::Array(..) => Err(StringError("Field access on array")),
                    Type::App(..) => Err(StringError("Field access on type application")),
                    Type::Variants(..) => Err(StringError("Field access on variant")),
                }
            }
            ast::Expr::Array(ref mut a) => {
                let mut expected_type = self.subs.new_var();
                for expr in a.expressions.iter_mut() {
                    let typ = try!(self.typecheck(expr));
                    expected_type = try!(self.unify(&expected_type, typ));
                }
                a.id.typ = Type::array(expected_type);
                Ok(a.id.typ.clone())
            }
            ast::Expr::ArrayAccess(ref mut array, ref mut index) => {
                let array_type = try!(self.typecheck(&mut **array));
                let var = self.subs.new_var();
                let array_type = try!(self.unify(&Type::array(var), array_type));
                let typ = match *array_type {
                    Type::Array(ref typ) => typ.clone(),
                    _ => return Err(IndexError(array_type.clone()))
                };
                let index_type = try!(self.typecheck(&mut **index));
                try!(self.unify(&Type::int(), index_type));
                Ok(typ)
            }
            ast::Expr::Lambda(ref mut lambda) => {
                let loc = format!("lambda:{}", expr.location);
                lambda.id.name = self.interner.intern(self.gc, &loc);
                let function_type = self.subs.new_var();
                let typ = try!(self.typecheck_lambda(function_type, &mut lambda.arguments, &mut lambda.body));
                lambda.id.typ = typ.clone();
                Ok(typ)
            }
            ast::Expr::Type(ref mut bindings, ref mut expr) => {
                for &mut ast::TypeBinding { ref mut name, ref mut typ } in bindings {
                    let (generic_args, id) = match (**name).clone() {
                        Type::Data(ast::TypeConstructor::Data(id), mut args) => {
                            let subs = Substitution::new();
                            let mut generic_args = Vec::with_capacity(args.len());
                            for arg in args.iter_mut() {
                                let mut a = (**arg).clone();
                                if let Type::Generic(ref mut gen) = a {
                                    gen.kind = Rc::new(subs.new_var());
                                    generic_args.push(gen.clone());
                                }
                                *arg = TcType::from(a);
                            }
                            let name_copy = Type::data(ast::TypeConstructor::Data(id), args.clone());
                            self.type_infos.type_to_id.insert(typ.clone(), name_copy.clone());
                            self.type_infos.id_to_type.insert(id, (generic_args.clone(), typ.clone().clone()));

                            {
                                let f = |id| {
                                    self.type_infos.id_to_type.get(&id).map(|t| &t.1)
                                        .and_then(|typ| self.type_infos.type_to_id.get(typ))
                                };
                                let mut check = super::kindcheck::KindCheck::new(&f, &mut args, subs);
                                try!(check.kindcheck_type(typ));
                                try!(check.kindcheck_type(name));
                            }

                            for (g, a) in generic_args.iter_mut().zip(&args) {
                                if let Type::Generic(ref gen) = **a {
                                    g.kind = gen.kind.clone();
                                }
                            }
                            (generic_args, id)
                        }
                        _ => panic!("ICE: Unexpected lhs of type binding {}", name)
                    };
                    self.type_infos.type_to_id.insert(typ.clone(), name.clone());
                    self.type_infos.id_to_type.insert(id, (generic_args, typ.clone()));
                }
                let expr_type = try!(self.typecheck(&mut **expr));
                Ok(expr_type)
            }
            ast::Expr::Record(ref mut id, ref mut fields) => {
                let fields = try!(fields.iter_mut()
                    .map(|field| {
                        match field.1 {
                            Some(ref mut expr) => self.typecheck(expr),
                            None => self.find(&field.0)
                        }.map(|typ| ast::Field { name: field.0, typ: typ })
                    })
                    .collect::<Result<Vec<_>, TypeError>>());
                let (id_type, record_type) = match self.find_record(&fields.iter().map(|f| f.name).collect::<Vec<_>>())
                                                  .map(|t| (t.0.clone(), t.1.clone())) {
                    Ok(x) => x,
                    Err(_) => {
                        id.typ = Type::record(fields);
                        return Ok(id.typ.clone());
                    }
                };
                let id_type = self.subs.instantiate(&id_type);
                let record_type = self.subs.instantiate_(&record_type);
                try!(self.unify(&Type::record(fields), record_type));
                id.typ = id_type.clone();
                Ok(id_type.clone())
            }
        }
    }

    fn typecheck_lambda(&mut self,
                        function_type: TcType,
                        arguments: &mut [TcIdent],
                        body: &mut ast::LExpr<TcIdent>
                       ) -> Result<TcType, TypeError> {
        self.stack.enter_scope();
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
        self.stack.exit_scope();
        Ok(Type::function(arg_types, body_type))
    }

    fn typecheck_pattern(&mut self, pattern: &mut ast::Pattern<TcIdent>, match_type: TcType) -> Result<TcType, TypeError> {
        match *pattern {
            ast::Pattern::Constructor(ref id, ref mut args) => {
                //Find the enum constructor and return the types for its arguments
                let ctor_type = try!(self.find(&id.name));
                let return_type = try!(self.typecheck_pattern_rec(args, ctor_type));
                self.unify(&match_type, return_type)
            }
            ast::Pattern::Record(ref record) => {
                let mut match_type = self.remove_alias(match_type);
                let mut types = Vec::new();
                let new_type = match *match_type {
                    Type::Record(ref expected_fields) => {
                        for pattern_field in record {
                            let expected_field = try!(expected_fields.iter()
                                .find(|expected_field| pattern_field.0 == expected_field.name)
                                .ok_or(UndefinedField(match_type.clone(), pattern_field.0)));
                            let var = self.subs.new_var();
                            types.push(var.clone());
                            try!(self.unify(&var, expected_field.typ.clone()));
                        }
                        None
                    }
                    _ => {
                        let fields: Vec<_> = record.iter().map(|t| t.0).collect();
                        //actual_type is the record (not hidden behind an alias)
                        let (mut typ, mut actual_type) = match self.find_record(&fields)
                                .map(|t| (t.0.clone(), t.1.clone())) {
                            Ok(typ) => typ,
                            Err(_) => {
                                let t = Type::record(record.iter()
                                    .map(|field|
                                        ast::Field {
                                            name: field.0,
                                            typ: self.subs.new_var()
                                        }
                                    )
                                    .collect());
                                (t.clone(), t)
                            }
                        };
                        typ = self.subs.instantiate_(&typ);
                        actual_type = self.subs.instantiate_(&actual_type);
                        try!(self.unify(&match_type, typ));
                        match *actual_type {
                            Type::Record(ref record_types) => {
                                types.extend(record_types.iter().map(|f| f.typ.clone()));
                            }
                            _ => panic!("Expected record found {}", match_type)
                        }
                        Some(actual_type)
                    }
                };
                match_type = new_type.unwrap_or(match_type);
                for (field, field_type) in record.iter().zip(types) {
                    let (mut name, ref bind) = *field;
                    if let Some(bind_name) = *bind {
                        name = bind_name;
                    }
                    self.stack_var(name, field_type);
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

    fn typecheck_pattern_rec(&mut self, args: &[TcIdent], typ: TcType) -> Result<TcType, TypeError> {
        if args.len() == 0 {
            return Ok(typ)
        }
        match *typ {
            Type::Function(ref argument_types, ref return_type) => {
                assert!(argument_types.len() == 1);
                self.stack_var(args[0].id().clone(), argument_types.last().unwrap().clone());
                self.typecheck_pattern_rec(&args[1..], return_type.clone())
            }
            _ => Err(PatternError(typ.clone(), args.len()))
        }
    }

    fn kindcheck(&self, typ: &mut TcType, args: &mut [TcType]) -> Result<(), TypeError> {
        let f = |id| {
            self.type_infos.id_to_type.get(&id).map(|t| &t.1)
                .and_then(|typ| self.type_infos.type_to_id.get(typ))
        };
        let subs = Substitution::new();
        let mut check = super::kindcheck::KindCheck::new(&f, args, subs);
        try!(check.kindcheck_type(typ));
        Ok(())
    }

    fn unify(&self, expected: &TcType, mut actual: TcType) -> TcResult {
        debug!("Unify {} <=> {}", expected, actual);
        match self.unify_(expected, &actual) {
            Ok(()) => {
                //Return the `expected` type as that is what is passed in for type
                //declarations
                Ok(self.set_type(expected.clone()))
            }
            Err(err) => {
                let mut expected = expected.clone();
                expected = self.set_type(expected);
                actual = self.set_type(actual);
                debug!("Error '{:?}' between:\n>> {}\n>> {}", err, expected, actual);
                Err(Unification(expected, actual, apply_subs(self, err)))
            }
        }
    }

    fn unify_(&self, expected: &TcType, actual: &TcType) -> UnificationResult {
        let expected = self.subs.real(expected);
        let actual = self.subs.real(actual);
        debug!("{} <=> {}", expected, actual);
        match (&**expected, &**actual) {
            (&Type::Variable(ref l), &Type::Variable(ref r)) if l.id == r.id => Ok(()),
            (&Type::Variable(ref l), _) => self.union(l, actual),
            (_, &Type::Variable(ref r)) => self.union(r, expected),
            (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    for (l, r) in l_args.iter().zip(r_args.iter()) {
                        try!(self.unify_(l, r));
                    }
                    self.unify_(l_ret, r_ret)
                }
                else {
                    Err(UnificationError::TypeMismatch(expected.clone(), actual.clone()))
                }
            }
            (&Type::Function(ref l_args, ref l_ret), &Type::App(..)) => {
                self.unify_function(&l_args[0], l_ret, actual)
            }
            (&Type::App(..), &Type::Function(ref l_args, ref l_ret)) => {
                self.unify_function(&l_args[0], l_ret, expected)
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => self.unify_(l, r),
            (&Type::Data(ref l, ref l_args), &Type::Data(ref r, ref r_args))
                if l == r && l_args.len() == r_args.len() => {
                for (l, r) in l_args.iter().zip(r_args.iter()) {
                    try!(self.unify_(l, r));
                }
                Ok(())
            }
            (&Type::Record(ref l_args), &Type::Record(ref r_args))
                if l_args.len() == r_args.len() => {

                for (l, r) in l_args.iter().zip(r_args.iter()) {
                    if l.name != r.name {
                        return Err(UnificationError::TypeMismatch(l.typ.clone(), r.typ.clone()))
                    }
                    else {
                        try!(self.unify_(&l.typ, &r.typ));
                    }
                }
                Ok(())
            }
            (&Type::Data(ref l, ref l_args), &Type::App(_, _)) => {
                self.unify_app(l, l_args, actual, &|last, r_arg| self.unify_(last, r_arg))
                    .or_else(|err| {
                        //Attempt to unify using the type that is aliased if that exists
                        match *l {
                            ast::TypeConstructor::Data(l) => {
                                let l = try!(self.type_of_alias(l, l_args));
                                match l {
                                    Some(l) => self.unify_(&l, actual),
                                    None => {
                                        Err(err)
                                    }
                                }
                            }
                            _ => Err(err)
                        }
                    })
            }
            (&Type::App(_, _), &Type::Data(ref r, ref r_args)) => {
                self.unify_app(r, r_args, expected, &|last, l_arg| self.unify_(l_arg, last))
                    .or_else(|err| {
                        match *r {
                            ast::TypeConstructor::Data(r) => {
                                let r = try!(self.type_of_alias(r, r_args));
                                match r {
                                    Some(r) => self.unify_(&r, expected),
                                    None => {
                                        Err(err)
                                    }
                                }
                            }
                            _ => Err(err)
                        }
                    })
            }
            (&Type::App(ref l1, ref l2), &Type::App(ref r1, ref r2)) => {
                self.unify_(l1, r1)
                    .and_then(|()| self.unify_(l2, r2))
            }
            (&Type::Data(ast::TypeConstructor::Data(l), ref l_args), _) => {
                let l = try!(self.type_of_alias(l, l_args));
                match l {
                    Some(l) => self.unify_(&l, actual),
                    None => {
                        Err(UnificationError::TypeMismatch(expected.clone(), actual.clone()))
                    }
                }
            }
            (_, &Type::Data(ast::TypeConstructor::Data(r), ref r_args)) => {
                let r = try!(self.type_of_alias(r, r_args));
                match r {
                    Some(r) => self.unify_(expected, &r),
                    None => {
                        Err(UnificationError::TypeMismatch(expected.clone(), actual.clone()))
                    }
                }
            }
            _ => {
                if expected == actual {
                    Ok(())
                }
                else {
                    Err(UnificationError::TypeMismatch(expected.clone(), actual.clone()))
                }
            }
        }
    }

    fn unify_app<F>(&self, l: &ast::TypeConstructor<InternedStr>, l_args: &[TcType], r: &TcType, f: &F) -> UnificationResult
            where F: Fn(&TcType, &TcType) -> UnificationResult {
        let r = self.subs.real(r);
        debug!("{:?} {:?} <==> {}", l, l_args, r);
        match **r {
            Type::App(ref r, ref r_arg) => {
                match l_args.last() {
                    Some(last) => {
                        f(last, r_arg)
                            .and_then(|_| 
                                self.unify_app(l, &l_args[0..l_args.len()-1], r, f)
                            )
                    }
                    None => {
                        let l = Type::data(l.clone(), l_args.iter().cloned().collect());
                        Err(UnificationError::TypeMismatch(l, r.clone()))
                    }
                }
            }
            Type::Data(ref r, ref r_args)
            if l == r && l_args.len() == r_args.len() => {
                for (l, r) in l_args.iter().zip(r_args) {
                    try!(self.unify_(l, r));
                }
                Ok(())
            }
            Type::Variable(ref r) => {
                self.union(r, &Type::data(l.clone(), l_args.iter().cloned().collect()))
            }
            _ => {
                let l = Type::data(l.clone(), l_args.iter().cloned().collect());
                Err(UnificationError::TypeMismatch(l, r.clone()))
            }
        }
    }

    fn unify_function(&self,
                         arg: &TcType,
                         ret: &TcType,
                         other: &TcType
                        ) -> UnificationResult {
        let error = || {
            let func = Type::function(vec![arg.clone()], ret.clone());
            Err(UnificationError::TypeMismatch(func, other.clone()))
        };
        let other = self.subs.real(other);
        match **other {
            Type::App(ref other_f, ref other_ret) => {
                let other_f = self.subs.real(other_f);
                match **other_f {
                    Type::App(ref fn_prim, ref other_arg) => {
                        self.unify_(fn_prim, &Type::builtin(ast::BuiltinType::FunctionType))
                            .and_then(|()| self.unify_(arg, other_arg))
                            .and_then(|()| self.unify_(ret, other_ret))
                    }
                    _ => error()
                }
            }
            _ => error()
        }
    }

    fn set_type(&self, t: TcType) -> TcType {
        ast::walk_move_type(t, &mut |typ| {
            let replacement = self.replace_variable(typ);
            let result = {
                let mut typ = typ;
                if let Some(ref t) = replacement {
                    typ = &**t;
                }
                unroll_app(typ)
            };
            result.or(replacement)
        })
    }

    fn replace_variable(&self, typ: &Type<InternedStr>) -> Option<TcType> {
        match *typ {
            Type::Variable(ref id) => {
                self.subs.find_type_for_var(id.id)
                    .map(|t| t.clone())
            }
            _ => None
        }
    }

    fn union(&self, id: &ast::TypeVariable, typ: &TcType) -> UnificationResult {
        self.subs.union(id, typ)
            .map_err(|()| UnificationError::Occurs(id.clone(), typ.clone()))
    }

    fn finish_type(&mut self, level: u32, typ: TcType) -> TcType {
        let mut generic = {
            let vars = self.subs.named_variables.borrow();
            let max_var = vars.keys()
                .fold("a", |max, current| {
                    if current.len() == 1 {
                        ::std::cmp::max(max, &current[..])
                    }
                    else {
                        max
                    }
                });
            String::from(max_var)
        };
        ast::walk_move_type(typ, &mut |typ| {
            let replacement = self.replace_variable(typ);
            let mut typ = typ;
            if let Some(ref t) = replacement {
                debug!("{} ==> {}",  typ, t);
                typ = &**t;
            }
            match *typ {
                Type::Variable(ref var) if self.subs.get_level(var.id) > level => {
                    let c = generic.pop().unwrap();
                    generic.push((c as u8 + 1) as char);
                    let id = self.interner.intern(self.gc, &generic);
                    let gen = Type::generic(ast::Generic { kind: var.kind.clone(), id: id });
                    self.subs.insert(var.id, gen.clone());
                    self.subs.named_variables.borrow_mut().insert(id, gen.clone());
                    Some(gen)
                }
                _ => unroll_app(typ).or(replacement.clone())
            }
        })
    }

    fn remove_alias(&self, typ: TcType) -> TcType {
        let x = match *typ {
            Type::Data(ast::TypeConstructor::Data(id), ref args) => {
                self.type_of_alias(id, args)
                    .unwrap_or_else(|_| None)
            }
            _ => None
        };
        x.unwrap_or(typ)
    }

    fn type_of_alias(&self, id: InternedStr, arguments: &[TcType]) -> Result<Option<TcType>, UnificationError> {
        let (args, typ) = {
            let (args, typ) = try!(TypeEnv::find_type_info(self, &id)
                    .map(|s| Ok(s))
                    .unwrap_or_else(|| Err(UnificationError::UndefinedType(id.clone()))));
            match typ {
                Some(typ) => {
                    //TODO avoid clones here
                    let args: Vec<_> = args.iter().cloned().collect();
                    (args, typ.clone())
                }
                None => {
                    return Ok(None)
                }
            }
        };
        if arguments.len() != args.len() {
            let expected = Type::data(ast::TypeConstructor::Data(id), arguments.iter().cloned().collect());
            return Err(UnificationError::TypeMismatch(expected, typ));
        }
        let typ = self.subs.instantiate_with(typ, arguments, &args);
        Ok(Some(typ))
    }
}

impl Substitution<TcType> {

    fn variable_for2(&self, generic: &ast::Generic<InternedStr>) -> TcType {
        let mut var = (*self.variable_for(generic.id)).clone();
        if let Type::Variable(ref mut var) = var {
            var.kind = generic.kind.clone()
        }
        TcType::from(var)
    }

    ///Instantiates a type, replacing all generic variables with fresh type variables
    fn instantiate(&mut self, typ: &TcType) -> TcType {
        self.named_variables.borrow_mut().clear();
        self.instantiate_(typ)
    }

    fn instantiate_(&mut self, typ: &TcType) -> TcType {
        instantiate(typ.clone(), |id| Some(self.variable_for2(id)))
    }

    fn instantiate_with(&self,
                        typ: TcType,
                        arguments: &[TcType],
                        args: &[ast::Generic<InternedStr>]
                       ) -> TcType {
        self.named_variables.borrow_mut().clear();
        instantiate(typ, |gen| {
            //Replace the generic variable with the type from the list
            //or if it is not found the make a fresh variable
            args.iter().zip(arguments)
                .find(|&(arg, _)| arg.id == gen.id)
                .map(|(_, typ)| typ.clone())
        })
    }
}

pub fn instantiate<F>(typ: TcType, mut f: F) -> TcType
where F: FnMut(&ast::Generic<InternedStr>) -> Option<TcType> {
    debug!("Instantiate {}", typ);
    ast::walk_move_type(typ, &mut |typ| {
        match *typ {
            Type::Generic(ref x) => {
                let var = f(x);
                if let Some(ref var) = var {
                    debug!("Bind generic {} -> {}", x, var);
                }
                var
            }
            _ => None
        }
    })
}

fn unroll_app(typ: &Type<InternedStr>) -> Option<TcType> {
    let mut args = Vec::new();
    let mut current = typ;
    loop {
        match *current {
            Type::App(ref l, ref r) => {
                args.push(r.clone());
                current = &**l;
            }
            Type::Data(ref l, ref rest) => {
                args.extend(rest.iter().rev().cloned());
                args.reverse();
                return Some(Type::data(l.clone(), args))
            }
            _ => return None
        }
    }
}

struct FunctionArgIter<'a, 'b: 'a> {
    tc: &'a mut Typecheck<'b>,
    typ: TcType
}

impl <'a, 'b> Iterator for FunctionArgIter<'a, 'b> {
    type Item = TcType;
    fn next(&mut self) -> Option<TcType> {
        loop {
            let (arg, new) = match *self.typ {
                Type::Function(ref args, ref ret) => {
                    (Some(args[0].clone()), ret.clone())
                }
                Type::Data(ast::TypeConstructor::Data(id), ref args) => {
                    match self.tc.type_of_alias(id, args) {
                        Ok(Some(typ)) => (None, typ.clone()),
                        Ok(None) => return None,
                        Err(_) => return Some(self.tc.subs.new_var())
                    }
                }
                _ => return Some(self.tc.subs.new_var())
            };
            self.typ = new;
            if let Some(arg) = arg {
                return Some(arg)
            }
        }
    }
}

fn function_arg_iter<'a, 'b>(tc: &'a mut Typecheck<'b>,
                         typ: TcType
                        ) -> FunctionArgIter<'a, 'b> {
    FunctionArgIter { tc: tc, typ: typ }
}


pub fn walk_real_type<F>(subs: &Substitution<TcType>, typ: &TcType, f: &mut F)
    where F: FnMut(&Type<InternedStr>) {
    let typ = subs.real(typ);
    f(typ);
    match **typ {
        Type::Data(_, ref args) => {
            for a in args {
                walk_real_type(subs, a, f);
            }
        }
        Type::Array(ref inner) => {
            walk_real_type(subs, inner, f);
        }
        Type::Function(ref args, ref ret) => {
            for a in args {
                walk_real_type(subs, a, f);
            }
            walk_real_type(subs, ret, f);
        }
        Type::Record(ref fields) => {
            for field in fields {
                walk_real_type(subs, &field.typ, f);
            }
        }
        Type::App(ref l, ref r) => {
            walk_real_type(subs, l, f);
            walk_real_type(subs, r, f);
        }
        Type::Variants(ref variants) => {
            for variant in variants {
                walk_real_type(subs, &variant.1, f);
            }
        }
        Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => ()
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use base::ast;
    use super::super::tests::{get_local_interner, intern};
    use ::Typed;

    macro_rules! assert_pass {
        ($e: expr) => {{
            if !$e.is_ok() {
                panic!("assert_pass: {}", $e.unwrap_err());
            }
        }}
    }
    macro_rules! assert_err {
        ($e: expr, $id: pat) => {{
            use super::TypeError::*;
            #[allow(unused_imports)]
            use super::UnificationError::{TypeMismatch, Occurs};
            match $e {
                Ok(x) => assert!(false, "Expected error, got {}", x),
                Err(err) => assert!(err.errors.iter().any(|e| match *e {
                                ast::Located { value: $id, .. } => true,
                                _ => false
                            }), "Found errors:\n{}\nbut expected {}", err, stringify!($id))
            }
        }}
    }

    fn typ(s: &str) -> TcType {
        assert!(s.len() != 0);
        typ_a(s, Vec::new())
    }
    fn typ_a(s: &str, args: Vec<TcType>) -> TcType {
        assert!(s.len() != 0);
        ast::ASTType::new(ast::type_con(intern(s), args))
    }

    pub fn parse_new(s: &str) -> ast::LExpr<TcIdent> {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut(ref mut interner, ref mut gc) = &mut *interner;
        let x = ::parser::parse_tc(gc, interner, s)
            .unwrap_or_else(|err| panic!("{:?}", err));
        x
    }

    pub fn typecheck(text: &str) -> Result<TcType, StringErrors> {
        let (_, t) = typecheck_expr(text);
        t
    }

    pub fn typecheck_expr(text: &str) -> (ast::LExpr<TcIdent>, Result<TcType, StringErrors>) {
        let mut expr = parse_new(text);
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut(ref mut interner, ref mut gc) = &mut *interner;
        let mut tc = Typecheck::new(interner, gc);
        let result = tc.typecheck_expr(&mut expr);
        (expr, result)
    }

    #[test]
    fn function_type_new() {
        let text = 
r"
\x -> x
";
        let result = typecheck(text);
        assert!(result.is_ok());
        match *result.unwrap() {
            Type::Function(_, _) => {
                assert!(true);
            }
            _ => assert!(false)
        }
    }

    #[test]
    fn function_2_args() {
        let _ = ::env_logger::init();
        let text = 
r"
\x y -> 1 #Int+ x #Int+ y
";
        let result = typecheck(text);
        assert_eq!(result, Ok(Type::function(vec![typ("Int"), typ("Int")], typ("Int"))));
    }

    #[test]
    fn type_decl() {
        let _ = ::env_logger::init();
        let text = 
r"
type Test = { x: Int } in { x = 0 }
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ("Test")));
    }

    #[test]
    fn type_decl_multiple() {
        let _ = ::env_logger::init();
        let text = 
r"
type Test = Int -> Int
and Test2 = | Test2 Test
in Test2 (\x -> x #Int+ 2)
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ("Test2")));
    }

    #[test]
    fn record_type() {
        let _ = ::env_logger::init();
        let text = 
r"
type T = { y: Int } in
let f: T -> Int = \x -> x.y in { y = f { y = 123 } }
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ("T")));
    }

    #[test]
    fn let_binding_type() {
        let _ = ::env_logger::init();
        let text = 
r"
let f: a -> b -> a = \x y -> x in f 1.0 ()
";
        let (expr, result) = typecheck_expr(text);
        assert_eq!(result, Ok(typ("Float")));
        match expr.value {
            ast::Expr::Let(ref bindings, _) => {
                assert_eq!(*bindings[0].expression.type_of(), *Type::function(vec![typ("a"), typ("b")], typ("a")));
            }
            _ => assert!(false)
        }
    }
    #[test]
    fn let_binding_recursive() {
        let _ = ::env_logger::init();
        let text = 
r"
let fac x = if x #Int== 0 then 1 else x #Int* fac (x #Int- 1) in fac
";
        let (_, result) = typecheck_expr(text);
        assert_eq!(result, Ok(Type::function(vec![typ("Int")], typ("Int"))));
    }
    #[test]
    fn let_binding_mutually_recursive() {
        let _ = ::env_logger::init();
        let text = 
r"
let f x = if x #Int< 0
          then x
          else g x
and g x = f (x #Int- 1)
in g 5
";
        let (_, result) = typecheck_expr(text);
        assert_eq!(result, Ok(typ("Int")));
    }

macro_rules! assert_m {
    ($i: expr, $p: pat => $e: expr) => {
        match $i {
            $p => $e,
            ref x => assert!(false, "Unexpected {}, found {:?}", stringify!($p), x)
        }
    }
}

    #[test]
    fn let_binding_general_mutually_recursive() {
        let _ = ::env_logger::init();
        let text =
r"
let test x = (1 #Int+ 2) #Int+ test2 x
and test2 x = 2 #Int+ test x
in test2 1";
        let (expr, result) = typecheck_expr(text);
        assert_eq!(result, Ok(typ("Int")));
        assert_m!(expr.value, ast::Expr::Let(ref binds, _) => {
            assert_eq!(binds.len(), 2);
            assert_m!(*binds[0].type_of(), ast::Type::Function(ref args, _) => {
                assert_m!(*args[0], ast::Type::Generic(_) => ())
            });
            assert_m!(*binds[1].type_of(), ast::Type::Function(ref args, _) => {
                assert_m!(*args[0], ast::Type::Generic(_) => ())
            });
        });
    }

    #[test]
    fn primitive_error() {
        let _ = ::env_logger::init();
        let text = 
r"
1 #Int== 2.2
";
        let result = typecheck(text);
        assert!(result.is_err());
    }
    #[test]
    fn binop_as_function() {
        let _ = ::env_logger::init();
        let text = 
r"
let (+) = \x y -> x #Int+ y
in 1 + 2
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ("Int")));
    }
    #[test]
    fn adt() {
        let _ = ::env_logger::init();
        let text = 
r"
type Option a = | None | Some a
in Some 1
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ_a("Option", vec![typ("Int")])));
    }
    #[test]
    fn case_constructor() {
        let _ = ::env_logger::init();
        let text = 
r"
type Option a = | None | Some a
in case Some 1 of
    | Some x -> x
    | None -> 2
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ("Int")));
    }
    #[test]
    fn real_type() {
        let _ = ::env_logger::init();
        let text = 
r"
type Eq a = {
    (==) : a -> a -> Bool
} in

let eq_Int: Eq Int = {
    (==) = \l r -> l #Int== r
}
in eq_Int
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ_a("Eq", vec![typ("Int")])));
    }

    #[test]
    fn functor() {
        let _ = ::env_logger::init();
        let text = 
r"
type Functor f = {
    map : (a -> b) -> f a -> f b
} in
type Option a = | None | Some a in
let option_Functor: Functor Option = {
    map = \f x -> case x of
                    | Some y -> Some (f y)
                    | None -> None
}
in option_Functor.map (\x -> x #Int- 1) (Some 2)
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ_a("Option", vec![typ("Int")])));
    }

    #[test]
    fn app_app_unify() {
        let _ = ::env_logger::init();
        let text = 
r"
type Monad m = {
    (>>=): m a -> (a -> m b) -> m b,
    return: a -> m a
} in
type Test a = | T a
in
let monad_Test: Monad Test = {
    (>>=) = \ta f -> case ta of
                    | T a -> f a,
    return = \x -> T x
} in
let (>>=) = monad_Test.(>>=)
in
let test: Test () = T 1 >>= \x -> monad_Test.return ()
in test
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ_a("Test", vec![Type::unit()])));
    }

    #[test]
    fn record_missing_field() {
        let _ = ::env_logger::init();
        let text = 
r"
case { x = 1 } of
    | { x, y } -> 1
";
        let result = typecheck(text);
        assert_err!(result, UndefinedField(..));
    }

    #[test]
    fn type_alias_function() {
        let _ = ::env_logger::init();
        let text = 
r"
type Fn a b = a -> b
in
let f: Fn String Int = \x -> 123
in f
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ_a("Fn", vec![typ("String"), typ("Int")])));
    }

    #[test]
    fn infer_mutually_recursive() {
        let _ = ::env_logger::init();
        let text = 
r"
let id x = x
and const x = \_ -> x
in
let c: a -> b -> a = const
in c
";
        let result = typecheck(text);
        assert!(result.is_ok());
    }

    #[test]
    fn error_mutually_recursive() {
        let _ = ::env_logger::init();
        let text = 
r"
let id x = x
and const x = \_ -> x
in const #Int+ 1
";
        let result = typecheck(text);
        assert!(result.is_err());
    }

    #[test]
    fn infer_ord_int() {
        let _ = ::env_logger::init();
        let text = 
r#"
type Ordering = | LT | EQ | GT
in

type Ord a = {
    compare : a -> a -> Ordering
} in

let ord_Int = {
    compare = \l r ->
        if l #Int< r
        then LT
        else if l #Int== r
        then EQ
        else GT
} in
let make_Ord ord
    =
    let compare = ord.compare
    in {
        (<=) = \l r -> case compare l r of
            | LT -> True
            | EQ -> True
            | GT -> False
    }
in
let (<=) = (make_Ord ord_Int).(<=)
in "" <= ""
"#;
        let result = typecheck(text);
        assert_err!(result, Unification(_, _, TypeMismatch(..)));
    }

    #[test]
    fn partial_function_unify() {
        let _ = ::env_logger::init();
        let text = 
r"
type Monad m = {
    (>>=) : m a -> (a -> m b) -> m b,
    return : a -> m a
} in
type State s a = s -> { value: a, state: s }
in
let (>>=) m f: State s a -> (a -> State s b) -> State s b =
    \state ->
        let { value, state } = m state
        and m2 = f value
        in m2 state
in
let return value: a -> State s a = \state -> { value, state }
in
let monad_State: Monad (State s) = { (>>=), return }
in { monad_State }
";
        let result = typecheck(text);
        assert_pass!(result);
    }

    ///Test that not all fields are required when unifying record patterns
    #[test]
    fn partial_pattern() {
        let _ = ::env_logger::init();
        let text = 
r#"
let { y } = { x = 1, y = "" }
in y
"#;
        let result = typecheck(text);
        assert_eq!(result, Ok(typ("String")));
    }

    #[test]
    fn unify_variant() {
        let _ = ::env_logger::init();
        let text = r#"
type Test a = | Test a
in Test 1
"#;
        let result = typecheck(text);
        assert_eq!(result, Ok(typ_a("Test", vec![typ("Int")])));
    }

    #[test]
    fn unify_transformer() {
        let _ = ::env_logger::init();
        let text = r#"
type Test a = | Test a
in
type Id a = | Id a
in
type IdT m a = m (Id a)
in
let return x: a -> IdT Test a = Test (Id x) 
in return 1
"#;
        let result = typecheck(text);
        assert_eq!(result, Ok(typ_a("IdT", vec![typ("Test"), typ("Int")])));
    }

    #[test]
    fn unify_transformer2() {
        let _ = ::env_logger::init();
        let text = r#"
type Option a = | None | Some a in
type Monad m = {
    return : a -> m a
} in
let monad_Option: Monad Option = {
    return = \x -> Some x
} in
type OptionT m a = m (Option a)
in
let monad_OptionT m: Monad m1 -> Monad (OptionT m1) =
    let return x: b -> OptionT m1 b = m.return (Some x) 
    in {
        return
    }
in 1
"#;
        let result = typecheck(text);
        assert_eq!(result, Ok(typ("Int")));
    }

    #[test]
    fn module() {
        let _ = ::env_logger::init();
        let text = 
r"
type SortedList a = | Cons a (SortedList a)
                    | Nil
in \(<) ->
    let empty = Nil
    in let insert x xs = case xs of
        | Nil -> Cons x Nil
        | Cons y ys -> if x < y
                       then Cons x xs
                       else Cons y (insert x ys)
in
let ret : { empty: SortedList a, insert: a -> SortedList a -> SortedList a }
        = { empty, insert }
in ret
";
        let result = typecheck(text);
        assert!(result.is_ok());
    }
}
