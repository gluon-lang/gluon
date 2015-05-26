use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::convert::AsRef;
use std::fmt;
use scoped_map::ScopedMap;
use base::ast;
use base::ast::MutVisitor;
use base::interner::{Interner, InternedStr};
use base::gc::Gc;

use self::TypeError::*;

pub use base::ast::{TcIdent, TcType, Type};


pub static INT_TYPE: TcType = Type::Builtin(ast::IntType);
pub static FLOAT_TYPE: TcType = Type::Builtin(ast::FloatType);
pub static STRING_TYPE: TcType = Type::Builtin(ast::StringType);
pub static BOOL_TYPE: TcType = Type::Builtin(ast::BoolType);
pub static UNIT_TYPE: TcType = Type::Builtin(ast::UnitType);

#[derive(Debug, PartialEq)]
enum TypeError {
    UndefinedVariable(InternedStr),
    NotAFunction(TcType),
    TypeMismatch(TcType, TcType),
    UnboundVariable,
    UndefinedStruct(InternedStr),
    UndefinedField(TcType, InternedStr),
    IndexError(TcType),
    StringError(&'static str)
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self)
    }
}

pub type TcResult = Result<TcType, TypeError>;

pub struct TypeInfos {
    pub datas: HashMap<InternedStr, Vec<ast::Constructor<TcIdent>>>,
    pub id_to_type: HashMap<InternedStr, TcType>,
    pub type_to_id: HashMap<TcType, TcType>
}

impl TypeInfos {
    pub fn new() -> TypeInfos {
        TypeInfos {
            datas: HashMap::new(),
            id_to_type: HashMap::new(),
            type_to_id: HashMap::new()
        }
    }
    pub fn find_type_info(&self, id: &InternedStr) -> Option<&[ast::Constructor<TcIdent>]> {
        self.datas.get(id)
            .map(|vec| &**vec)
    }

    pub fn find_record(&self, field: &InternedStr) -> Option<&TcType> {
        self.id_to_type.iter()
            .find(|&(_, typ)| {
                match *typ {
                    Type::Record(ref fields) => fields.iter().any(|f| f.name == *field),
                    _ => false
                }
            })
            .map(|t| t.1)
    }
    pub fn find_id(&self, typ: &TcType) -> Option<&TcType> {
        self.type_to_id.get(typ)
    }
    pub fn extend(&mut self, other: TypeInfos) {
        let TypeInfos { datas, id_to_type, type_to_id } = other;
        self.datas.extend(datas);
        self.id_to_type.extend(id_to_type);
        self.type_to_id.extend(type_to_id);
    }
}

pub trait TypeEnv {
    fn find_type(&self, id: &InternedStr) -> Option<(&[ast::Constraint], &TcType)>;
    fn find_type_info(&self, id: &InternedStr) -> Option<&[ast::Constructor<TcIdent>]>;
    fn find_type_name(&self, typ: &TcType) -> Option<&TcType>;
}

pub struct Typecheck<'a> {
    environment: Option<&'a (TypeEnv + 'a)>,
    interner: &'a mut Interner,
    gc: &'a mut Gc,
    pub type_infos: TypeInfos,
    module: HashMap<InternedStr, ast::Constrained<TcType>>,
    stack: ScopedMap<InternedStr, TcType>,
    subs: Substitution,
    errors: Errors<ast::Located<TypeError>>
}

#[derive(Debug, PartialEq)]
struct Errors<T> {
    errors: Vec<T>
}

impl <T> Errors<T> {
    fn new() -> Errors<T> {
        Errors { errors: Vec::new() }
    }
    fn has_errors(&self) -> bool {
        self.errors.len() != 0
    }
    fn error(&mut self, t: T) {
        self.errors.push(t);
    }
}

impl <T: fmt::Display> fmt::Display for Errors<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in self.errors.iter() {
            try!(write!(f, "{}\n", error));
        }
        Ok(())
    }
}

pub type StringErrors = Errors<ast::Located<TypeError>>;

impl <'a> Typecheck<'a> {
    
    pub fn new(interner: &'a mut Interner, gc: &'a mut Gc) -> Typecheck<'a> {
        Typecheck {
            environment: None,
            interner: interner,
            gc: gc,
            module: HashMap::new(),
            type_infos: TypeInfos::new(),
            stack: ScopedMap::new(),
            subs: Substitution::new(),
            errors: Errors::new()
        }
    }

    fn find(&mut self, id: &InternedStr) -> TcResult {
        let t: Option<(&[ast::Constraint], &TcType)> = {
            let stack = &self.stack;
            let module = &self.module;
            let environment = &self.environment;
            match stack.find(id).map(|typ| (&[][..], typ)) {
                Some(x) => Some(x),
                None => module.get(id)
                    .map(|c| (&c.constraints[..], &c.value))
                    .or_else(|| environment.and_then(|e| e.find_type(id)))
            }
        };
        match t {
            Some((constraints, typ)) => {
                let x = self.subs.instantiate_constrained(constraints, typ);
                debug!("Find {} : {:?}", id, x);
                Ok(x)
            }
            None => Err(UndefinedVariable(id.clone()))
        }
    }

    fn find_record(&self, field: &InternedStr) -> Result<&TcType, TypeError> {
        self.type_infos.find_record(field)
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(UndefinedStruct(field.clone())))
    }

    fn find_type_info(&self, id: &InternedStr) -> Result<&[ast::Constructor<TcIdent>], TypeError> {
        self.type_infos.find_type_info(id)
            .or_else(|| self.environment.and_then(|e| e.find_type_info(id)))
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(UndefinedStruct(id.clone())))
    }
    
    fn stack_var(&mut self, id: InternedStr, typ: TcType) {
        self.stack.insert(id, typ);
    }

    pub fn add_environment(&mut self, env: &'a TypeEnv) {
        self.environment = Some(env);
    }

    fn replace_vars(&mut self, variables: &HashMap<InternedStr, u32>, expr: &mut ast::LExpr<TcIdent>) {
        //Insert all type variables in the type declaration so that they get replaced by their
        //corresponding generic variable
        for (generic_id, var_id) in variables {
            self.subs.map.insert(*var_id, box Type::Generic(*generic_id));
        }
        //Replace all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b:'a> { tc: &'a mut Typecheck<'b> }
        impl <'a, 'b> ReplaceVisitor<'a, 'b> {
            fn finish_type(&mut self, location: ast::Location, typ: &mut TcType) {
                let mut unbound_variable = false;
                ast::walk_mut_type(typ, &mut |typ| {
                    self.tc.replace_variable(typ);
                    if let Type::Variable(_) = *typ {
                        unbound_variable = true;
                    }
                });
                if unbound_variable {
                    self.tc.errors.error(ast::Located { location: location, value: TypeError::UnboundVariable });
                }
            }
        }
        impl <'a, 'b> MutVisitor for ReplaceVisitor<'a, 'b> {
            type T = TcIdent;
            fn visit_expr(&mut self, e: &mut ast::LExpr<TcIdent>) {
                match e.value {
                    ast::Expr::Identifier(ref mut id) => self.finish_type(e.location, &mut id.typ),
                    ast::Expr::FieldAccess(_, ref mut id) => self.finish_type(e.location, &mut id.typ),
                    ast::Expr::Array(ref mut array) => self.finish_type(e.location, &mut array.id.typ),
                    ast::Expr::Lambda(ref mut lambda) => self.finish_type(e.location, &mut lambda.id.typ),
                    ast::Expr::BinOp(_, ref mut id, _) => self.finish_type(e.location, &mut id.typ),
                    ast::Expr::Match(_, ref mut alts) => {
                        for alt in alts.iter_mut() {
                            match alt.pattern {
                                ast::ConstructorPattern(ref mut id, ref mut args) => {
                                    self.finish_type(e.location, &mut id.typ);
                                    for arg in args.iter_mut() {
                                        self.finish_type(e.location, &mut arg.typ);
                                    }
                                }
                                ast::IdentifierPattern(ref mut id) => self.finish_type(e.location, &mut id.typ)
                            }
                        }
                    }
                    ast::Expr::Record(ref mut id, _) => self.finish_type(e.location, &mut id.typ),
                    _ => ()
                }
                ast::walk_mut_expr(self, e);
            }
        }
        ReplaceVisitor { tc: self }.visit_expr(expr);
    }

    pub fn typecheck_expr(&mut self, expr: &mut ast::LExpr<TcIdent>) -> Result<TcType, StringErrors> {
        self.subs.clear();
        self.stack.clear();

        let mut typ = match self.typecheck(expr) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.error(ast::Located { location: expr.location, value: err });
                return Err(::std::mem::replace(&mut self.errors, Errors::new()));
            }
        };
        if self.errors.has_errors() {
            Err(::std::mem::replace(&mut self.errors, Errors::new()))
        }
        else {
            let mut generic = String::from_str("a");
            ast::walk_mut_type(&mut typ, &mut |typ| {
                match *typ {
                    Type::Variable(id) => {
                        if let None = self.find_type_for_var(id) {
                            let gen = Type::Generic(self.interner.intern(self.gc, &generic));
                            let c = generic.pop().unwrap();
                            generic.push((c as u8 + 1) as char);
                            self.subs.map.insert(id, Box::new(gen));
                        }
                    }
                    _ => ()
                };
                self.replace_variable(typ);
            });
            self.replace_vars(&HashMap::new(), expr);
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
                    ast::Integer(_) => INT_TYPE.clone(),
                    ast::Float(_) => FLOAT_TYPE.clone(),
                    ast::String(_) => STRING_TYPE.clone(),
                    ast::Bool(_) => BOOL_TYPE.clone()
                })
            }
            ast::Expr::Call(ref mut func, ref mut args) => {
                let mut func_type = try!(self.typecheck(&mut**func));
                for arg in args.iter_mut() {
                    let f = Type::Function(vec![self.subs.new_var()], Box::new(self.subs.new_var()));
                    func_type = try!(self.unify(&f, func_type));
                    match func_type {
                        Type::Function(arg_type, ret) => {
                            assert!(arg_type.len() == 1);
                            let actual = try!(self.typecheck(arg));
                            try!(self.unify(&arg_type[0], actual));
                            func_type = *ret;
                        }
                        t => return Err(NotAFunction(t))
                    }
                }
                Ok(func_type)
            }
            ast::Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut**pred));
                try!(self.unify(&BOOL_TYPE, pred_type));
                let true_type = try!(self.typecheck(&mut**if_true));
                let false_type = match *if_false {
                    Some(ref mut if_false) => try!(self.typecheck(&mut**if_false)),
                    None => UNIT_TYPE.clone()
                };
                self.unify(&true_type, false_type)
            }
            ast::Expr::While(ref mut pred, ref mut expr) => {
                let pred_type = try!(self.typecheck(&mut **pred));
                try!(self.unify(&BOOL_TYPE, pred_type));
                self.typecheck(&mut**expr)
                    .map(|_| UNIT_TYPE.clone())
            }
            ast::Expr::BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut**lhs));
                let rhs_type = try!(self.typecheck(&mut**rhs));
                if op.name.starts_with("#") {
                    let arg_type = try!(self.unify(&lhs_type, rhs_type));
                    let offset;
                    let typ = if op.name[1..].starts_with("Int") {
                        offset = "Int".len();
                        op.typ = ast::fn_type(vec![INT_TYPE.clone(), INT_TYPE.clone()], INT_TYPE.clone());
                        try!(self.unify(&INT_TYPE, arg_type))
                    }
                    else if op.name[1..].starts_with("Float") {
                        offset = "Float".len();
                        op.typ = ast::fn_type(vec![FLOAT_TYPE.clone(), FLOAT_TYPE.clone()], FLOAT_TYPE.clone());
                        try!(self.unify(&FLOAT_TYPE, arg_type))
                    }
                    else {
                        panic!("ICE: Unknown primitive type")
                    };
                    match &op.name[1+offset..] {
                        "+" | "-" | "*" => Ok(typ),
                        "==" => Ok(BOOL_TYPE.clone()),
                        _ => Err(UndefinedVariable(op.name.clone()))
                    }
                }
                else {
                    match &op.name[..] {
                        "&&" | "||" => {
                            try!(self.unify(&lhs_type, rhs_type.clone()));
                            self.unify(&BOOL_TYPE, lhs_type)
                        }
                        _ => {
                            op.typ = try!(self.find(op.id()));
                            let func_type = ast::fn_type(vec![lhs_type, rhs_type], self.subs.new_var());
                            match try!(self.unify(&op.typ, func_type)) {
                                Type::Function(_, return_type) => 
                                    match *return_type {
                                        Type::Function(_, return_type) => Ok(*return_type),
                                        _ => panic!("ICE: unify binop")
                                    },
                                _ => panic!("ICE: unify binop")
                            }
                        }
                    }
                }
            }
            ast::Expr::Block(ref mut exprs) => {
                self.stack.enter_scope();
                let mut typ = Type::Builtin(ast::UnitType);
                for expr in exprs.iter_mut() {
                    typ = try!(self.typecheck(expr));
                }
                self.stack.exit_scope();
                Ok(typ)
            }
            ast::Expr::Match(ref mut expr, ref mut alts) => {
                let typ = try!(self.typecheck(&mut**expr));
                self.stack.enter_scope();
                try!(self.typecheck_pattern(&mut alts[0].pattern, typ.clone()));
                let alt1_type = try!(self.typecheck(&mut alts[0].expression));
                self.stack.exit_scope();

                for alt in alts.iter_mut().skip(1) {
                    self.stack.enter_scope();
                    try!(self.typecheck_pattern(&mut alt.pattern, typ.clone()));
                    let alt_type = try!(self.typecheck(&mut alt.expression));
                    self.stack.exit_scope();
                    try!(self.unify(&alt1_type, alt_type));
                }
                Ok(alt1_type)
            }
            ast::Expr::Let(ref mut id, ref mut expr, ref mut body) => {
                let id_type = self.subs.instantiate(&id.typ);
                //Store the current generic -> variable mapping so that we can reverse it later
                let variables = self.subs.variables.clone();
                debug!("--- {:?} {}", variables, id.typ);
                let mut typ = try!(self.typecheck(&mut **expr));
                if id.typ != UNIT_TYPE {
                    //Merge the type declaration and the actual type
                    typ = try!(self.merge(id_type, typ));
                }
                self.replace_vars(&variables, &mut **expr);
                ast::walk_mut_type(&mut typ, &mut |typ| {
                    self.replace_variable(typ);
                });
                id.typ = typ.clone();
                debug!("let {} : {}", id.name, typ);
                self.stack_var(id.name.clone(), typ);
                body.as_mut().map(|body| self.typecheck(&mut **body))
                    .unwrap_or(Ok(UNIT_TYPE.clone()))
            }
            ast::Expr::Assign(ref mut lhs, ref mut rhs) => {
                let rhs_type = try!(self.typecheck(&mut **rhs));
                let lhs_type = try!(self.typecheck(&mut **lhs));
                try!(self.unify(&lhs_type, rhs_type));
                Ok(UNIT_TYPE.clone())
            }
            ast::Expr::FieldAccess(ref mut expr, ref mut field_access) => {
                let mut typ = try!(self.typecheck(&mut **expr));
                if let Type::Variable(_) = typ {
                    let record_type = try!(self.find_record(&field_access.name));
                    typ = try!(self.unify(record_type, typ));
                }
                let record = match typ {
                    Type::Data(ast::TypeConstructor::Data(id), _) => {
                        self.type_infos.id_to_type.get(&id).unwrap_or(&typ)
                    }
                    _ => &typ
                };
                match *record {
                    Type::Record(ref fields) => {
                        let field_type = fields.iter()
                            .find(|field| field.name == *field_access.id())
                            .map(|field| field.typ.clone());
                        field_access.typ = match field_type {
                            Some(typ) => typ,
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
                a.id.typ = Type::Array(box expected_type);
                Ok(a.id.typ.clone())
            }
            ast::Expr::ArrayAccess(ref mut array, ref mut index) => {
                let array_type = try!(self.typecheck(&mut **array));
                let var = self.subs.new_var();
                let array_type = try!(self.unify(&Type::Array(box var), array_type));
                let typ = match array_type {
                    Type::Array(typ) => *typ,
                    typ => return Err(IndexError(typ))
                };
                let index_type = try!(self.typecheck(&mut **index));
                try!(self.unify(&INT_TYPE, index_type));
                Ok(typ)
            }
            ast::Expr::Lambda(ref mut lambda) => {
                self.stack.enter_scope();
                let mut arg_types = Vec::new();
                for arg in lambda.arguments.iter_mut() {
                    arg.typ = self.subs.new_var();
                    arg_types.push(arg.typ.clone());
                    self.stack_var(arg.name.clone(), arg.typ.clone());
                }
                let body_type = try!(self.typecheck(&mut *lambda.body));
                self.stack.exit_scope();
                lambda.id.typ = ast::fn_type(arg_types, body_type);
                Ok(lambda.id.typ.clone())
            }
            ast::Expr::Type(ref id_type, ref mut typ, ref mut expr) => {
                match *id_type {
                    Type::Data(ast::TypeConstructor::Data(id), _) => {
                        self.stack_var(id, typ.clone());
                        self.type_infos.id_to_type.insert(id, typ.clone());
                    }
                    _ => panic!("ICE: Unexpected lhs of type binding {}", id_type)
                }
                self.type_infos.type_to_id.insert(typ.clone(), id_type.clone());
                let expr_type = try!(self.typecheck(&mut **expr));
                Ok(expr_type)
            }
            ast::Expr::Record(ref mut id, ref mut fields) => {
                let typ = try!(fields.iter_mut()
                    .map(|field| Ok(ast::Field {
                        name: field.0,
                        typ: try!(self.typecheck(&mut field.1))
                    }))
                    .collect::<Result<_, _>>()
                    .map(Type::Record));
                let type_name = self.type_infos.type_to_id.get(&typ)
                        .map(|t| t.clone());
                let typ = type_name.unwrap_or(typ);
                id.typ = typ.clone();
                Ok(typ)
            }
        }
    }

    fn typecheck_pattern(&mut self, pattern: &mut ast::Pattern<TcIdent>, match_type: TcType) -> Result<(), TypeError> {
        let typename = match match_type {
            Type::Data(ast::TypeConstructor::Data(id), _) => id,
            _ => return Err(StringError("Pattern matching only works on data types"))
        };
        match *pattern {
            ast::ConstructorPattern(ref name, ref mut args) => {
                //Find the enum constructor and return the types for its arguments
                let ctor_type = {
                    let constructors = try!(self.find_type_info(&typename));
                    match constructors.iter().find(|ctor| ctor.name.id() == name.id()) {
                        Some(ctor) => ctor.name.typ.clone(),
                        None => return Err(StringError("Undefined constructor"))
                    }
                };
                let ctor_type = self.subs.instantiate(&ctor_type);
                let (argument_types, return_type) = match ctor_type {
                    Type::Function(argument_types, return_type) => {
                        (argument_types, *return_type)
                    }
                    _ => return Err(StringError("Enum constructor must be a function type"))
                };
                try!(self.unify(&match_type, return_type));
                for (arg, typ) in args.iter().zip(argument_types.into_iter()) {
                    self.stack_var(arg.id().clone(), typ);
                }
                Ok(())
            }
            ast::IdentifierPattern(ref id) => {
                self.stack_var(id.id().clone(), match_type);
                Ok(())
            }
        }
    }

    fn unify(&self, expected: &TcType, mut actual: TcType) -> TcResult {
        debug!("Unify {:?} <=> {:?}", expected, actual);
        if self.unify_(expected, &actual) {
            self.set_type(&mut actual);
            Ok(actual)
        }
        else {
            let mut expected = expected.clone();
            self.set_type(&mut expected);
            self.set_type(&mut actual);
            Err(TypeMismatch(expected, actual))
        }
    }
    fn unify_(&self, expected: &TcType, actual: &TcType) -> bool {
        let expected = self.real_type(expected);
        let actual = self.real_type(actual);
        debug!("{:?} <=> {:?}", expected, actual);
        match (expected, actual) {
            (&Type::Variable(ref l), _) => {
                self.union(*l, actual);
                true
            }
            (_, &Type::Variable(ref r)) => {
                self.union(*r, expected);
                true
            }
            (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    l_args.iter().zip(r_args.iter()).all(|(l, r)| self.unify_(l, r)) && self.unify_(&**l_ret, &**r_ret)
                }
                else {
                    false
                }
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => self.unify_(&**l, &**r),
            (&Type::Data(ref l, ref l_args), &Type::Data(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| self.unify_(l, r))
            }
            (&Type::Record(ref l_args), &Type::Record(ref r_args)) => {
                l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter())
                    .all(|(l, r)| l.name == r.name && self.unify_(&l.typ, &r.typ))
            }
            _ => expected == actual
        }
    }
    fn merge(&self, mut expected: TcType, mut actual: TcType) -> TcResult {
        if self.merge_(&expected, &actual) {
            Ok(expected)
        }
        else {
            self.set_type(&mut expected);
            self.set_type(&mut actual);
            Err(TypeMismatch(expected, actual))
        }
    }
    fn merge_(&self, expected: &TcType, actual: &TcType) -> bool {
        let expected = self.real_type(expected);
        let actual = self.real_type(actual);
        debug!("Merge {:?} {:?}", expected, actual);
        match (expected, actual) {
            (_, &Type::Variable(ref r)) => {
                self.union(*r, expected);
                true
            }
            (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    l_args.iter()
                        .zip(r_args.iter())
                        .all(|(l, r)| self.merge_(l, r))
                        && self.merge_(&**l_ret, &**r_ret)
                }
                else {
                    false
                }
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => self.merge_(&**l, &**r),
            (&Type::Data(ref l, ref l_args), &Type::Data(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| self.merge_(l, r))
            }
            _ => expected == actual
        }
    }

    fn set_type(&self, t: &mut TcType) {
        ast::walk_mut_type(t, &mut |typ| self.replace_variable(typ) );
    }
    
    fn replace_variable(&self, typ: &mut TcType) {
        let replacement = match *typ {
            Type::Variable(id) => {
                self.find_type_for_var(id)
                    .map(|t| t.clone())
            }
            _ => None
        };
        match replacement {
            Some(x) => *typ = x,
            None => ()
        }
    }

    fn real_type<'r>(&'r self, typ: &'r TcType) -> &'r TcType {
        let typ = match *typ {
            Type::Variable(var) => match self.find_type_for_var(var) {
                Some(t) => t,
                None => typ
            },
            _ => typ
        };
        self.type_infos.find_id(typ)
            .or_else(|| self.environment.and_then(|e| e.find_type_name(typ)))
            .unwrap_or(typ)
    }

    fn find_type_for_var(&self, var: u32) -> Option<&TcType> {
        //Use unsafe so that we can hold a reference into the map and continue
        //to look for parents
        //Since we never have a cycle in the map we will never hold a &mut
        //to the same place
        let this: &mut Substitution = unsafe {
            let s: *const Substitution = &self.subs;
            ::std::mem::transmute(s)
        };
        this.map.get_mut(&var).map(|typ| {
            match **typ {
                Type::Variable(parent_var) if parent_var != var => {
                    match self.find_type_for_var(parent_var) {
                        Some(other) => { **typ = other.clone(); }
                        None => ()
                    }
                    &**typ
                }
                _ => &**typ
            }
        })
    }
    fn union(&self, id: u32, typ: &TcType) {
        {
            let id_type = self.find_type_for_var(id);
            let other_type = self.real_type(typ);
            if id_type.map(|x| x == other_type).unwrap_or(&Type::Variable(id) == other_type) {
                return
            }
        }
        let this: &mut Substitution = unsafe {
            let e: *const Substitution = &self.subs;
            ::std::mem::transmute(e)
        };
        //Always make sure the mapping is from a higher variable to a lower
        //This way the resulting variables are always equal to any variables in the globals
        //declaration
        match *typ {
            Type::Variable(other_id) if id < other_id => this.assign_union(other_id, Type::Variable(id)),
            _ => this.assign_union(id, typ.clone())
        }
    }
}

#[derive(Debug)]
struct Substitution {
    map: HashMap<u32, Box<TcType>>,
    constraints: HashMap<u32, Vec<TcType>>,
    variables: HashMap<InternedStr, u32>,
    var_id: u32
}
impl Substitution {
    fn new() -> Substitution {
        Substitution {
            map: HashMap::new(),
            constraints: HashMap::new(),
            variables: HashMap::new(),
            var_id: 0
        }
    }

    fn variable_for(&mut self, id: InternedStr) -> u32 {
        match self.variables.entry(id) {
            Entry::Vacant(entry) => {
                self.var_id += 1;
                *entry.insert(self.var_id)
            }
            Entry::Occupied(entry) => *entry.get()
        }
    }

    fn clear(&mut self) {
        self.map.clear();
        self.constraints.clear();
        self.variables.clear();
        self.var_id = 0;
    }

    fn assign_union(&mut self, id: u32, typ: TcType) {
        match self.constraints.remove(&id) {
            Some(constraints) => {
                match typ {
                    Type::Variable(other_id) => {
                        self.constraints.insert(other_id, constraints);
                    }
                    _ => ()
                }
            }
            None => ()
        }
        self.map.insert(id, box typ);
    }

    fn new_var(&mut self) -> TcType {
        self.var_id += 1;
        Type::Variable(self.var_id)
    }

    fn instantiate_constrained(&mut self, constraints: &[ast::Constraint], typ: &TcType) -> TcType {
        self.variables.clear();
        for constraint in constraints.iter() {
            let c = Type::Data(ast::TypeConstructor::Data(constraint.name), Vec::new());
            let var = self.variable_for(constraint.type_variable);
            match self.constraints.entry(var) {
                Entry::Vacant(entry) => {
                    entry.insert(vec![c]);
                }
                Entry::Occupied(entry) => {
                    entry.into_mut().push(c);
                }
            }
        }
        self.instantiate_(typ)
    }
    fn instantiate(&mut self, typ: &TcType) -> TcType {
        self.variables.clear();
        self.instantiate_(typ)
    }
    fn instantiate_(&mut self, typ: &TcType) -> TcType {
        match *typ {
            Type::Generic(x) => {
                let var = self.variable_for(x);
                debug!("Bind generic {} -> {}", x, var);
                Type::Variable(var)
            }
            Type::Function(ref args, ref return_type) => {
                let args2 = args.iter().map(|a| self.instantiate_(a)).collect();
                Type::Function(args2, box self.instantiate_(&**return_type))
            }
            Type::Array(ref typ) => Type::Array(box self.instantiate_(&**typ)),
            Type::Data(ref id, ref args) => {
                let args2 = args.iter().map(|a| self.instantiate_(a)).collect();
                Type::Data(id.clone(), args2)
            }
            Type::Record(ref fields) => {
                Type::Record(fields.iter()
                    .map(|field| ast::Field {
                            name: field.name,
                            typ: self.instantiate_(&field.typ)
                        }
                    )
                    .collect())
            }
            Type::App(ref f, ref r) => {
                Type::App(Box::new(self.instantiate_(f)), Box::new(self.instantiate(r)))
            }
            ref x => x.clone()
        }
    }
}

pub trait Typed {
    type Id;
    fn type_of(&self) -> &Type<Self::Id>;
}
impl <Id> Typed for TcIdent<Id> {
    type Id = Id;
    fn type_of(&self) -> &Type<Id> {
        &self.typ
    }
}
impl <Id> Typed for ast::Expr<Id>
    where Id: Typed<Id=InternedStr> + AsRef<str> + ast::AstId<Untyped=InternedStr> {
    type Id = Id::Id;
    fn type_of(&self) -> &Type<Id::Untyped> {
        match *self {
            ast::Expr::Identifier(ref id) => id.type_of(),
            ast::Expr::Literal(ref lit) => {
                match *lit {
                    ast::Integer(_) => &INT_TYPE,
                    ast::Float(_) => &FLOAT_TYPE,
                    ast::String(_) => &STRING_TYPE,
                    ast::Bool(_) => &BOOL_TYPE
                }
            }
            ast::Expr::IfElse(_, ref arm, _) => arm.type_of(),
            ast::Expr::Block(ref exprs) => {
                match exprs.last() {
                    Some(last) => last.type_of(),
                    None => &UNIT_TYPE
                }
            }
            ast::Expr::BinOp(ref lhs, ref op, _) => {
                match *op.type_of() {
                    Type::Function(_, ref return_type) => 
                        match **return_type {
                            Type::Function(_, ref return_type) => return return_type,
                            _ => ()
                        },
                    _ => ()
                }
                match AsRef::<str>::as_ref(op) {
                    "+" | "-" | "*" => lhs.type_of(),
                    "<" | ">" | "<=" | ">=" | "==" | "!=" | "&&" | "||" => &BOOL_TYPE,
                    _ => panic!()
                }
            }
            ast::Expr::Let(..) | ast::Expr::While(..) | ast::Expr::Assign(..) => &UNIT_TYPE,
            ast::Expr::Call(ref func, _) => {
                match func.type_of() {
                    &Type::Function(_, ref return_type) => &**return_type,
                    x => panic!("{:?}", x)
                }
            }
            ast::Expr::Match(_, ref alts) => alts[0].expression.type_of(),
            ast::Expr::FieldAccess(_, ref id) => id.type_of(),
            ast::Expr::Array(ref a) => a.id.type_of(),
            ast::Expr::ArrayAccess(ref array, _) => match array.type_of() {
                &Type::Array(ref t) => &**t,
                t => panic!("Not an array type {:?}", t)
            },
            ast::Expr::Lambda(ref lambda) => lambda.id.type_of(),
            ast::Expr::Type(_, _, ref expr) => expr.type_of(),
            ast::Expr::Record(ref id, _) => id.type_of()
        }
    }
}

impl Typed for Option<Box<ast::Located<ast::Expr<TcIdent>>>> {
    type Id = InternedStr;
    fn type_of(&self) -> &TcType {
        match *self {
            Some(ref t) => t.type_of(),
            None => &UNIT_TYPE
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use base::ast;
    use super::super::tests::{get_local_interner, intern};

    fn typ(s: &str) -> TcType {
        assert!(s.len() != 0);
        let is_var = s.chars().next().unwrap().is_lowercase();
        match ast::str_to_primitive_type(s) {
            Some(b) => Type::Builtin(b),
            None if is_var => Type::Generic(intern(s)),
            None => Type::Data(ast::TypeConstructor::Data(intern(s)), Vec::new())
        }
    }

    pub fn parse_new(s: &str) -> ast::LExpr<TcIdent> {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut(ref mut interner, ref mut gc) = &mut *interner;
        let x = ::parser_new::parse_tc(gc, interner, s)
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
        match result.unwrap() {
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
        assert_eq!(result, Ok(ast::fn_type(vec![typ("Int"), typ("Int")], typ("Int"))));
    }

    #[test]
    fn type_decl() {
        let _ = ::env_logger::init();
        let text = 
r"
type Test = { x: Int } in { x: 0 }
";
        let result = typecheck(text);
        assert_eq!(result, Ok(typ("Test")));
    }

    #[test]
    fn record_type() {
        let _ = ::env_logger::init();
        let text = 
r"
type T = { y: Int } in
let f: T -> Int = \x -> x.y in { y: f { y: 123 } }
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
            ast::Expr::Let(_, ref expr, _) => {
                assert_eq!(*expr.type_of(), ast::fn_type(vec![typ("a"), typ("b")], typ("a")));
            }
            _ => assert!(false)
        }
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
}
