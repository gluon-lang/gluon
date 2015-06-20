use std::collections::HashMap;
use std::convert::AsRef;
use std::fmt;
use scoped_map::ScopedMap;
use base::ast;
use base::ast::MutVisitor;
use base::interner::{Interner, InternedStr};
use base::gc::Gc;
use kindcheck;
use substitution::{Substitution, Substitutable};

use self::TypeError::*;

pub use base::ast::{TcIdent, TcType, Type, Kind};

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
    UndefinedType(InternedStr),
    UndefinedField(TcType, InternedStr),
    IndexError(TcType),
    PatternError(TcType),
    KindError(kindcheck::Error),
    StringError(&'static str)
}

impl From<kindcheck::Error> for TypeError {
    fn from(e: kindcheck::Error) -> TypeError {
        KindError(e)
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TypeError::*;
        match *self {
            UndefinedVariable(name) => write!(f, "Undefined variable `{}`", name),
            NotAFunction(ref typ) => write!(f, "`{}` is not a function", typ),
            TypeMismatch(ref l, ref r) => write!(f, "Expected: {}\nFound: {} does not unify", l, r),
            UndefinedType(name) => write!(f, "Type `{}` is not defined", name),
            StringError(name) => write!(f, "{}", name),
            _ => write!(f, "{:?}", self)
        }
    }
}

pub type TcResult = Result<TcType, TypeError>;

impl Substitutable for TcType {
    fn new(id: u32) -> TcType {
        Type::Variable(ast::TypeVariable { kind: Kind::Star, id: id })
    }
    fn get_var(&self) -> Option<u32> {
        match *self {
            Type::Variable(ref var) => Some(var.id),
            _ => None
        }
    }
}

#[derive(Debug)]
pub struct TypeInfos {
    pub id_to_type: HashMap<InternedStr, TcType>,
    pub type_to_id: HashMap<TcType, TcType>
}

impl TypeInfos {
    pub fn new() -> TypeInfos {
        TypeInfos {
            id_to_type: HashMap::new(),
            type_to_id: HashMap::new()
        }
    }
    pub fn find_type_info(&self, id: &InternedStr) -> Option<&TcType> {
        self.id_to_type.get(id)
    }
    pub fn find_adt(&self, id: &InternedStr) -> Option<&TcType> {
        self.id_to_type.iter()
            .filter_map(|(_, typ)| {
                match *typ {
                    Type::Variants(ref variants) => variants.iter().find(|v| v.0 == *id),
                    _ => None
                }
            })
            .next()
            .map(|x| &x.1)
    }

    pub fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)> {
        self.id_to_type.iter()
            .find(|&(_, typ)| {
                match *typ {
                    Type::Record(ref record_fields) => {
                        fields.iter().all(|&name| record_fields.iter().any(|f| f.name == name))
                    }
                    _ => false
                }
            })
            .and_then(|t| self.type_to_id.get(&t.1).map(|id_type| (id_type, t.1)))
    }
    pub fn find_id(&self, typ: &TcType) -> Option<TcType> {
        self.type_to_id.iter()
            .filter_map(|(real_type, id_type)| {
                find_real_type(id_type, real_type, typ)
            })
            .next()
    }
    pub fn extend(&mut self, other: TypeInfos) {
        let TypeInfos { id_to_type, type_to_id } = other;
        self.id_to_type.extend(id_to_type);
        self.type_to_id.extend(type_to_id);
    }
}


fn find_real_type<'a>(id_type: &TcType, id_rhs_type: &TcType, real_type: &'a TcType) -> Option<TcType> {
    let mut result = HashMap::new();
    if find_real_type_(id_rhs_type, real_type, &mut result) {
        let mut typ = id_type.clone();
        ast::walk_mut_type(&mut typ, &mut |typ| {
            *typ = match *typ {
                Type::Generic(ref id) => result[&id.id].clone(),
                _ => return
            };
        });
        Some(typ)
    }
    else {
        None
    }
}
fn find_real_type_<'a>(id_rhs_type: &TcType, real_type: &'a TcType, out: &mut HashMap<InternedStr, &'a TcType>) -> bool {
    match (id_rhs_type, real_type) {
        (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
            l_args.iter().zip(r_args.iter())
                .all(|(l, r)| find_real_type_(l, r, out))
                && find_real_type_(&**l_ret, &**r_ret, out)
        }
        (&Type::Variable(_), _) => {
            panic!()
        }
        (&Type::Generic(ref i), real_type) => {
            out.insert(i.id, real_type);
            true
        }
        (&Type::Array(ref l), &Type::Array(ref r)) => find_real_type_(&**l, &**r, out),
        (&Type::Data(ref l, ref l_args), &Type::Data(ref r, ref r_args)) => {
            l == r && l_args.iter().zip(r_args.iter()).all(|(l, r)| find_real_type_(l, r, out))
        }
        (&Type::Record(ref l_args), &Type::Record(ref r_args)) => {
            l_args.iter().zip(r_args.iter()).all(|(l, r)| l.name == r.name && find_real_type_(&l.typ, &r.typ, out))
        }
        (&Type::App(ref l_1, ref r_1), &Type::App(ref l_2, ref r_2)) => {
            find_real_type_(l_1, l_2, out) && find_real_type_(r_1, r_2, out)
        }
        (l, r) => l == r
    }
}

pub trait TypeEnv {
    fn find_type(&self, id: &InternedStr) -> Option<(&[ast::Constraint], &TcType)>;
    fn find_type_info(&self, id: &InternedStr) -> Option<&TcType>;
    fn find_type_name(&self, typ: &TcType) -> Option<TcType>;
    fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)>;
}

pub struct Typecheck<'a> {
    environment: Option<&'a (TypeEnv + 'a)>,
    interner: &'a mut Interner,
    gc: &'a mut Gc,
    pub type_infos: TypeInfos,
    module: HashMap<InternedStr, ast::Constrained<TcType>>,
    stack: ScopedMap<InternedStr, TcType>,
    subs: Substitution<TcType>,
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

impl <'a> TypeEnv for Typecheck<'a> {
    fn find_type(&self, id: &InternedStr) -> Option<(&[ast::Constraint], &TcType)> {
        let t: Option<&TcType> = {
            let stack = &self.stack;
            let module = &self.module;
            let environment = &self.environment;
            let type_infos = &self.type_infos;
            match stack.find(id) {
                Some(x) => Some(x),
                None => module.get(id)
                    .map(|c| &c.value)
                    .or_else(|| type_infos.find_adt(id))
                    .or_else(|| environment.and_then(|e| e.find_type(id).map(|x| x.1)))
            }
        };
        t.map(|t| (&[][..], t))
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<&TcType> {
        self.type_infos.find_type_info(id)
            .or_else(|| self.environment.and_then(|e| e.find_type_info(id)))
    }
    fn find_type_name(&self, _typ: &TcType) -> Option<TcType> {
        None
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
            module: HashMap::new(),
            type_infos: TypeInfos::new(),
            stack: ScopedMap::new(),
            subs: Substitution::new(),
            errors: Errors::new()
        }
    }

    fn find(&mut self, id: &InternedStr) -> TcResult {
        let t: Option<&TcType> = {
            let stack = &self.stack;
            let module = &self.module;
            let environment = &self.environment;
            let type_infos = &self.type_infos;
            match stack.find(id) {
                Some(x) => Some(x),
                None => module.get(id)
                    .map(|c| &c.value)
                    .or_else(|| type_infos.find_adt(id))
                    .or_else(|| environment.and_then(|e| e.find_type(id).map(|x| x.1)))
            }
        };
        match t {
            Some(typ) => {
                let x = self.subs.instantiate(typ);
                debug!("Find {} : {:?}", id, x);
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

    fn find_type_info(&self, id: &InternedStr) -> Result<&TcType, TypeError> {
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

    fn replace_vars(&mut self, level: u32, variables: &HashMap<InternedStr, u32>, expr: &mut ast::LExpr<TcIdent>) {
        //Insert all type variables in the type declaration so that they get replaced by their
        //corresponding generic variable
        for (generic_id, var_id) in variables {
            unsafe { self.subs.insert(*var_id, Type::Generic(ast::Generic { kind: ast::Kind::Star, id: *generic_id })); }
        }
        //Replace all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b:'a> { level: u32, tc: &'a mut Typecheck<'b> }
        impl <'a, 'b> ReplaceVisitor<'a, 'b> {
            fn finish_type(&mut self, typ: &mut TcType) {
                ast::walk_mut_type2(typ, &mut |typ| {
                    self.tc.replace_variable(typ);
                    *typ = match *typ {
                        Type::Variable(ref var) if var.id >= self.level => {
                            let generic = format!("a_{}", var);
                            let id = self.tc.interner.intern(self.tc.gc, &generic);
                            Type::Generic(ast::Generic { kind: var.kind.clone(), id: id })
                        }
                        _ => return
                    };
                }, &mut unroll_app);
            }
        }
        impl <'a, 'b> MutVisitor for ReplaceVisitor<'a, 'b> {
            type T = TcIdent;
            fn visit_expr(&mut self, e: &mut ast::LExpr<TcIdent>) {
                match e.value {
                    ast::Expr::Identifier(ref mut id) => self.finish_type(&mut id.typ),
                    ast::Expr::FieldAccess(_, ref mut id) => self.finish_type(&mut id.typ),
                    ast::Expr::Array(ref mut array) => self.finish_type(&mut array.id.typ),
                    ast::Expr::Lambda(ref mut lambda) => self.finish_type(&mut lambda.id.typ),
                    ast::Expr::BinOp(_, ref mut id, _) => self.finish_type(&mut id.typ),
                    ast::Expr::Match(_, ref mut alts) => {
                        for alt in alts.iter_mut() {
                            match alt.pattern {
                                ast::ConstructorPattern(ref mut id, ref mut args) => {
                                    self.finish_type(&mut id.typ);
                                    for arg in args.iter_mut() {
                                        self.finish_type(&mut arg.typ);
                                    }
                                }
                                ast::IdentifierPattern(ref mut id) => self.finish_type(&mut id.typ)
                            }
                        }
                    }
                    ast::Expr::Let(ref mut bindings, _) => {
                        for bind in bindings {
                            self.finish_type(&mut bind.name.typ);
                        }
                    }
                    ast::Expr::Record(ref mut id, _) => self.finish_type(&mut id.typ),
                    _ => ()
                }
                ast::walk_mut_expr(self, e);
            }
        }
        let mut stack = ::std::mem::replace(&mut self.stack, ScopedMap::new());
        for (_, vec) in stack.iter_mut() {
            for typ in vec {
                ast::walk_mut_type2(typ, &mut |typ| {
                    self.replace_variable(typ);
                    *typ = match *typ {
                        Type::Variable(ref var) if var.id >= level => {
                            let generic = format!("a_{}", var);
                            Type::Generic(ast::Generic { kind: var.kind.clone(), id: self.interner.intern(self.gc, &generic) })
                        }
                        _ => return
                    };
                }, &mut unroll_app);
            }
        }
        ::std::mem::swap(&mut self.stack, &mut stack);
        ReplaceVisitor { level: level, tc: self }.visit_expr(expr);
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
            let mut generic = String::from("a");
            ast::walk_mut_type2(&mut typ, &mut |typ| {
                self.replace_variable(typ);
                match *typ {
                    Type::Variable(ref var) => {
                        if let None = self.subs.find_type_for_var(var.id) {
                            let gen = Type::Generic(ast::Generic { kind: var.kind.clone(), id: self.interner.intern(self.gc, &generic) });
                            let c = generic.pop().unwrap();
                            generic.push((c as u8 + 1) as char);
                            unsafe { self.subs.insert(var.id, gen) }
                        }
                    }
                    _ => ()
                };
            }, &mut unroll_app);
            self.replace_vars(0, &HashMap::new(), expr);
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
                        "==" | "<" => Ok(BOOL_TYPE.clone()),
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
            ast::Expr::Tuple(ref mut exprs) => {
                assert!(exprs.len() == 0);
                Ok(UNIT_TYPE.clone())
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
            ast::Expr::Let(ref mut bindings, ref mut body) => {
                self.stack.enter_scope();
                let level = self.subs.var_id;
                let is_recursive = bindings.iter().all(|bind| bind.arguments.len() > 0);
                if is_recursive {
                    for bind in bindings.iter_mut() {
                        if bind.name.typ.is_uninitialized() {
                            bind.name.typ = self.subs.new_var();
                        }
                        else {
                            try!(self.kindcheck(&mut bind.name.typ, &mut []));
                        }
                        self.stack_var(bind.name.name.clone(), bind.name.typ.clone());
                    }
                }
                let mut types = Vec::new();
                for bind in bindings.iter_mut() {
                    //Store the current generic -> variable mapping so that we can reverse it later
                    //Functions which are declared as `let f x = ...` are allowed to be self recursive
                    let mut typ = if bind.arguments.len() != 0 {
                        try!(self.typecheck_lambda(&mut bind.arguments, &mut bind.expression))
                    }
                    else {
                        if !bind.name.typ.is_uninitialized() {
                            try!(self.kindcheck(&mut bind.name.typ, &mut []));
                        }
                        try!(self.typecheck(&mut bind.expression))
                    };
                    debug!("let {} : {}", bind.name.name, typ);
                    if !is_recursive {
                        //Merge the type declaration and the actual type
                        if !bind.name.typ.is_uninitialized() {
                            typ = try!(self.unify(&bind.name.typ, typ));
                        }
                        bind.name.typ = typ.clone();
                        self.replace_vars(level, &HashMap::new(), &mut bind.expression);
                        self.stack_var(bind.name.name.clone(), typ);
                    }
                    else {
                        types.push(typ);
                    }
                }
                if is_recursive {
                    for (mut typ, bind) in types.into_iter().zip(bindings) {
                        //Merge the type declaration and the actual type
                        typ = try!(self.unify(&bind.name.typ, typ));
                        bind.name.typ = typ;
                        self.replace_vars(level, &HashMap::new(), &mut bind.expression);
                    }
                }
                debug!("Typecheck `in`");
                let result = self.typecheck(body);
                self.stack.exit_scope();
                result
            }
            ast::Expr::FieldAccess(ref mut expr, ref mut field_access) => {
                let mut typ = try!(self.typecheck(&mut **expr));
                if let Type::Variable(_) = typ {
                    let (record_type, _) = try!(self.find_record(&[field_access.name])
                                              .map(|t| (t.0.clone(), t.1.clone())));
                    let record_type = self.subs.instantiate(&record_type);
                    typ = try!(self.unify(&record_type, typ));
                }
                let record = match typ {
                    Type::Data(ast::TypeConstructor::Data(id), _) => {
                        self.find_type_info(&id)
                            .map(|t| t.clone())
                            .unwrap_or_else(|_| typ.clone())
                    }
                    Type::App(ref f, _) => {
                        match **f {
                            Type::Data(ast::TypeConstructor::Data(id), _) => {
                                self.find_type_info(&id)
                                    .map(|t| t.clone())
                                    .unwrap_or_else(|_| typ.clone())
                            }
                            _ => typ.clone()
                        }
                    }
                    _ => typ.clone()
                };
                let record = self.subs.instantiate(&record);
                match record {
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
                let typ = try!(self.typecheck_lambda(&mut lambda.arguments, &mut lambda.body));
                lambda.id.typ = typ.clone();
                Ok(typ)
            }
            ast::Expr::Type(ref mut id_type, ref mut typ, ref mut expr) => {
                let id = match *id_type {
                    Type::Data(ast::TypeConstructor::Data(id), ref mut args) => {
                        for arg in args.iter_mut() {
                            if let Type::Generic(ref mut gen) = *arg {
                                gen.kind = self.subs.new_kind();
                            }
                        }
                        let id_type_copy = Type::Data(ast::TypeConstructor::Data(id), args.clone());
                        self.type_infos.type_to_id.insert(typ.clone(), id_type_copy);
                        self.type_infos.id_to_type.insert(id, typ.clone());
                        try!(self.kindcheck(typ, args));
                        self.stack_var(id, typ.clone());
                        id
                    }
                    _ => panic!("ICE: Unexpected lhs of type binding {}", id_type)
                };
                self.type_infos.type_to_id.insert(typ.clone(), id_type.clone());
                self.type_infos.id_to_type.insert(id, typ.clone());
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
                    Err(_) => return Ok(Type::Record(fields))
                };
                let id_type = self.subs.instantiate(&id_type);
                let record_type = self.subs.instantiate_(&record_type);
                try!(self.unify(&Type::Record(fields), record_type));
                id.typ = id_type.clone();
                Ok(id_type.clone())
            }
        }
    }

    fn typecheck_lambda(&mut self, arguments: &mut [TcIdent], body: &mut ast::LExpr<TcIdent>) -> Result<TcType, TypeError> {
        self.stack.enter_scope();
        let mut arg_types = Vec::new();
        for arg in arguments {
            arg.typ = self.subs.new_var();
            arg_types.push(arg.typ.clone());
            self.stack_var(arg.name.clone(), arg.typ.clone());
        }
        let body_type = try!(self.typecheck(body));
        self.stack.exit_scope();
        Ok(ast::fn_type(arg_types, body_type))
    }

    fn typecheck_pattern(&mut self, pattern: &mut ast::Pattern<TcIdent>, match_type: TcType) -> Result<(), TypeError> {
        match *pattern {
            ast::ConstructorPattern(ref id, ref mut args) => {
                //Find the enum constructor and return the types for its arguments
                let ctor_type = try!(self.find(&id.name));
                let return_type = try!(self.typecheck_pattern_rec(args, ctor_type));
                try!(self.unify(&match_type, return_type));
                Ok(())
            }
            ast::IdentifierPattern(ref id) => {
                self.stack_var(id.id().clone(), match_type);
                Ok(())
            }
        }
    }

    fn typecheck_pattern_rec(&mut self, args: &mut [TcIdent], typ: TcType) -> Result<TcType, TypeError> {
        if args.len() == 0 {
            return Ok(typ)
        }
        match typ {
            Type::Function(mut argument_types, return_type) => {
                assert!(argument_types.len() == 1);
                self.stack_var(args[0].id().clone(), argument_types.pop().unwrap());
                self.typecheck_pattern_rec(&mut args[1..], *return_type)
            }
            _ => Err(PatternError(typ))
        }
    }

    fn kindcheck(&self, typ: &mut TcType, args: &mut [TcType]) -> Result<(), TypeError> {
        let f = |id| {
            self.type_infos.id_to_type.get(&id)
                .and_then(|typ| self.type_infos.type_to_id.get(typ))
        };
        let mut check = super::kindcheck::KindCheck::new(&f, args, self.subs.var_id);
        try!(check.kindcheck_type(typ));
        Ok(())
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
        let expected = self.subs.real(expected);
        let actual = self.subs.real(actual);
        debug!("{:?} <=> {:?}", expected, actual);
        match (expected, actual) {
            (&Type::Variable(ref l), _) => {
                self.union(l, actual);
                true
            }
            (_, &Type::Variable(ref r)) => {
                self.union(r, expected);
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
            (&Type::Data(ref l, ref l_args), &Type::App(_, _)) => {
                self.unify_app(l, l_args, actual, &|last, r_arg| self.unify_(last, r_arg))
            }
            (&Type::App(_, _), &Type::Data(ref r, ref r_args), ) => {
                self.unify_app(r, r_args, expected, &|last, l_arg| self.unify_(l_arg, last))
            }
            _ => expected == actual
        }
    }

    fn unify_app<F>(&self, l: &ast::TypeConstructor<InternedStr>, l_args: &[TcType], r: &TcType, f: &F) -> bool
            where F: Fn(&TcType, &TcType) -> bool {
        let r = self.subs.real(r);
        match *r {
            Type::App(ref r, ref r_arg) => {
                match l_args.last() {
                    Some(last) => {
                        f(last, r_arg) && self.unify_app(l, &l_args[0..l_args.len()-1], r, f)
                    }
                    None => false
                }
            }
            Type::Data(ref r, _) => l_args.len() == 0 && l == r,
            Type::Variable(ref r) => {
                self.union(r, &Type::Data(l.clone(), Vec::new()));
                true
            }
            _ => false
        }
    }

    fn set_type(&self, t: &mut TcType) {
        ast::walk_mut_type(t, &mut |typ| {
            self.replace_variable(typ);
            unroll_app(typ);
        });
    }

    fn replace_variable(&self, typ: &mut TcType) {
        let replacement = match *typ {
            Type::Variable(ref id) => {
                self.subs.find_type_for_var(id.id)
                    .map(|t| t.clone())
            }
            _ => None
        };
        match replacement {
            Some(x) => *typ = x,
            None => ()
        }
    }

    fn union(&self, id: &ast::TypeVariable, typ: &TcType) {
        {
            let id_type = self.subs.find_type_for_var(id.id);
            let other_type = self.subs.real(typ);
            if id_type.map(|x| x == other_type).unwrap_or(Type::Variable(id.clone()) == *other_type) {
                return
            }
        }
        let map: &mut _ = unsafe { &mut *self.subs.map.get() };
        //Always make sure the mapping is from a higher variable to a lower
        //This way the resulting variables are always equal to any variables in the globals
        //declaration
        match *typ {
            Type::Variable(ref other_id) if id.id < other_id.id => map.insert(other_id.id, box Type::Variable(id.clone())),
            _ => map.insert(id.id, box typ.clone())
        };
    }
}

impl Substitution<TcType> {

    fn variable_for2(&mut self, generic: &ast::Generic<InternedStr>) -> TcType {
        let mut var = self.variable_for(generic.id);
        if let Type::Variable(ref mut var) = var {
            var.kind = generic.kind.clone()
        }
        var
    }

    fn new_kind(&mut self) -> ast::Kind {
        self.var_id += 1;
        ast::Kind::Variable(self.var_id)
    }

    fn instantiate(&mut self, typ: &TcType) -> TcType {
        self.variables.clear();
        self.instantiate_(typ)
    }
    fn instantiate_(&mut self, typ: &TcType) -> TcType {
        match *typ {
            Type::Generic(ref x) => {
                let var = self.variable_for2(x);
                debug!("Bind generic {} -> {}", x, var);
                var
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
                Type::App(Box::new(self.instantiate_(f)), Box::new(self.instantiate_(r)))
            }
            ref x => x.clone()
        }
    }
}

fn unroll_app(typ: &mut TcType) {
    *typ = match *typ {
        Type::App(ref mut l, ref mut r) => {
            match &mut **l {
                &mut Type::Data(ref mut l, ref mut args) => {
                    let l = ::std::mem::replace(l, ast::TypeConstructor::Builtin(ast::BuiltinType::StringType));
                    let r = ::std::mem::replace(&mut **r, Type::Variable(ast::TypeVariable { kind: Kind::Star, id: 0 }));
                    let mut args = ::std::mem::replace(args, Vec::new());
                    args.push(r);
                    Type::Data(l, args)
                }
                _ => return
            }
        }
        _ => return
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
            ast::Expr::Tuple(ref exprs) => {
                assert!(exprs.len() == 0);
                &UNIT_TYPE
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
            ast::Expr::Let(..) => &UNIT_TYPE,
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

impl <T> Typed for ast::Binding<T>
    where T: Typed<Id=InternedStr> + ast::AstId<Untyped=InternedStr> {
    type Id = T::Untyped;
    fn type_of(&self) -> &TcType {
        self.name.type_of()
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
            None if is_var => Type::Generic(ast::Generic { kind: ast::Kind::Star, id: intern(s) }),
            None => Type::Data(ast::TypeConstructor::Data(intern(s)), Vec::new())
        }
    }
    fn typ_a(s: &str, args: Vec<TcType>) -> TcType {
        assert!(s.len() != 0);
        let is_var = s.chars().next().unwrap().is_lowercase();
        match ast::str_to_primitive_type(s) {
            Some(b) => Type::Builtin(b),
            None if is_var => Type::Generic(ast::Generic { kind: ast::Kind::Star, id: intern(s) }),
            None => Type::Data(ast::TypeConstructor::Data(intern(s)), args)
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
type Test = { x: Int } in { x = 0 }
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
                assert_eq!(*bindings[0].expression.type_of(), ast::fn_type(vec![typ("a"), typ("b")], typ("a")));
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
        assert_eq!(result, Ok(ast::fn_type(vec![typ("Int")], typ("Int"))));
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
            _ => assert!(false)
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
                assert_m!(args[0], ast::Type::Generic(_) => ())
            });
            assert_m!(*binds[1].type_of(), ast::Type::Function(ref args, _) => {
                assert_m!(args[0], ast::Type::Generic(_) => ())
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
    fn prelude_test() {
        use std::fs::File;
        use std::io::Read;
        let mut text = String::new();
        File::open("prelude.s").unwrap().read_to_string(&mut text).unwrap();
        let result = typecheck(&text);
        assert_eq!(result.map(|_| ()), Ok(()));
    }

    #[bench]
    fn prelude(b: &mut ::test::Bencher) {
        use std::fs::File;
        use std::io::Read;
        //Only parse once since it takes much more time when running in debug mode
        thread_local! { static PRELUDE: ::std::cell::RefCell<Option<ast::LExpr<TcIdent>>> = ::std::cell::RefCell::new(None) }
        let expr = PRELUDE.with(|expr| {
            let mut expr = expr.borrow_mut();
            if let None = *expr {
                let _ = ::env_logger::init();
                let mut text = String::new();
                File::open("prelude.s").unwrap().read_to_string(&mut text).unwrap();
                *expr = Some(parse_new(&text))
            }
            expr.as_ref().unwrap().clone()
        });
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut(ref mut interner, ref mut gc) = &mut *interner;
        b.iter(|| {
            let mut tc = Typecheck::new(interner, gc);
            ::test::black_box(tc.typecheck_expr(&mut expr.clone()))
        })
    }
}
