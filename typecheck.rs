use std::collections::HashMap;
use scoped_map::ScopedMap;
use ast::*;
use interner::*;



#[deriving(Clone, Eq, PartialEq, Show)]
pub struct TcIdent {
    pub typ: TcType,
    pub name: InternedStr
}
impl TcIdent {
    pub fn id(&self) -> &InternedStr {
        &self.name
    }
}

impl Str for TcIdent {
    fn as_slice(&self) -> &str {
        self.name.as_slice()
    }
}

type TcType = Type<InternedStr>;

#[deriving(Show)]
enum TypeError {
    UndefinedVariable(InternedStr),
    NotAFunction(TcType),
    WrongNumberOfArguments(uint, uint),
    TypeMismatch(TcType, TcType),
    UndefinedStruct(InternedStr),
    UndefinedField(InternedStr, InternedStr),
    TypeError(&'static str)
}

type TcResult = Result<TcType, TypeError>;


fn find_type<'a>(module: &'a Module<TcIdent>, name: &InternedStr) -> Option<TcType> {
    module.functions.iter()
        .find(|f| f.name.id() == name)
        .map(|f| FunctionType(f.arguments.iter().map(|field| field.typ.clone()).collect(), box f.return_type.clone()))
        .or_else(|| module.structs.iter()
            .find(|s| s.name.id() == name)
            .map(|s| s.name.typ.clone())
        )
}

pub struct Typecheck<'a> {
    module: HashMap<InternedStr, TcType>,
    structs: HashMap<InternedStr, Vec<(InternedStr, TcType)>>,
    stack: ScopedMap<InternedStr, TcType>
}

impl <'a> Typecheck<'a> {
    
    pub fn new() -> Typecheck<'a> {
        Typecheck {
            module: HashMap::new(),
            structs: HashMap::new(),
            stack: ScopedMap::new()
        }
    }
    
    fn find(&self, id: &InternedStr) -> TcResult {
        self.stack.find(id)
            .or_else(|| self.module.find(id))
            .map(|t| t.clone())
            .map(Ok)
            .unwrap_or_else(|| Err(UndefinedVariable(id.clone())))
    }

    fn find_enum(&self, id: &InternedStr) -> Result<(), TypeError> {
        Ok(())
    }

    fn find_struct(&self, id: &InternedStr) -> Result<&Vec<(InternedStr, TcType)>, TypeError> {
        self.structs.find(id)
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(UndefinedStruct(id.clone())))
    }

    fn stack_var(&mut self, id: InternedStr, typ: TcType) {
        self.stack.insert(id, typ);
    }

    pub fn typecheck_module(&mut self, module: &mut Module<TcIdent>) -> Result<(), TypeError> {
        
        for f in module.functions.mut_iter() {
            f.name.typ = FunctionType(f.arguments.iter().map(|f| f.typ.clone()).collect(), box f.return_type.clone());
            self.module.insert(f.name.name, f.name.typ.clone());
        }
        for s in module.structs.mut_iter() {
            let fields = s.fields.iter().map(|f| (f.name, f.typ.clone())).collect();
            self.structs.insert(s.name.name, fields);

            let args = s.fields.iter().map(|f| f.typ.clone()).collect();
            s.name.typ = FunctionType(args, box Type(s.name.name));
            self.module.insert(s.name.name, s.name.typ.clone());
        }
        for e in module.enums.iter() {
            for ctor in e.constructors.iter() {
                let typ = FunctionType(ctor.arguments.clone(), box Type(e.name.name));
                self.module.insert(ctor.name.name, typ);
            }
        }
        for f in module.functions.mut_iter() {
            try!(self.typecheck_function(f));
        }
        Ok(())
    }

    fn typecheck_function(&mut self, function: &mut Function<TcIdent>) -> Result<(), TypeError> {
        self.stack.clear();
        for arg in function.arguments.iter() {
            self.stack_var(arg.name.clone(), arg.typ.clone());
        }
        let return_type = try!(self.typecheck(&mut function.expression));
        self.unify(&function.return_type, return_type)
            .map(|_| ())
    }

    fn typecheck(&mut self, expr: &mut Expr<TcIdent>) -> TcResult {
        match *expr {
            Identifier(ref mut id) => {
                id.typ = try!(self.find(id.id()));
                Ok(id.typ.clone())
            }
            Literal(ref lit) => {
                Ok(match *lit {
                    Integer(_) => int_type.clone(),
                    Float(_) => float_type.clone(),
                    String(_) => string_type.clone(),
                    Bool(_) => bool_type.clone()
                })
            }
            Call(ref mut func, ref mut args) => {
                let func_type = try!(self.typecheck(&mut**func));
                match func_type {
                    FunctionType(arg_types, return_type) => {
                        if arg_types.len() != args.len() {
                            return Err(WrongNumberOfArguments(arg_types.len(), args.len()));
                        }
                        for i in range(0, arg_types.len()) {
                            let actual = try!(self.typecheck(args.get_mut(i)));
                            try!(self.unify(&arg_types[i], actual));
                        }
                        Ok(*return_type)
                    }
                    t => Err(NotAFunction(t))
                }
            }
            IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut**pred));
                self.unify(&bool_type, pred_type);
                let true_type = try!(self.typecheck(&mut**if_true));
                let false_type = try!(self.typecheck(&mut**if_false));
                self.unify(&true_type, false_type)
            }
            While(ref mut pred, ref mut expr) => {
                let pred_type = try!(self.typecheck(&mut **pred));
                try!(self.unify(&bool_type, pred_type));
                self.typecheck(&mut**expr)
                    .map(|_| unit_type.clone())
            }
            BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut**lhs));
                let rhs_type = try!(self.typecheck(&mut**rhs));
                try!(self.unify(&lhs_type, rhs_type.clone()));
                match op.as_slice() {
                    "+" | "-" | "*" => {
                        if lhs_type == int_type || lhs_type == float_type {
                            Ok(lhs_type)
                        }
                        else {
                            return Err(TypeError("Expected numbers in binop"))
                        }
                    }
                    "<" | ">" | "<=" | ">=" => Ok(bool_type.clone()),
                    _ => Err(UndefinedVariable(op.name.clone()))
                }
            }
            Block(ref mut exprs) => {
                self.stack.enter_scope();
                let mut typ = unit_type.clone();
                for expr in exprs.mut_iter() {
                    typ = try!(self.typecheck(expr));
                }
                self.stack.exit_scope();
                Ok(typ)
            }
            Match(ref mut expr, ref mut alts) => {
                let typ = try!(self.typecheck(&mut**expr));
                self.stack.enter_scope();
                try!(self.typecheck_pattern(&mut alts.get_mut(0).pattern, typ.clone()));
                let alt1_type = try!(self.typecheck(&mut alts.get_mut(0).expression));
                self.stack.exit_scope();

                for alt in alts.mut_iter().skip(1) {
                    self.stack.enter_scope();
                    try!(self.typecheck_pattern(&alt.pattern, typ.clone()));
                    let alt_type = try!(self.typecheck(&mut alt.expression));
                    self.stack.exit_scope();
                    try!(self.unify(&alt1_type, alt_type));
                }
                Ok(alt1_type)
            }
            Let(ref mut id, ref mut expr) => {
                id.typ = try!(self.typecheck(&mut **expr));
                self.stack_var(id.name.clone(), id.typ.clone());
                Ok(unit_type.clone())
            }
            Assign(ref mut lhs, ref mut rhs) => {
                let rhs_type = try!(self.typecheck(&mut **rhs));
                let lhs_type = try!(self.typecheck(&mut **lhs));
                self.unify(&lhs_type, rhs_type)
            }
            FieldAccess(ref mut expr, ref mut id) => {
                let typ = try!(self.typecheck(&mut **expr));
                match typ {
                    Type(ref struct_id) => {
                        let fields = try!(self.find_struct(struct_id));
                        id.typ = try!(fields.iter()
                            .find(|& &(ref name, _)| *name == id.name)
                            .map(|&(_, ref t)| Ok(t.clone()))
                            .unwrap_or_else(|| Err(UndefinedField(struct_id.clone(), id.name.clone()))));
                        Ok(id.typ.clone())
                    }
                    FunctionType(..) => Err(TypeError("Field access on function")),
                    LiteralType(..) => Err(TypeError("Field acces on primitive"))
                }
            }
        }
    }

    fn typecheck_pattern(&mut self, pattern: &Pattern<TcIdent>, match_type: TcType) -> Result<(), TypeError> {
        match *pattern {
            ConstructorPattern(ref name, _) => {
                let ctor_type = try!(self.find(name.id()));
                match ctor_type {
                    FunctionType(_, ref return_type) => {
                        self.unify(&**return_type, match_type)
                            .map(|_| ())
                    }
                    _ => self.unify(&ctor_type, match_type)
                            .map(|_| ())
                }
            }
            IdentifierPattern(ref id) => {
                self.stack_var(id.id().clone(), match_type);
                Ok(())
            }
        }
    }

    fn unify(&self, expected: &TcType, actual: TcType) -> TcResult {
        if *expected == actual {
            Ok(actual)
        }
        else {
            Err(TypeMismatch(expected.clone(), actual))
        }
    }
}

pub trait Typed {
    fn type_of(&self) -> &Type<InternedStr>;
}
impl Typed for TcIdent {
    fn type_of(&self) -> &Type<InternedStr> {
        &self.typ
    }
}
impl <Id: Typed + Str> Typed for Expr<Id> {
    fn type_of(&self) -> &Type<InternedStr> {
        match *self {
            Identifier(ref id) => id.type_of(),
            Literal(ref lit) => {
                match *lit {
                    Integer(_) => &int_type,
                    Float(_) => &float_type,
                    String(_) => &string_type,
                    Bool(_) => &bool_type
                }
            }
            IfElse(_, ref arm, _) => arm.type_of(),
            Block(ref exprs) => {
                if exprs.len() == 0 {
                    &unit_type
                }
                else {
                    exprs.last().unwrap().type_of()
                }
            }
            BinOp(ref lhs, ref op, _) => {
                match op.as_slice() {
                    "+" | "-" | "*" => lhs.type_of(),
                    "<" | ">" | "<=" | ">=" => &bool_type,
                    _ => fail!()
                }
            }
            Let(..) | While(..) | Assign(..) => &unit_type,
            Call(ref func, _) => {
                match func.type_of() {
                    &FunctionType(_, ref return_type) => &**return_type,
                    _ => fail!()
                }
            }
            Match(_, ref alts) => alts[0].expression.type_of(),
            FieldAccess(_, ref id) => id.type_of()
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use super::TcIdent;
    use ast::*;
    use parser::*;
    use interner::InternedStr;

    pub fn parse<T>(s: &str, f: |&mut Parser<TcIdent>|:'static -> ParseResult<T>) -> T {
        use std::io::BufReader;
        let mut buffer = BufReader::new(s.as_bytes());
        let mut parser = Parser::new(&mut buffer, |s| TcIdent { typ: unit_type.clone(), name: s });
        f(&mut parser)
            .unwrap_or_else(|err| fail!(err))
    }

    #[test]
    fn while_() {
        let text = "fn main() { let x = 2; while x < 10 { x } }";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!(err))

    }
    #[test]
    fn enums() {
        let text = 
r"
enum AB {
    A(int),
    B(float)
}
fn main() -> int {
    match A(1) {
        A(x) => { x }
        B(x) => { 0 }
    }
}";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err))

    }
}
