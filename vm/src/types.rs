use std::collections::HashMap;
use std::rc::Rc;
use base::ast;
use base::symbol::Symbol;
use check::kindcheck::KindEnv;
use check::typecheck::{TypeEnv, TcType, Type};

pub use self::Instruction::*;

pub type VMIndex = u32;
pub type VMTag = u32;

#[derive(Copy, Clone, Debug)]
pub enum Instruction {
    PushInt(isize),
    PushFloat(f64),
    PushString(VMIndex),
    Push(VMIndex),
    PushGlobal(VMIndex),
    Call(VMIndex),
    TailCall(VMIndex),
    Construct(VMIndex, VMIndex),
    GetField(VMIndex),
    Split,
    TestTag(VMTag),
    Jump(VMIndex),
    CJump(VMIndex),
    Pop(VMIndex),
    Slide(VMIndex),

    // Creates a closure with 'n' upvariables
    // Pops the 'n' values on top of the stack and creates a closure
    MakeClosure(VMIndex, VMIndex),
    // Creates a closure but does not fill its environment
    NewClosure(VMIndex, VMIndex),
    // Fills the previously allocated closure with `n` upvariables
    CloseClosure(VMIndex),
    PushUpVar(VMIndex),

    GetIndex,
    SetIndex,

    AddInt,
    SubtractInt,
    MultiplyInt,
    IntLT,
    IntEQ,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    FloatLT,
    FloatEQ,
}


impl Instruction {
    pub fn adjust(&self) -> i32 {
        match *self {
            PushInt(_) | PushFloat(_) | PushString(_) | Push(_) | PushGlobal(_) => 1,
            Call(n) => -(n as i32),
            TailCall(n) => -(n as i32),
            Construct(_, n) => 1 - n as i32,
            GetField(_) => 0,
            // The number of added stack slots are handled separately as the type is needed to
            // calculate the number of slots needed
            Split => -1,
            TestTag(_) => 1,
            Jump(_) => 0,
            CJump(_) => -1,
            Pop(n) => -(n as i32),
            Slide(n) => -(n as i32),
            MakeClosure(_, _) => 1,
            NewClosure(_, _) => 1,
            CloseClosure(_) => -1,
            PushUpVar(_) => 1,
            GetIndex => 0,
            SetIndex => -1,
            AddInt |
            SubtractInt |
            MultiplyInt |
            IntLT |
            IntEQ |
            AddFloat |
            SubtractFloat |
            MultiplyFloat |
            FloatLT |
            FloatEQ => -1,
        }
    }
}

#[derive(Debug)]
pub struct TypeInfos {
    pub id_to_type: HashMap<Symbol, (Vec<ast::Generic<Symbol>>, TcType)>,
    pub type_to_id: HashMap<TcType, TcType>,
}

impl KindEnv for TypeInfos {
    fn find_kind(&self, type_name: Symbol) -> Option<Rc<ast::Kind>> {
        self.id_to_type
            .get(&type_name)
            .and_then(|tup| self.type_to_id.get(&tup.1))
            .map(|typ| typ.kind())
    }
}

impl TypeEnv for TypeInfos {
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
        self.id_to_type
            .iter()
            .filter_map(|(_, &(_, ref typ))| {
                match **typ {
                    Type::Variants(ref variants) => variants.iter().find(|v| v.0 == *id),
                    _ => None,
                }
            })
            .next()
            .map(|x| &x.1)
    }

    fn find_type_info(&self, id: &Symbol) -> Option<(&[ast::Generic<Symbol>], Option<&TcType>)> {
        self.id_to_type
            .get(id)
            .map(|&(ref args, ref typ)| (&args[..], Some(typ)))
    }
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        self.id_to_type
            .iter()
            .find(|&(_, &(_, ref typ))| {
                match **typ {
                    Type::Record { fields: ref record_fields, .. } => {
                        fields.iter().all(|&name| record_fields.iter().any(|f| f.name == name))
                    }
                    _ => false,
                }
            })
            .and_then(|t| self.type_to_id.get(&(t.1).1).map(|id_type| (id_type, &(t.1).1)))
    }
}

impl TypeInfos {
    pub fn new() -> TypeInfos {
        TypeInfos {
            id_to_type: HashMap::new(),
            type_to_id: HashMap::new(),
        }
    }

    pub fn extend(&mut self, other: TypeInfos) {
        let TypeInfos { id_to_type, type_to_id } = other;
        self.id_to_type.extend(id_to_type);
        self.type_to_id.extend(type_to_id);
    }
}
