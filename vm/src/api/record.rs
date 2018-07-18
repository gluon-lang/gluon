use std::any::Any;

use frunk_core::hlist::{h_cons, HCons, HList, HNil};

use base::symbol::Symbol;
use base::types::{self, Alias, AliasData, ArcType, Generic, Type};

use super::{ActiveThread, Getable, Pushable, ValueRef, VmType};
use thread;
use types::VmIndex;
use value::{Def, Value, ValueRepr};
use vm::Thread;
use {Result, Variants};

pub struct Record<T, U> {
    pub type_fields: T,
    pub fields: U,
}

pub trait Field: Default {
    fn name() -> &'static str;
    fn args() -> &'static [&'static str] {
        &[]
    }
}

pub trait FieldTypes: HList {
    type Type: Any;
    fn field_types(
        vm: &Thread,
        type_fields: &mut Vec<types::Field<Symbol, Alias<Symbol, ArcType>>>,
    );
}

pub trait FieldValues: HList {
    type Type: Any;
    fn field_values(vm: &Thread, fields: &mut Vec<types::Field<Symbol, ArcType>>);
}

pub trait PushableFieldList<'vm>: HList {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()>;
}

pub trait GetableFieldList<'vm, 'value>: HList + Sized {
    fn from_value(vm: &'vm Thread, values: &'value [Value]) -> Option<Self>;
}

impl<'vm> PushableFieldList<'vm> for HNil {
    fn push(self, _: &mut ActiveThread) -> Result<()> {
        Ok(())
    }
}

impl<'vm, 'value> GetableFieldList<'vm, 'value> for HNil {
    fn from_value(_vm: &'vm Thread, values: &'value [Value]) -> Option<Self> {
        debug_assert!(values.is_empty(), "Retrieving type {:?}", values);
        Some(HNil)
    }
}

impl FieldTypes for HNil {
    type Type = ();
    fn field_types(_: &Thread, _: &mut Vec<types::Field<Symbol, Alias<Symbol, ArcType>>>) {}
}

impl<F: Field, H: VmType, T> FieldTypes for HCons<(F, H), T>
where
    T: FieldTypes,
    H::Type: Sized,
{
    type Type = HCons<(&'static str, H::Type), T::Type>;
    fn field_types(
        vm: &Thread,
        type_fields: &mut Vec<types::Field<Symbol, Alias<Symbol, ArcType>>>,
    ) {
        let typ = H::make_type(vm);
        let name = {
            let mut self_symbol = None;
            types::walk_type(&typ, |typ: &ArcType| {
                if self_symbol.is_none() {
                    match **typ {
                        Type::Ident(ref id) if id.definition_name() == F::name() => {
                            self_symbol = Some(id.clone())
                        }
                        _ => (),
                    }
                }
            });
            self_symbol.unwrap_or_else(|| Symbol::from(F::name()))
        };
        let args = F::args();
        assert!(
            name.definition_name().starts_with(char::is_uppercase),
            "{}",
            name
        );
        type_fields.push(types::Field::new(
            name.clone(),
            Alias::from(AliasData::new(
                name,
                args.iter()
                    .map(|arg| {
                        Generic::new(
                            Symbol::from(*arg),
                            vm.global_env().type_cache().kind_cache.typ(),
                        )
                    })
                    .collect(),
                typ,
            )),
        ));
        T::field_types(vm, type_fields);
    }
}

impl FieldValues for HNil {
    type Type = ();
    fn field_values(_: &Thread, _: &mut Vec<types::Field<Symbol, ArcType>>) {}
}

impl<F: Field, H: VmType, T> FieldValues for HCons<(F, H), T>
where
    T: FieldValues,
    H::Type: Sized,
{
    type Type = HCons<(&'static str, H::Type), T::Type>;
    fn field_values(vm: &Thread, fields: &mut Vec<types::Field<Symbol, ArcType>>) {
        let name = Symbol::from(F::name());
        let args = F::args();
        debug_assert!(args.is_empty());
        fields.push(types::Field::new(name, H::make_type(vm)));
        T::field_values(vm, fields);
    }
}

impl<'vm, F: Field, H: Pushable<'vm>, T> PushableFieldList<'vm> for HCons<(F, H), T>
where
    T: PushableFieldList<'vm>,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let ((_, head), tail) = self.pluck();
        head.push(context)?;
        tail.push(context)
    }
}

impl<'vm, 'value, F, H, T> GetableFieldList<'vm, 'value> for HCons<(F, H), T>
where
    F: Field,
    H: Getable<'vm, 'value> + VmType,
    T: GetableFieldList<'vm, 'value>,
{
    fn from_value(vm: &'vm Thread, values: &'value [Value]) -> Option<Self> {
        let head = unsafe { H::from_value(vm, Variants::new(&values[0])) };
        T::from_value(vm, &values[1..]).map(move |tail| h_cons((F::default(), head), tail))
    }
}

impl<T: FieldTypes, U: FieldValues> VmType for Record<T, U> {
    type Type = Record<T::Type, U::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let mut type_fields = Vec::new();
        T::field_types(vm, &mut type_fields);
        let mut fields = Vec::new();
        U::field_values(vm, &mut fields);
        let type_cache = vm.global_env().type_cache();
        type_cache.record(type_fields, fields)
    }
}
impl<'vm, T, U> Pushable<'vm> for Record<T, U>
where
    U: PushableFieldList<'vm>,
{
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let thread = context.thread();
        self.fields.push(context)?;
        let context = context.context();
        let len = U::LEN as VmIndex;
        let offset = context.stack.len() - len;
        let value = thread::alloc(
            &mut context.gc,
            thread,
            &context.stack,
            Def {
                tag: 0,
                elems: &context.stack[offset..],
            },
        )?;
        for _ in 0..len {
            context.stack.pop();
        }
        context.stack.push(ValueRepr::Data(value));
        Ok(())
    }
}
impl<'vm, 'value, T, U> Getable<'vm, 'value> for Record<T, U>
where
    T: Default,
    U: GetableFieldList<'vm, 'value>,
{
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::Data(ref data) => {
                let fields = U::from_value(vm, data.fields()).unwrap();
                Record {
                    type_fields: T::default(),
                    fields,
                }
            }
            _ => ice!("Value is not a Record"),
        }
    }
}
