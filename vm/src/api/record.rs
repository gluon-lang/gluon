use std::any::Any;

use frunk_core::hlist::{h_cons, HCons, HList, HNil};

use crate::base::{
    symbol::Symbol,
    types::{self, Alias, AliasData, ArcType, Type},
};

use super::{ActiveThread, Getable, Pushable, ValueRef, VmType};

use crate::{interner::InternedStr, value::Value, vm::Thread, Result, Variants};

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
    fn vm_push(
        self,
        context: &mut ActiveThread<'vm>,
        field_names: &mut Vec<InternedStr>,
    ) -> Result<()>;
}

pub trait GetableFieldList<'vm, 'value>: HList + Sized {
    fn from_value(vm: &'vm Thread, values: &'value [Value]) -> Option<Self>;
}

impl<'vm> PushableFieldList<'vm> for HNil {
    fn vm_push(self, _: &mut ActiveThread, _: &mut Vec<InternedStr>) -> Result<()> {
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

        let args = F::args();

        let alias_name = Symbol::from(F::name().replace("::", "."));
        let field_name = Symbol::from(alias_name.declared_name());

        let mut rhs_is_equivalent = None;
        {
            let (f, a) = if let Type::App(f, a) = &*typ {
                (f, &a[..])
            } else {
                (&typ, &[][..])
            };
            if let Type::Alias(f) = &**f {
                if f.name.declared_name() == field_name.declared_name()
                    && args.len() == a.len()
                    && args.iter().zip(a).all(|(l, r)| match &**r {
                        Type::Generic(gen) => *l == gen.id.declared_name(),
                        _ => false,
                    })
                {
                    rhs_is_equivalent = Some(Alias::from(f.clone()));
                }
            }
        }

        let alias = rhs_is_equivalent.unwrap_or_else(|| {
            let alias_name = {
                let mut self_symbol = None;
                types::walk_type(&typ, |typ: &ArcType| {
                    if self_symbol.is_none() {
                        match **typ {
                            Type::Ident(ref id)
                                if id.name.declared_name() == field_name.declared_name() =>
                            {
                                self_symbol = Some(id.name.clone())
                            }
                            _ => (),
                        }
                    }
                });
                self_symbol.unwrap_or_else(|| alias_name)
            };
            assert!(
                field_name.declared_name().starts_with(char::is_uppercase),
                "Types `{}` does not start with an uppercase letter",
                field_name
            );
            Alias::from(AliasData::new(
                alias_name,
                args.iter()
                    .map(|arg| match *vm.global_env().get_generic(*arg) {
                        Type::Generic(ref gen) => gen.clone(),
                        _ => unreachable!(),
                    })
                    .collect(),
                typ,
            ))
        });

        type_fields.push(types::Field::new(field_name, alias));
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
    fn vm_push(
        self,
        context: &mut ActiveThread<'vm>,
        field_names: &mut Vec<InternedStr>,
    ) -> Result<()> {
        let ((_, head), tail) = self.pluck();
        field_names.push(context.thread().global_env().intern(F::name())?);
        head.vm_push(context)?;
        tail.vm_push(context, field_names)
    }
}

impl<'vm, 'value, F, H, T> GetableFieldList<'vm, 'value> for HCons<(F, H), T>
where
    F: Field,
    H: Getable<'vm, 'value> + VmType,
    T: GetableFieldList<'vm, 'value>,
{
    fn from_value(vm: &'vm Thread, values: &'value [Value]) -> Option<Self> {
        let head = H::from_value(vm, Variants::new(&values[0]));
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
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let mut field_names = Vec::new();
        self.fields.vm_push(context, &mut field_names)?;

        let mut context = context.context();

        context.push_new_record(U::LEN, &field_names)?;
        Ok(())
    }
}
impl<'vm, 'value, T, U> Getable<'vm, 'value> for Record<T, U>
where
    T: Default,
    U: GetableFieldList<'vm, 'value>,
{
    impl_getable_simple!();

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

pub struct Row<T, U, R> {
    pub type_fields: T,
    pub fields: U,
    pub rest: R,
}

impl<T: FieldTypes, U: FieldValues, R: VmType> VmType for Row<T, U, R> {
    type Type = Record<T::Type, U::Type>;
    fn make_type(vm: &Thread) -> ArcType {
        let mut type_fields = Vec::new();
        T::field_types(vm, &mut type_fields);
        let mut fields = Vec::new();
        U::field_values(vm, &mut fields);
        Type::extend_full_row(type_fields, fields, R::make_type(vm))
    }
}

pub struct EmptyRow;

impl VmType for EmptyRow {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        let type_cache = vm.global_env().type_cache();
        type_cache.empty_row()
    }
}
