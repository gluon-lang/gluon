pub use crate::base::types::{ArcType as RcType, Flags};

#[cfg(test)]
mod tests {
    use super::*;

    use crate::base::{
        symbol::Symbol,
        types::{Generic, Type, TypePtr as _},
    };

    #[test]
    fn flags() {
        let generic =
            Type::<_, RcType>::generic(Generic::new(Symbol::from("a"), Default::default()));
        assert_eq!(generic.flags(), Flags::HAS_GENERICS);
        assert_eq!(
            Type::function(vec![generic.clone()], generic.clone()).flags(),
            Flags::HAS_GENERICS
        );
    }
}
