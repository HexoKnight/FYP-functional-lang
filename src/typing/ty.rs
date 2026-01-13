use crate::hashed_hashmap::HashedHashMap;

type TypeRef<'ctx> = &'ctx Type<'ctx>;

// TODO: manual Hash / *Eq impls for more complex types
// TODO: impl Display for nicer output
#[derive(Hash, Eq, PartialEq, Debug)]
pub enum Type<'ctx> {
    Arr {
        arg: TypeRef<'ctx>,
        result: TypeRef<'ctx>,
    },

    Enum(HashedHashMap<&'ctx str, TypeRef<'ctx>>),
    Tuple(Box<[TypeRef<'ctx>]>),

    Bool,
}
