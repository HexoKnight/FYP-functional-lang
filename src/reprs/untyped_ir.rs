use std::collections::HashMap;

use crate::{
    common::WithInfo,
    reprs::common::{ArgStructure, EnumLabel, Idx, Span},
};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs {
        arg_structure: ArgStructure,
        arg_type: Type<'i>,

        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,
        arg: Box<Term<'i>>,
    },

    Var(Idx),

    Enum(Type<'i>, EnumLabel<'i>),
    Match(Type<'i>, HashMap<EnumLabel<'i>, Term<'i>>),

    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}

pub type Type<'i> = WithInfo<Span<'i>, RawType<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawType<'i> {
    Arr {
        arg: Box<Type<'i>>,
        result: Box<Type<'i>>,
    },

    Tuple(Box<[Type<'i>]>),
    Enum(HashMap<EnumLabel<'i>, Type<'i>>),

    Bool,
    Never,
}
