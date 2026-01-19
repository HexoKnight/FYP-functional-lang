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
        body: Box<Term<'i>>,
    },
    App {
        func: Box<Term<'i>>,
        arg: Box<Term<'i>>,
    },

    Var(Idx),

    Enum(EnumLabel<'i>),
    Match(HashMap<EnumLabel<'i>, Term<'i>>),

    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}
