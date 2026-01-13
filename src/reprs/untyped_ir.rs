use std::collections::HashMap;

use crate::{
    common::WithInfo,
    reprs::common::{ArgStructure, Span},
};

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs(Abs<'i>),
    App(App<'i>),

    Var(Var<'i>),

    Tuple(Box<[Term<'i>]>),

    Bool(bool),
}

#[derive(Eq, PartialEq, Debug)]
pub struct Abs<'i> {
    pub arg_structure: ArgStructure,
    pub arg_type: Type<'i>,

    pub body: Box<Term<'i>>,
}

#[derive(Eq, PartialEq, Debug)]
pub struct App<'i> {
    pub func: Box<Term<'i>>,
    pub arg: Box<Term<'i>>,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Var<'i> {
    pub name: &'i str,
    pub index: usize,
}

pub type Type<'i> = WithInfo<Span<'i>, RawType<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawType<'i> {
    Arr(Arr<'i>),

    Tuple(Box<[Type<'i>]>),
    Enum(HashMap<&'i str, Type<'i>>),

    Bool,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Arr<'i> {
    pub arg: Box<Type<'i>>,
    pub result: Box<Type<'i>>,
}
