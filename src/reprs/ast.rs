use crate::common::WithInfo;

pub type Term<'i> = WithInfo<Span<'i>, RawTerm<'i>>;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Span<'i> {
    pub text: &'i str,
    pub start: usize,
}

#[derive(Eq, PartialEq, Debug)]
pub enum RawTerm<'i> {
    Abs(Abs<'i>),
    App(App<'i>),

    Var(Var<'i>),

    Bool(bool),
}

#[derive(Eq, PartialEq, Debug)]
pub struct Abs<'i> {
    pub arg: Ident<'i>,
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
    pub ident: Ident<'i>,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Ident<'i> {
    pub name: &'i str,
}

pub type Type<'i> = WithInfo<Span<'i>, RawType<'i>>;

#[derive(Eq, PartialEq, Debug)]
pub enum RawType<'i> {
    Arr(Arr<'i>),

    Bool,
}

#[derive(Eq, PartialEq, Debug)]
pub struct Arr<'i> {
    pub arg: Box<Type<'i>>,
    pub result: Box<Type<'i>>,
}
