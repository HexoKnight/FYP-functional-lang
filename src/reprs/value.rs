use derive_where::derive_where;

use crate::{
    common::WithInfo,
    evaluation::ContextClosure,
    reprs::{ast::Span, typed_ir},
};

pub type Value<'i, Abs = ()> = WithInfo<Span<'i>, RawValue<Abs>>;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum RawValue<Abs> {
    Abs(Abs),

    Bool(bool),
}

#[derive(Clone)]
#[derive_where(Debug)]
pub struct Abs<'i, 'ir, 'a> {
    #[derive_where(skip)]
    pub closed_ctx: ContextClosure<'i, 'ir, 'a>,
    pub body: &'ir typed_ir::Term<'i>,
}

impl<'i, A> Value<'i, A> {
    pub fn map_abs<T>(self, mut f: impl FnMut(A) -> T) -> Value<'i, T> {
        WithInfo(
            self.0,
            match self.1 {
                RawValue::Abs(a) => RawValue::Abs(f(a)),
                RawValue::Bool(b) => RawValue::Bool(b),
            },
        )
    }
}
