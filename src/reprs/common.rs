use crate::newtype_derive;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Span<'i> {
    pub text: &'i str,
    pub start: usize,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ArgStructure {
    Tuple(Box<[ArgStructure]>),
    Var,
}

#[derive(Hash, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct EnumLabel<'i>(pub &'i str);

newtype_derive!([EnumLabel<'i>(&'i str)] Debug, Display);

/// de Bruijn index
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct Idx(usize);

impl Idx {
    pub fn get<'s, T>(&'_ self, stack: &'s [T]) -> Option<&'s T> {
        stack.iter().nth_back(self.0)
    }

    pub fn find<T>(stack: &[T], f: impl FnMut(&T) -> bool) -> Option<Self> {
        stack.iter().rev().position(f).map(Self)
    }
}
