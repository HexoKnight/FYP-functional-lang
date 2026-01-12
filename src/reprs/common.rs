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
