use std::fmt::Debug;

pub struct WithInfo<I, T>(pub I, pub T);

impl<I, T: Debug> Debug for WithInfo<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.1.fmt(f)
    }
}
impl<I, T: Eq> Eq for WithInfo<I, T> {}
impl<I, T: PartialEq> PartialEq for WithInfo<I, T> {
    fn eq(&self, other: &Self) -> bool {
        self.1 == other.1
    }
}
