use itertools::Itertools;

use crate::hashed_hashmap::HashedHashMap;

type TypeRef<'ctx> = &'ctx Type<'ctx>;

// TODO: manual Hash / *Eq impls for more complex types
// TODO: impl Display for nicer output
#[derive(Hash, Eq, PartialEq)]
pub enum Type<'ctx> {
    Arr {
        arg: TypeRef<'ctx>,
        result: TypeRef<'ctx>,
    },

    Enum(HashedHashMap<&'ctx str, TypeRef<'ctx>>),
    Tuple(Box<[TypeRef<'ctx>]>),

    Bool,
    Never,
}

impl Type<'_> {
    // TODO(type aliases): pass in alias info
    pub fn write_display(&self, w: &mut impl std::fmt::Write) -> std::fmt::Result {
        match self {
            Type::Arr { arg, result } => {
                if matches!(arg, Type::Arr { .. }) {
                    w.write_str("(")?;
                    arg.write_display(w)?;
                    w.write_str(") -> ")?;
                    result.write_display(w)
                } else {
                    arg.write_display(w)?;
                    w.write_str(" -> ")?;
                    result.write_display(w)
                }
            }
            Type::Enum(variants) => {
                w.write_str("enum {")?;
                let mut iter = variants.0.iter().sorted_unstable_by_key(|(l, _)| *l);
                if let Some((l, ty)) = iter.next() {
                    w.write_str(l)?;
                    w.write_str(": ")?;
                    ty.write_display(w)?;
                    for (l, ty) in iter {
                        w.write_str(", ")?;
                        w.write_str(l)?;
                        w.write_str(": ")?;
                        ty.write_display(w)?;
                    }
                }
                w.write_str("}")
            }
            Type::Tuple(elems) => {
                w.write_str("(")?;
                let mut iter = elems.iter();
                if let Some(first) = iter.next() {
                    first.write_display(w)?;
                    w.write_str(",")?;
                    if let Some(second) = iter.next() {
                        w.write_str(" ")?;
                        second.write_display(w)?;
                        for ty in iter {
                            w.write_str(", ")?;
                            ty.write_display(w)?;
                        }
                    }
                }
                w.write_str(")")
            }
            Type::Bool => w.write_str("bool"),
            Type::Never => w.write_str("!"),
        }
    }

    pub fn display(&self) -> String {
        let mut string = String::new();
        self.write_display(&mut string)
            .expect("writing to a string buffer should be infallible");
        string
    }
}
