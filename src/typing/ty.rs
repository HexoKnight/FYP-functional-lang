use itertools::Itertools;

use crate::{
    hashed_hashmap::HashedHashMap,
    reprs::common::{EnumLabel, Lvl},
    typing::{Context, TypeCheckError},
};

type TypeRef<'ctx> = &'ctx Type<'ctx>;

// TODO: manual Hash / *Eq impls for more complex types
// TODO: impl Display for nicer output
#[derive(Hash, Eq, PartialEq)]
pub enum Type<'ctx> {
    TyAbs {
        // disables some type interning but comparing type abstractions is uncommon and displaying
        // useful type information is more important
        name: &'ctx str,
        bounds: TyBounds<'ctx>,
        result: TypeRef<'ctx>,
    },

    TyVar(Lvl),

    Arr {
        arg: TypeRef<'ctx>,
        result: TypeRef<'ctx>,
    },

    Enum(HashedHashMap<EnumLabel<'ctx>, TypeRef<'ctx>>),
    Tuple(Box<[TypeRef<'ctx>]>),

    Bool,
    Any,
    Never,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub struct TyBounds<'ctx> {
    pub upper: Option<TypeRef<'ctx>>,
    pub lower: Option<TypeRef<'ctx>>,
}

impl<'ctx> Type<'ctx> {
    pub fn write_display(
        &self,
        ctx: &Context<'ctx, '_>,
        w: &mut String,
    ) -> Result<(), TypeCheckError> {
        match self {
            Type::TyAbs {
                name,
                bounds:
                    bounds @ TyBounds {
                        upper,
                        lower: bottom,
                    },
                result,
            } => {
                w.push('[');
                w.push_str(name);
                if let Some(upper) = upper {
                    w.push_str(" <");
                    upper.write_display(ctx, w)?;
                }
                if let Some(bottom) = bottom {
                    w.push_str(" >");
                    bottom.write_display(ctx, w)?;
                }
                w.push_str("] ");
                result.write_display(&ctx.push_ty_var(name, *bounds), w)?;
            }
            Type::TyVar(level) => {
                w.push_str(ctx.get_ty_var_unwrap(*level)?.0);
            }
            Type::Arr { arg, result } => {
                if matches!(arg, Type::TyAbs { .. } | Type::Arr { .. }) {
                    w.push('(');
                    arg.write_display(ctx, w)?;
                    w.push_str(") -> ");
                    result.write_display(ctx, w)?;
                } else {
                    arg.write_display(ctx, w)?;
                    w.push_str(" -> ");
                    result.write_display(ctx, w)?;
                }
            }
            Type::Enum(variants) => {
                w.push_str("enum {");
                let mut iter = variants.0.iter().sorted_unstable_by_key(|(l, _)| *l);
                if let Some((l, ty)) = iter.next() {
                    w.push_str(l.0);
                    w.push_str(": ");
                    ty.write_display(ctx, w)?;
                    for (l, ty) in iter {
                        w.push_str(", ");
                        w.push_str(l.0);
                        w.push_str(": ");
                        ty.write_display(ctx, w)?;
                    }
                }
                w.push('}');
            }
            Type::Tuple(elems) => {
                w.push('(');
                let mut iter = elems.iter();
                if let Some(first) = iter.next() {
                    first.write_display(ctx, w)?;
                    w.push(',');
                    if let Some(second) = iter.next() {
                        w.push(' ');
                        second.write_display(ctx, w)?;
                        for ty in iter {
                            w.push_str(", ");
                            ty.write_display(ctx, w)?;
                        }
                    }
                }
                w.push(')');
            }
            Type::Bool => w.push_str("bool"),
            Type::Any => w.push('_'),
            Type::Never => w.push('!'),
        }
        Ok(())
    }

    pub fn display(&self, ctx: &Context<'ctx, '_>) -> Result<String, TypeCheckError> {
        let mut string = String::new();
        self.write_display(ctx, &mut string)?;
        Ok(string)
    }
}
