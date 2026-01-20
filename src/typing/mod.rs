use std::collections::HashMap;

use itertools::{Itertools, zip_eq};
use typed_arena::Arena;

use crate::common::WithInfo;
use crate::reprs::common::{ArgStructure, Lvl};
use crate::reprs::{
    typed_ir::{self as tir},
    untyped_ir as uir,
};
use crate::typing::ty::TyBounds;

use self::context::{Context, ContextInner};
use self::ty::Type;

mod ty;

mod context {
    use typed_arena::Arena;

    use crate::{
        intern::InternedArena,
        reprs::common::{Idx, Lvl},
        typing::ty::TyBounds,
    };

    use super::{InternedType, TypeCheckError, ty::Type};

    // doesn't suffer from the same dropck issues as self references
    // do not (currently) pass through this type
    /// Cheaply cloneable (hopefully) append-only stack
    type Stack<T> = Vec<T>;

    pub(super) struct ContextInner<'a> {
        ty_arena: InternedArena<'a, Type<'a>>,
    }
    impl<'a> ContextInner<'a> {
        pub(super) fn new(arena: &'a Arena<Type<'a>>) -> Self {
            Self {
                ty_arena: InternedArena::with_arena(arena),
            }
        }

        fn intern(&self, var: Type<'a>) -> InternedType<'a> {
            self.ty_arena.intern(var)
        }
    }

    #[must_use]
    #[derive(Clone)]
    pub(super) struct Context<'a, 'inn> {
        inner: &'inn ContextInner<'a>,
        var_ty_stack: Stack<InternedType<'a>>,
        ty_var_stack: Stack<(&'a str, TyBounds<'a>)>,
    }

    impl<'a, 'inn> Context<'a, 'inn> {
        pub(super) fn with_inner(inner: &'inn ContextInner<'a>) -> Self {
            Self {
                inner,
                var_ty_stack: Vec::new(),
                ty_var_stack: Vec::new(),
            }
        }

        pub(super) fn intern<'s>(&'s self, var: Type<'a>) -> InternedType<'a> {
            self.inner.intern(var)
        }

        pub(super) fn push_var_tys(
            &self,
            vars: impl IntoIterator<Item = InternedType<'a>>,
        ) -> Self {
            let mut new = self.clone();
            new.var_ty_stack.extend(vars);
            new
        }

        pub(super) fn get_var_ty(&self, index: Idx) -> Option<&'a Type<'a>> {
            index.get(&self.var_ty_stack).copied()
        }

        pub(super) fn push_ty_var(&self, ty_var_name: &'a str, ty_var: TyBounds<'a>) -> Self {
            let mut new = self.clone();
            new.ty_var_stack.push((ty_var_name, ty_var));
            new
        }

        pub(super) fn get_ty_var(&self, level: Lvl) -> Option<(&'a str, TyBounds<'a>)> {
            level.get(&self.ty_var_stack).copied()
        }

        pub(super) fn get_ty_var_unwrap(
            &self,
            level: Lvl,
        ) -> Result<(&'a str, TyBounds<'a>), TypeCheckError> {
            self.get_ty_var(level)
                .ok_or_else(|| format!("illegal failure: type variable level not found: {level:?}"))
        }

        pub(super) fn next_ty_var_level(&self) -> Lvl {
            Lvl::get_depth(&self.ty_var_stack)
        }
    }
}

type InternedType<'a> = &'a Type<'a>;

pub type TypeCheckError = String;

trait TypeCheck<'i, 'a> {
    type TypeChecked;

    fn type_check(
        &self,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError>;
}

pub fn type_check<'i>(
    untyped_ir: &uir::Term<'i>,
) -> Result<(tir::Term<'i>, String), TypeCheckError> {
    let arena = Arena::new();
    let inner = ContextInner::new(&arena);
    let ctx = Context::with_inner(&inner);

    let (term, ty) = untyped_ir.type_check(&ctx)?;
    Ok((term, ty.display(&ctx)?))
}

impl<'i, 'a, T: TypeCheck<'i, 'a>> TypeCheck<'i, 'a> for Box<T> {
    type TypeChecked = Box<T::TypeChecked>;

    fn type_check(
        &self,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
        T::type_check(self, ctx).map(|(term, ty)| (Box::new(term), ty))
    }
}

impl<'i: 'a, 'a> TypeCheck<'i, 'a> for uir::Term<'i> {
    type TypeChecked = tir::Term<'i>;

    fn type_check(
        &self,
        ctx: &Context<'a, '_>,
    ) -> Result<(Self::TypeChecked, InternedType<'a>), TypeCheckError> {
        let WithInfo(info, term) = self;

        let (term, ty) = match term {
            uir::RawTerm::Abs {
                arg_structure,
                arg_type,
                body,
            } => {
                let arg_type = arg_type.eval(ctx)?;
                let destructured_arg_types = arg_type.destructure(arg_structure, ctx)?;

                let ctx_ = ctx.push_var_tys(destructured_arg_types);
                let (body, body_type) = body.type_check(&ctx_)?;

                let ty = Type::Arr {
                    arg: arg_type,
                    result: body_type,
                };

                (
                    tir::RawTerm::Abs {
                        arg_structure: arg_structure.clone(),
                        body,
                    },
                    ctx.intern(ty),
                )
            }
            uir::RawTerm::App { func, arg } => {
                let (func, func_type) = func.type_check(ctx)?;
                let (arg, arg_type) = arg.type_check(ctx)?;

                let func_result_type = func_type.get_function_result_type(ctx)?;
                check_subtype(
                    ctx.intern(Type::Arr {
                        arg: arg_type,
                        result: ctx.intern(Type::Any),
                    }),
                    func_type,
                    ctx,
                )
                .map_err(|mut e| {
                    e.insert_str(0, "error typing function application:\n");
                    e
                })?;
                (tir::RawTerm::App { func, arg }, func_result_type)
            }
            uir::RawTerm::TyAbs { name, bounds, body } => {
                let bounds = bounds.eval(ctx)?;

                let ctx_ = ctx.push_ty_var(name, bounds);
                let (body, body_type) = body.type_check(&ctx_)?;

                let WithInfo(_info, body) = *body;

                (
                    body,
                    ctx.intern(Type::TyAbs {
                        name,
                        bounds,
                        result: body_type,
                    }),
                )
            }
            uir::RawTerm::TyApp { abs, arg } => {
                let (abs, abs_type) = abs.type_check(ctx)?;
                let WithInfo(_info, abs) = *abs;

                let arg = arg.eval(ctx)?;
                let Type::TyAbs {
                    name: _,
                    bounds,
                    result,
                } = abs_type
                else {
                    // TODO
                    return Err(format!(
                        "cannot apply a type argument to type: {abs_type}",
                        abs_type = abs_type.display(ctx)?
                    ));
                };
                if let Some(upper) = bounds.upper {
                    check_subtype(upper, arg, ctx)
                        .map_err(prepend(|| "unsatisfied type arg upper bound:\n"))?;
                }
                if let Some(lower) = bounds.lower {
                    check_subtype(arg, lower, ctx)
                        .map_err(prepend(|| "unsatisfied type arg lower bound:\n"))?;
                }
                let ty = result.substitute_ty_var(arg, ctx);
                (abs, ty)
            }
            uir::RawTerm::Var(index) => (
                tir::RawTerm::Var(*index),
                ctx.get_var_ty(*index).ok_or_else(|| {
                    format!("illegal failure: variable index not found: {index:?}\n")
                })?,
            ),
            uir::RawTerm::Enum(enum_type, label) => {
                let enum_type = enum_type.eval(ctx)?;

                let Type::Enum(variants) = enum_type else {
                    // TODO
                    return Err(format!(
                        "cannot construct an enum with a non-enum type: {enum_type}",
                        enum_type = enum_type.display(ctx)?
                    ));
                };
                let Some(variant_type) = variants.0.get(label) else {
                    // TODO
                    return Err(format!(
                        "enum type does not contain label '{label}': {enum_type}",
                        enum_type = enum_type.display(ctx)?
                    ));
                };
                (
                    tir::RawTerm::Enum(*label),
                    ctx.intern(Type::Arr {
                        arg: variant_type,
                        result: enum_type,
                    }),
                )
            }
            uir::RawTerm::Match(enum_type, arms) => {
                let enum_type = enum_type.eval(ctx)?;
                let Type::Enum(variants) = enum_type else {
                    // TODO
                    return Err(format!(
                        "cannot match on a non-enum type: {enum_type}",
                        enum_type = enum_type.display(ctx)?
                    ));
                };

                let (arms, result_types): (HashMap<_, _>, Vec<_>) = arms
                    .iter()
                    .map(|(label, func)| -> Result<_, TypeCheckError> {
                        let (func, func_type) = func.type_check(ctx)?;
                        // check dead branches
                        let Some(variant_type) = variants.0.get(label) else {
                            // TODO
                            return Err(format!(
                                "enum type does not contain label '{label}': {enum_type}",
                                enum_type = enum_type.display(ctx)?
                            ));
                        };
                        let Type::Arr {
                            arg: func_arg_type,
                            result: func_result_type,
                        } = func_type
                        else {
                            // TODO
                            return Err(format!(
                                "match arm must be a function type: {func_type}",
                                func_type = func_type.display(ctx)?
                            ));
                        };
                        check_subtype(func_arg_type, variant_type, ctx)
                            .map_err(prepend(|| "incorrect match arm type:\n"))?;
                        Ok(Some(((*label, func), *func_result_type)))
                    })
                    .filter_map_ok(|o| o)
                    .try_collect()?;

                variants.0.iter().try_for_each(|(label, _)| {
                    if arms.contains_key(label) {
                        Ok(())
                    } else {
                        // TODO
                        Err(format!("match missing arm with label '{label}'"))
                    }
                })?;
                (
                    tir::RawTerm::Match(arms),
                    ctx.intern(Type::Arr {
                        arg: enum_type,
                        result: Type::join(result_types, ctx)?,
                    }),
                )
            }
            uir::RawTerm::Tuple(elems) => {
                let (elems, types): (Vec<_>, Vec<_>) =
                    elems.iter().map(|e| e.type_check(ctx)).try_collect()?;
                (
                    tir::RawTerm::Tuple(elems.into_boxed_slice()),
                    ctx.intern(Type::Tuple(types.into_boxed_slice())),
                )
            }
            uir::RawTerm::Bool(b) => (tir::RawTerm::Bool(*b), ctx.intern(Type::Bool)),
        };

        Ok((WithInfo(*info, term), ty))
    }
}

impl<'i: 'a, 'a> uir::Type<'i> {
    fn eval(&self, ctx: &Context<'a, '_>) -> Result<InternedType<'a>, TypeCheckError> {
        let WithInfo(_info, ty) = self;

        let ty = match ty {
            uir::RawType::TyAbs {
                name,
                bounds,
                result,
            } => {
                let bounds = bounds.eval(ctx)?;
                Type::TyAbs {
                    name,
                    bounds,
                    // ty_vars are not currently used so this is useless but may as well push it if
                    // only for future correctness
                    result: result.eval(&ctx.push_ty_var(name, bounds))?,
                }
            }
            uir::RawType::TyVar(level) => Type::TyVar(*level),
            uir::RawType::Arr { arg, result } => {
                let arg = arg.as_ref().eval(ctx)?;
                let result = result.as_ref().eval(ctx)?;
                Type::Arr { arg, result }
            }
            uir::RawType::Tuple(elems) => {
                Type::Tuple(elems.iter().map(|e| e.eval(ctx)).try_collect()?)
            }
            uir::RawType::Enum(variants) => Type::Enum(
                variants
                    .iter()
                    .map(|(l, t)| t.eval(ctx).map(|t| (*l, t)))
                    .try_collect()?,
            ),
            uir::RawType::Bool => Type::Bool,
            uir::RawType::Any => Type::Any,
            uir::RawType::Never => Type::Never,
        };

        Ok(ctx.intern(ty))
    }
}

impl<'i: 'a, 'a> uir::TyBounds<'i> {
    fn eval(&self, ctx: &Context<'a, '_>) -> Result<TyBounds<'a>, TypeCheckError> {
        let uir::TyBounds { upper, lower } = self;
        let upper = upper.as_ref().map(|ty| ty.eval(ctx)).transpose()?;
        let lower = lower.as_ref().map(|ty| ty.eval(ctx)).transpose()?;
        if let (Some(upper), Some(lower)) = (upper, lower) {
            check_subtype(upper, lower, ctx).map_err(prepend(
                || "type bound error: upper bound must be supertype of lower bound",
            ))?;
        }
        Ok(TyBounds { upper, lower })
    }
}

// TODO: improve error messages by specifying which type is 'expected'
/// # Errors
/// returns Err when not subtype
fn check_subtype<'a>(
    supertype: InternedType<'a>,
    subtype: InternedType<'a>,
    ctx: &Context<'a, '_>,
) -> Result<(), TypeCheckError> {
    if ty_eq(supertype, subtype) {
        return Ok(());
    }

    match (supertype, subtype) {
        (
            Type::TyAbs {
                name: name_super,
                bounds: bounds_super,
                result: supertype,
            },
            Type::TyAbs {
                name: name_sub,
                bounds: bounds_sub,
                result: subtype,
            },
        ) => {
            // subtype bounds must enclose supertype bounds
            if let Some(upper_sub) = bounds_sub.upper {
                let upper_super = bounds_super.upper.unwrap_or_else(|| ctx.intern(Type::Any));
                check_subtype(upper_sub, upper_super, ctx)
            } else {
                Ok(())
            }
            .map_err(prepend(|| {
                "subtype upper bound must be a supertype of supertype upper bound".to_string()
            }))
            .and_then(|()| {
                if let Some(lower_sub) = bounds_sub.lower {
                    let lower_super = bounds_super
                        .lower
                        .unwrap_or_else(|| ctx.intern(Type::Never));
                    check_subtype(lower_super, lower_sub, ctx)
                } else {
                    Ok(())
                }
                .map_err(prepend(|| {
                    "subtype lower bound must be a subtype of supertype lower bound".to_string()
                }))
            })
            .map_err(prepend(|| {
                "bounds of subtype type arg must enclose those of the supertype type arg:"
                    .to_string()
            }))
            .and_then(|()| check_subtype(supertype, subtype, &ctx.push_ty_var(std::cmp::min(name_super, name_sub), *bounds_super)))
        }
        (
            Type::TyAbs {
                name,
                bounds,
                result: supertype,
            },
            subtype,
        ) => check_subtype(supertype, subtype, &ctx.push_ty_var(name, *bounds)),
        (
            supertype,
            Type::TyAbs {
                name,
                bounds,
                result: subtype,
            },
        ) => check_subtype(supertype, subtype, &ctx.push_ty_var(name, *bounds)),
        // covered by ty_eq above but included regardless
        (Type::TyVar(level_super), Type::TyVar(level_sub)) if level_super == level_sub => Ok(()),
        (Type::TyVar(level), subtype) => {
            // if the lower bound doesn't exist (ie. it is unbounded below), it is equivalent to
            // having a lower bound of the bottom type
            let (_, supertype_bounds) = ctx.get_ty_var_unwrap(*level)?;
            let lower = supertype_bounds
                .lower
                .unwrap_or_else(|| ctx.intern(Type::Never));
            // a type is guaranteed to be a subtype of the instantiated type iff it is a
            // subtype of the lower bound (due to the transitivity of subtyping)
            check_subtype(lower, subtype, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "subtyping must be guaranteed for all possible instantiations of type var: {}\n\
                    for example, one such instantiation is: {}",
                    supertype.display(ctx)?,
                    lower.display(ctx)?
                ))
            }))
        }
        (supertype, Type::TyVar(level)) => {
            // if the lower bound doesn't exist (ie. it is unbounded below), it is equivalent to
            // having a lower bound of the bottom type
            let (_, subtype_bounds) = ctx.get_ty_var_unwrap(*level)?;
            let upper = subtype_bounds
                .upper
                .unwrap_or_else(|| ctx.intern(Type::Any));
                // a type is guaranteed to be a supertype of the instantiated type iff it is a
                // supertype of the upper bound (due to the transitivity of subtyping)
            check_subtype(supertype, upper, ctx).map_err(try_prepend(|| {
                Ok(format!(
                    "subtyping must be guaranteed for all possible instantiations of type var: {}\n\
                    for example, one such instantiation is: {}",
                    supertype.display(ctx)?,
                    upper.display(ctx)?
                ))
            }))
        }
        (
            Type::Arr {
                arg: arg_sup,
                result: res_sup,
            },
            Type::Arr {
                arg: arg_sub,
                result: res_sub,
            },
        ) => {
            check_subtype(arg_sub, arg_sup, ctx)?;
            check_subtype(res_sup, res_sub, ctx)
        }
        (Type::Enum(variants_sup), Type::Enum(variants_sub)) => variants_sub
            .0
            .iter()
            // for each variant of the subtype:
            .try_for_each(|(l, ty_sub)| {
                // check that the supertype also has it...
                let Some(ty_sup) = variants_sup.0.get(l) else {
                    return Err(format!(
                        "subtyping error: label '{l}' missing from supertype",
                    ));
                };
                // and that the variant types maintain the same subtyping relationship
                check_subtype(ty_sup, ty_sub, ctx)
            }),
        (Type::Tuple(elems_sup), Type::Tuple(elems_sub)) => {
            if elems_sup.len() != elems_sub.len() {
                return Err("subtyping error: tuples have different lengths".to_string());
            }
            zip_eq(elems_sup, elems_sub).try_for_each(|(sup, sub)| check_subtype(sup, sub, ctx))
        }
        (Type::Bool, Type::Bool) => Ok(()),
        (Type::Any, _) => Ok(()),
        (_, Type::Any) => Err(
            "_ is the any type: it has no supertypes bar itself and cannot be constructed (directly)"
                .to_string(),
        ),
        (_, Type::Never) => Ok(()),
        (Type::Never, _) => Err(
            "! is the never type: it has no subtypes bar itself and cannot be constructed"
                .to_string(),
        ),
        // not using _ to avoid catching more cases than intended
        (Type::Arr { .. } | Type::Enum(..) | Type::Tuple(..) | Type::Bool, _) => {
            Err("subtyping error: types are incompatible".to_string())
        }
    }
    .map_err(try_prepend(|| {
        Ok(format!(
            "subtyping error:\n\
            {}\n\
            is not a supertype of:\n\
            {}",
            supertype.display(ctx)?,
            subtype.display(ctx)?
        ))
    }))
}

fn ty_eq<'a>(ty1: InternedType<'a>, ty2: InternedType<'a>) -> bool {
    std::ptr::eq(ty1, ty2)
}

impl<'a> Type<'a> {
    fn get_function_result_type(
        &'a self,
        ctx: &Context<'a, '_>,
    ) -> Result<&'a Self, TypeCheckError> {
        match self {
            Type::Arr { arg: _, result } => Ok(result),
            Type::TyVar(level) => ctx
                .get_ty_var_unwrap(*level)?
                .1
                .upper
                .map(|t| t.get_function_result_type(ctx))
                .unwrap_or(Err(format!(
                    "expected function type but got a type arg without an upper bound:\n{}",
                    self.display(ctx)?
                ))),
            Type::Never => Ok(self),
            _ => Err(format!(
                "expected function type\ngot: {}",
                self.display(ctx)?
            )),
        }
    }

    /// Join multiple types to produce the 'minimal' supertype.
    /// Intuitively, it's the union of the input types.
    ///
    /// Specifically, should be the type that is:
    /// - a supertype of every input type
    /// - a subtype of all other supertypes of every input type.
    ///
    /// # Errors
    /// When joining incompatible types (ie. types with no common supertypes).
    ///
    /// We could return the top type in this situation but the top type is essentially useless (ie.
    /// isomorphic to the unit type) so the user could just discard the values to join unit types
    /// instead.
    fn join(
        types: impl IntoIterator<Item = InternedType<'a>>,
        ctx: &Context<'a, '_>,
    ) -> Result<InternedType<'a>, TypeCheckError> {
        fn join2<'a>(
            ty1: InternedType<'a>,
            ty2: InternedType<'a>,
            ctx: &Context<'a, '_>,
        ) -> Result<InternedType<'a>, TypeCheckError> {
            // these checks are meant as optimisations, and shouldn't be necessary for correctness
            if ty_eq(ty1, ty2) {
                return Ok(ty1);
            }
            // TODO(proper errors): catch specifically subtyping errors
            if check_subtype(ty1, ty2, ctx).is_ok() {
                return Ok(ty1);
            }
            if check_subtype(ty2, ty1, ctx).is_ok() {
                return Ok(ty2);
            }
            let ty = match (ty1, ty2) {
                (
                    Type::TyAbs {
                        name: name1,
                        bounds:
                            TyBounds {
                                upper: upper1,
                                lower: lower1,
                            },
                        result: res1,
                    },
                    Type::TyAbs {
                        name: name2,
                        bounds:
                            TyBounds {
                                upper: upper2,
                                lower: lower2,
                            },
                        result: res2,
                    },
                ) => {
                    let name = std::cmp::min(name1, name2);
                    let bounds = TyBounds {
                        upper: match (upper1, upper2) {
                            (Some(upper1), Some(upper2)) => {
                                Some(Type::meet([*upper1, *upper2], ctx)?)
                            }
                            (Some(upper), None) | (None, Some(upper)) => Some(*upper),
                            (None, None) => None,
                        },
                        lower: match (lower1, lower2) {
                            (Some(lower1), Some(lower2)) => Some(join2(lower1, lower2, ctx)?),
                            (Some(lower), None) | (None, Some(lower)) => Some(*lower),
                            (None, None) => None,
                        },
                    };
                    Type::TyAbs {
                        name,
                        bounds,
                        result: join2(res1, res2, &ctx.push_ty_var(name, bounds))?,
                    }
                }
                (Type::TyVar(level1), Type::TyVar(level2)) => {
                    return if level1 == level2 {
                        Ok(ty1)
                    } else {
                        return Err(format!(
                            "cannot join type variables:\n\
                            variable 1: {ty1}\n\
                            variable 2: {ty2}",
                            ty1 = ty1.display(ctx)?,
                            ty2 = ty2.display(ctx)?
                        ));
                    };
                }
                (
                    Type::Arr {
                        arg: arg1,
                        result: res1,
                    },
                    Type::Arr {
                        arg: arg2,
                        result: res2,
                    },
                ) => Type::Arr {
                    arg: if ty_eq(arg1, arg2) {
                        arg1
                    } else {
                        // func arg is contravariant so meet instead
                        Type::meet([*arg1, *arg2], ctx)?
                    },
                    result: join2(res1, res2, ctx)?,
                },
                (Type::Enum(variants1), Type::Enum(variants2)) => Type::Enum(
                    variants1
                        .0
                        .iter()
                        .map(|(l, ty1)| {
                            variants2
                                .0
                                .get(l)
                                // recursively join intersection
                                .map(|ty2| join2(ty1, ty2, ctx))
                                // passthru labels only in variants1
                                .unwrap_or(Ok(ty1))
                                .map(|ty| (*l, ty))
                        })
                        .chain(
                            variants2
                                .0
                                .iter()
                                // passthru labels only in variants2
                                .filter(|(l, _)| !variants1.0.contains_key(*l))
                                .map(|(l, ty2)| Ok((*l, *ty2))),
                        )
                        .try_collect()?,
                ),
                (Type::Tuple(elems1), Type::Tuple(elems2)) => {
                    let len1 = elems1.len();
                    let len2 = elems2.len();
                    if len1 != len2 {
                        return Err(format!(
                            "cannot join tuples with different lengths:\n\
                            tuple 1: {len1} elements: {ty1}\n\
                            tuple 2: {len2} elements: {ty2}",
                            ty1 = ty1.display(ctx)?,
                            ty2 = ty2.display(ctx)?
                        ));
                    }
                    Type::Tuple(
                        zip_eq(elems1, elems2)
                            .map(|(ty1, ty2)| join2(ty1, ty2, ctx))
                            .try_collect()?,
                    )
                }
                (Type::Bool, Type::Bool) => Type::Bool,
                (any @ Type::Any, _) | (_, any @ Type::Any) => return Ok(any),
                (Type::Never, ty) | (ty, Type::Never) => return Ok(ty),
                // not using _ to avoid catching more cases than intended
                (
                    Type::TyAbs { .. }
                    | Type::TyVar { .. }
                    | Type::Arr { .. }
                    | Type::Enum(..)
                    | Type::Tuple(..)
                    | Type::Bool,
                    _,
                ) => {
                    return Err(format!(
                        "cannot join incompatible types:\n\
                        type 1: {ty1}\n\
                        type 2: {ty2}\n",
                        ty1 = ty1.display(ctx)?,
                        ty2 = ty2.display(ctx)?
                    ));
                }
            };

            let ty = ctx.intern(ty);
            debug_assert_eq!(check_subtype(ty, ty1, ctx), Ok(()));
            debug_assert_eq!(check_subtype(ty, ty2, ctx), Ok(()));

            Ok(ty)
        }

        let mut iter = types.into_iter();
        let Some(first) = iter.next() else {
            return Ok(ctx.intern(Type::Never));
        };
        iter.try_fold(first, |ty1, ty2| join2(ty1, ty2, ctx))
    }

    /// Meet multiple types to produce the 'maximal' subtype.
    /// Intuitively, it's the intersection of the input types.
    ///
    /// Specifically, should be the type that is:
    /// - a subtype of every input type
    /// - a supertype of all other subtypes of every input type.
    ///
    /// # Errors
    /// - meeting 0 types (should not occur in practice)
    fn meet(
        types: impl IntoIterator<Item = InternedType<'a>>,
        ctx: &Context<'a, '_>,
    ) -> Result<InternedType<'a>, TypeCheckError> {
        fn meet2<'a>(
            ty1: InternedType<'a>,
            ty2: InternedType<'a>,
            ctx: &Context<'a, '_>,
        ) -> Result<InternedType<'a>, TypeCheckError> {
            // these checks are meant as optimisations, and shouldn't be necessary for correctness
            if ty_eq(ty1, ty2) {
                return Ok(ty1);
            }
            // TODO(proper errors): catch specifically subtyping errors
            if check_subtype(ty2, ty1, ctx).is_ok() {
                return Ok(ty1);
            }
            if check_subtype(ty1, ty2, ctx).is_ok() {
                return Ok(ty2);
            }
            let ty = match (ty1, ty2) {
                (
                    Type::TyAbs {
                        name: name1,
                        bounds:
                            TyBounds {
                                upper: upper1,
                                lower: lower1,
                            },
                        result: res1,
                    },
                    Type::TyAbs {
                        name: name2,
                        bounds:
                            TyBounds {
                                upper: upper2,

                                lower: lower2,
                            },
                        result: res2,
                    },
                ) => {
                    let name = std::cmp::min(name1, name2);
                    let bounds = TyBounds {
                        upper: match (upper1, upper2) {
                            (Some(upper1), Some(upper2)) => Some(meet2(upper1, upper2, ctx)?),
                            (Some(upper), None) | (None, Some(upper)) => Some(*upper),
                            (None, None) => None,
                        },
                        lower: match (lower1, lower2) {
                            (Some(lower1), Some(lower2)) => {
                                Some(Type::join([*lower1, *lower2], ctx)?)
                            }
                            (Some(lower), None) | (None, Some(lower)) => Some(*lower),
                            (None, None) => None,
                        },
                    };
                    Type::TyAbs {
                        name,
                        bounds,
                        result: meet2(res1, res2, &ctx.push_ty_var(name, bounds))?,
                    }
                }
                (Type::TyVar(level1), Type::TyVar(level2)) => {
                    return if level1 == level2 {
                        Ok(ty1)
                    } else {
                        return Err(format!(
                            "cannot join type variables:\n\
                            variable 1: {ty1}\n\
                            variable 2: {ty2}",
                            ty1 = ty1.display(ctx)?,
                            ty2 = ty2.display(ctx)?
                        ));
                    };
                }
                (
                    Type::Arr {
                        arg: arg1,
                        result: res1,
                    },
                    Type::Arr {
                        arg: arg2,
                        result: res2,
                    },
                ) => Type::Arr {
                    arg: if ty_eq(arg1, arg2) {
                        arg1
                    } else {
                        // contravariant * contravariant = covariant again
                        Type::join([*arg1, *arg2], ctx)?
                    },
                    result: meet2(res1, res2, ctx)?,
                },
                (Type::Enum(variants1), Type::Enum(variants2)) => Type::Enum(
                    // meeting enums
                    variants1
                        .0
                        .iter()
                        .filter_map(|(l, ty1)| {
                            variants2
                                .0
                                .get(l)
                                // recursively meet only intersection
                                .map(|ty2| meet2(ty1, ty2, ctx).map(|ty| (*l, ty)))
                        })
                        .try_collect()?,
                ),
                (Type::Tuple(elems1), Type::Tuple(elems2)) => {
                    let len1 = elems1.len();
                    let len2 = elems2.len();
                    if len1 == len2 {
                        Type::Tuple(
                            zip_eq(elems1, elems2)
                                .map(|(ty1, ty2)| meet2(ty1, ty2, ctx))
                                .try_collect()?,
                        )
                    } else {
                        Type::Never
                    }
                }
                (Type::Bool, Type::Bool) => Type::Bool,
                (Type::Any, ty) | (ty, Type::Any) => return Ok(ty),
                (never @ Type::Never, _) | (_, never @ Type::Never) => return Ok(never),
                // not using _ to avoid catching more cases than intended
                (
                    Type::TyAbs { .. }
                    | Type::TyVar { .. }
                    | Type::Arr { .. }
                    | Type::Enum(..)
                    | Type::Tuple(..)
                    | Type::Bool,
                    _,
                ) => Type::Never,
            };

            let ty = ctx.intern(ty);
            debug_assert_eq!(check_subtype(ty1, ty, ctx), Ok(()));
            debug_assert_eq!(check_subtype(ty2, ty, ctx), Ok(()));

            Ok(ty)
        }

        let mut iter = types.into_iter();
        let Some(first) = iter.next() else {
            return Err("cannot meet 0 types".to_string());
        };
        iter.try_fold(first, |ty1, ty2| meet2(ty1, ty2, ctx))
    }
}

impl<'a> Type<'a> {
    fn destructure(
        &self,
        arg_structure: &ArgStructure,
        ctx: &Context<'a, '_>,
    ) -> Result<impl Iterator<Item = &Self>, TypeCheckError> {
        fn inner<'a, 's>(
            arg_structure: &ArgStructure,
            ty: &'s Type<'a>,
            ctx: &Context<'a, '_>,
            output: &mut impl FnMut(&'s Type<'a>),
        ) -> Result<(), TypeCheckError> {
            match (arg_structure, ty) {
                (ArgStructure::Tuple(st_elems), Type::Tuple(ty_elems)) => {
                    let st_len = st_elems.len();
                    let ty_len = ty_elems.len();
                    if st_len != ty_len {
                        // TODO
                        return Err(format!(
                            "destructured tuple has {st_len} elements\nwhile it's type has {ty_len} elements"
                        ));
                    }
                    zip_eq(st_elems, ty_elems)
                        .try_for_each(|(st, ty)| inner(st, ty, ctx, output))?;
                }

                (ArgStructure::Tuple(_), ty) => {
                    // TODO
                    return Err(format!(
                        "cannot tuple-destructure value of type {ty}",
                        ty = ty.display(ctx)?
                    ));
                }
                (ArgStructure::Var, ty) => output(ty),
            }
            Ok(())
        }
        let mut buffer = Vec::new();
        inner(arg_structure, self, ctx, &mut |ty| buffer.push(ty))?;
        Ok(buffer.into_iter())
    }

    fn substitute_ty_var_rec(
        &'a self,
        depth: Lvl,
        ty: &'a Self,
        ctx: &Context<'a, '_>,
    ) -> &'a Self {
        let ty = match self {
            Type::TyAbs {
                name,
                bounds: TyBounds { upper, lower },
                result,
            } => Type::TyAbs {
                name,
                bounds: TyBounds {
                    upper: upper.map(|t| t.substitute_ty_var_rec(depth, ty, ctx)),
                    lower: lower.map(|t| t.substitute_ty_var_rec(depth, ty, ctx)),
                },
                result: result.substitute_ty_var_rec(depth, ty, ctx),
            },
            Type::TyVar(level) if *level == depth => return ty,
            Type::TyVar(level) => match level.shallower() {
                // deeper than replaced but not equal (due to prev arm)
                Some(shallower) if level.deeper_than(depth) => Type::TyVar(shallower),
                // either:
                // - shallowest so could not be strictly deeper
                // - not deeper
                None | Some(_) => return self,
            },
            Type::Arr { arg, result } => Type::Arr {
                arg: arg.substitute_ty_var_rec(depth, ty, ctx),
                result: result.substitute_ty_var_rec(depth, ty, ctx),
            },
            Type::Enum(variants) => Type::Enum(
                variants
                    .0
                    .iter()
                    .map(|(l, t)| (*l, t.substitute_ty_var_rec(depth, ty, ctx)))
                    .collect(),
            ),
            Type::Tuple(elems) => Type::Tuple(
                elems
                    .iter()
                    .map(|e| e.substitute_ty_var_rec(depth, ty, ctx))
                    .collect(),
            ),
            Type::Bool | Type::Any | Type::Never => return self,
        };

        ctx.intern(ty)
    }

    fn substitute_ty_var(&'a self, ty: &'a Self, ctx: &Context<'a, '_>) -> &'a Self {
        self.substitute_ty_var_rec(ctx.next_ty_var_level(), ty, ctx)
    }
}

fn prepend<'s, F, S>(f: F) -> impl FnOnce(TypeCheckError) -> TypeCheckError
where
    F: FnOnce() -> S,
    S: Into<std::borrow::Cow<'s, str>>,
{
    |mut e| {
        e.insert(0, '\n');
        e.insert_str(0, &f().into());
        e
    }
}

fn try_prepend<'s, F, S>(f: F) -> impl FnOnce(TypeCheckError) -> TypeCheckError
where
    F: FnOnce() -> Result<S, TypeCheckError>,
    S: Into<std::borrow::Cow<'s, str>>,
{
    |mut e| match f() {
        Ok(s) => {
            e.insert(0, '\n');
            e.insert_str(0, &s.into());
            e
        }
        Err(e) => e,
    }
}
