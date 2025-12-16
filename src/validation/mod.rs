use crate::common::WithInfo;
use crate::reprs::ast;
use crate::reprs::untyped_ir as ir;

type ValidationError = String;

struct Context<'i> {
    var_stack: Vec<&'i str>,
}

trait Validate<'i> {
    type Validated;
    fn validate(&self, ctx: &mut Context<'i>) -> Result<Self::Validated, ValidationError>;
}

pub fn validate<'i>(ast: &ast::Term<'i>) -> Result<ir::Term<'i>, ValidationError> {
    ast.validate(&mut Context {
        var_stack: Vec::new(),
    })
}

impl<'i, T: Validate<'i>> Validate<'i> for Box<T> {
    type Validated = Box<T::Validated>;

    fn validate(&self, ctx: &mut Context<'i>) -> Result<Self::Validated, ValidationError> {
        T::validate(&self, ctx).map(Box::new)
    }
}

impl<'i> Validate<'i> for ast::Term<'i> {
    type Validated = ir::Term<'i>;

    fn validate(&self, ctx: &mut Context<'i>) -> Result<Self::Validated, ValidationError> {
        let WithInfo(info, term) = self;

        let term = match term {
            ast::RawTerm::Abs(ast::Abs {
                arg,
                arg_type,
                body,
            }) => ir::RawTerm::Abs(ir::Abs {
                arg_type: arg_type.validate(ctx)?,
                body: {
                    ctx.var_stack.push(arg.name);
                    let body = body.validate(ctx)?;
                    ctx.var_stack.pop();
                    body
                },
            }),
            ast::RawTerm::App(ast::App { func, arg }) => ir::RawTerm::App(ir::App {
                func: func.validate(ctx)?,
                arg: arg.validate(ctx)?,
            }),
            ast::RawTerm::Var(ast::Var { ident }) => {
                let Some(index) = ctx
                    .var_stack
                    .iter()
                    .rev()
                    .position(|arg| arg == &ident.name)
                else {
                    return Err(format!("variable '{}' not found", ident.name));
                };
                ir::RawTerm::Var(ir::Var {
                    name: ident.name,
                    index,
                })
            }
            ast::RawTerm::Bool(b) => ir::RawTerm::Bool(*b),
        };

        Ok(WithInfo(*info, term))
    }
}

impl<'i> Validate<'_> for ast::Type<'i> {
    type Validated = ir::Type<'i>;

    fn validate(&self, ctx: &mut Context) -> Result<Self::Validated, ValidationError> {
        let WithInfo(info, ty) = self;

        let ty = match ty {
            ast::RawType::Arr(ast::Arr { arg, result }) => ir::RawType::Arr(ir::Arr {
                arg: arg.validate(ctx)?,
                result: result.validate(ctx)?,
            }),
            ast::RawType::Bool => ir::RawType::Bool,
        };
        Ok(WithInfo(*info, ty))
    }
}

#[cfg(test)]
pub mod tests {
    use pretty_assertions::assert_eq;

    use crate::parsing::tests::parse_success;

    use super::*;

    #[track_caller]
    pub fn validate_success(src: &str) -> ir::Term<'_> {
        let ast = parse_success(src);
        match validate(&ast) {
            Ok(o) => o,
            Err(e) => panic!("validate failure:\n'{}'\n{}", src, e),
        }
    }

    #[track_caller]
    pub fn validate_failure(src: &str) -> ValidationError {
        let ast = parse_success(src);
        match validate(&ast) {
            Ok(o) => panic!("validate success:\n'{}'\n{:#?}", src, o),
            Err(e) => e,
        }
    }

    #[track_caller]
    pub fn validate_eq(src1: &str, src2: &str) {
        assert_eq!(validate_success(src1), validate_success(src2))
    }

    #[test]
    fn parsing() {
        validate_success(r"\x:bool x");
        validate_success(r"(\x:bool x)");
        validate_success(r"\x:bool \ y : bool x");
        validate_failure(r"\x:bool y");

        validate_success(r"\x:bool x x");

        validate_success(r"(\x:bool x) true");
        validate_success(r"(\x: bool -> bool x) (\y: bool false)");
    }
}
