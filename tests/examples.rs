use include_dir::{Dir, File, include_dir};

use functional_lang as fl;

const EXAMPLES_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/examples");

fn info<E>(info: impl std::fmt::Display) -> impl FnOnce(E) -> String
where
    E: std::fmt::Display,
{
    move |e| format!("{info}: {e}")
}

fn run_file(file: &File) -> Result<(String, String), String> {
    let content = std::str::from_utf8(file.contents()).map_err(info(""))?;

    let ast = fl::parsing::Parser::default()
        .parse(content)
        .map_err(info("parse failure"))?;

    let untyped_ir = fl::validation::validate(&ast).map_err(info("validate failure"))?;

    let (typed_ir, ty) = fl::typing::type_check(&untyped_ir).map_err(info("type check failure"))?;

    let value = fl::evaluation::evaluate(&typed_ir).map_err(info("evaluation failure"))?;

    Ok((format!("{value:?}"), ty))
}

#[test]
fn run_examples() {
    for file in EXAMPLES_DIR.files() {
        let file_path = file.path().to_string_lossy();
        let (value, ty) = run_file(file)
            .map_err(info(format!("evaulating {file_path}")))
            .unwrap_or_else(|e| panic!("{e}"));
        println!("{file_path} produced the value:\n{value}\nwith type:\n{ty}",);
    }
}
