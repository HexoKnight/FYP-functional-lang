use lalrpop_util::lalrpop_mod;

use crate::reprs::ast::Term;

lalrpop_mod!(
    #[allow(clippy::pedantic)]
    syntax,
    "/parsing/syntax.rs"
);

type UserParserError = String;

pub type ParseError<'i> =
    lalrpop_util::ParseError<usize, lalrpop_util::lexer::Token<'i>, UserParserError>;

#[derive(Default)]
pub struct Parser {
    term_parser: syntax::TermParser,
}
impl Parser {
    pub fn parse<'i>(&self, input: &'i str) -> Result<Term<'i>, ParseError<'i>> {
        self.term_parser.parse(input)
    }
}
