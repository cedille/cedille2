
use pest::Parser;
use pest::iterators::Pairs;
use pest::error::Error;

#[derive(Parser)]
#[grammar = "cedille.pest"]
pub struct CedilleParser;

pub fn parse(input : &str) -> Result<Pairs<Rule>, Error<Rule>> {
    CedilleParser::parse(Rule::main, input)
}

