
use std::sync::Arc;
use std::collections::HashMap;

use thiserror::Error;
use miette::{SourceSpan, Diagnostic};

use cedille2_core::prelude::*;
use crate::lexer::*;

#[derive(Debug)]
enum Command {
    Extension(Symbol, usize, usize),
    Def(Symbol, Expr)
}

#[derive(Debug)]
enum Expr {
    Word(Symbol),
    Group(Symbol, Vec<Expr>)
}

#[derive(Debug, Error, Diagnostic)]
enum ParseError {
    #[error("Invalid token")]
    InvalidToken {
        #[source_code]
        src: Arc<String>,
        span: SourceSpan
    },
    #[error("Invalid numeral")]
    InvalidNumeral {
        #[source_code]
        src: Arc<String>,
        span: SourceSpan
    },
    #[error("Expected any token, found eof")]
    UnexpectedEndOfFile,
    #[error("Expected nested alignment")]
    Alignment {
        #[source_code]
        src: Arc<String>,
        span: SourceSpan
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Alignment {
    line: usize,
    indent: usize
}

impl Alignment {
    fn nest(&self) -> Alignment {
        Alignment {
            line: self.line,
            indent: self.indent + 2
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ParseGadgetInstruction {
    Expect(Symbol),
    ConsumeExpr(usize)
}

#[derive(Debug)]
struct ParseGadget {
    commands: Vec<ParseGadgetInstruction>
}

#[derive(Debug)]
struct GadgetTable {
    precedence: HashMap<Symbol, (usize, usize)>,
}

impl GadgetTable {
    fn binding_power(&self, prefix: Vec<Symbol>, symbol: Symbol) -> (Option<usize>, Option<usize>) {
        todo!()
    }
}

impl GadgetTable {
    fn new() -> GadgetTable {
        todo!()
    }
}

fn into_miette_span(span: logos::Span) -> SourceSpan {
    let len = span.end - span.start;
    (span.start, len).into()
}

fn parse_file(input: Arc<String>) -> Result<Vec<Command>, ParseError> {
    let mut commands = vec![];
    let mut lex = Lexer::new(input.clone(), input.as_ref());

    let mut prec = GadgetTable::new();



    while let Some(token) = lex.next() {
        let token = token.map_err(|_| invalid_token(&lex))?;
        let command = parse_command(token, &mut prec, &mut lex)?;
        commands.push(command);
    }
    Ok(commands)

}

fn parse_command(token: Token, prec: &mut GadgetTable, lex: &mut Lexer) -> Result<Command, ParseError> {
    let symbol = Symbol::from(lex.slice());
    let align = Alignment {
        line: lex.line(),
        indent: lex.indent()
    };
    let command = if symbol == *KEYWORD_SYNTAX {
        let num1 = parse_numeral(lex)?;
        let num2 = parse_numeral(lex)?;
        Command::Extension(symbol, num1, num2)
    } else {
        let expr = parse_expr(align.nest(), prec, lex)?;
        Command::Def(symbol, expr)
    };
    Ok(command)
}

fn parse_numeral(lex: &mut Lexer) -> Result<usize, ParseError> {
    let data = lex.slice().parse::<usize>().map_err(|_| {
        ParseError::InvalidNumeral { 
            src: lex.src.clone(), 
            span: into_miette_span(lex.span())
        }
    })?;
    Ok(data)
}

#[inline]
fn parse_expr(
    align: Alignment,
    prec: &mut GadgetTable,
    lex: &mut Lexer)
    -> Result<Expr, ParseError>
{
    parse_expr_bp(vec![], 0, align, prec, lex)
}

fn parse_expr_bp(
    mut prefix: Vec<Symbol>,
    min_bp: usize,
    align: Alignment,
    prec: &mut GadgetTable,
    lex: &mut Lexer)
    -> Result<Expr, ParseError>
{
    let mut exprs: Vec<Expr> = vec![];
    let token = lex.next()
        .ok_or(ParseError::UnexpectedEndOfFile)?
        .map_err(|_| invalid_token(lex))?;
    check_alignment(lex, align, lex.indent(), lex.line())?;
    let symbol = Symbol::from(lex.slice());
    let (lp, rp) = prec.binding_power(prefix.clone(), symbol);
    prefix.push(symbol);
    expect_start_operator(lex, lp)?;
    let lhs = if let Some(rp) = rp {
        parse_expr_bp(prefix.clone(), rp, align, prec, lex)?
    } else { Expr::Word(symbol) };
    exprs.push(lhs);

    loop {
        let Some(token) = lex.peek() else { break };
        token.map_err(|_| invalid_token(lex))?;
        if check_alignment(lex, align, lex.indent(), lex.line()).is_err() { break }
        let symbol = Symbol::from(lex.slice());
        let (lp, rp) = prec.binding_power(prefix.clone(), symbol);
        if lp.is_none() && rp.is_none() { break }
        expect_chaining_operator(lex, lp)?;
        let Some(lp) = lp else { unreachable!() };
        if lp < min_bp { break }

        lex.next();
        prefix.push(symbol);
        // postfix symbol
        if rp.is_none() {

        }
    }

    todo!()
}

fn invalid_token(lex: &Lexer) -> ParseError {
    ParseError::InvalidToken {
        src: lex.src.clone(),
        span: into_miette_span(lex.span())
    }
}

fn check_alignment(lex: &Lexer, align: Alignment, indent: usize, line: usize) -> Result<(), ParseError> {
    let test = indent >= align.indent || line == align.line;
    if !test {
        Err(ParseError::Alignment {
            src: lex.src.clone(),
            span: into_miette_span(lex.span())
        })
    } else { Ok(()) }
}

fn expect_start_operator(lex: &Lexer, bp: Option<usize>) -> Result<(), ParseError> {
    todo!()
}

fn expect_chaining_operator(lex: &Lexer, bp: Option<usize>) -> Result<(), ParseError> {
    todo!()
}

mod tests {
    use super::*;

    #[test]
    fn ex1() {
        let input = Arc::new(r#"
            module nat
            syntax 2 + 3
            f : 0A 0B 0C -> Set
            f A B C = c
        "#.to_string());
        parse_file(input).unwrap();
    }
}