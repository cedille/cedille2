
use nom::{
    Parser,
    branch::alt,
    error::context,
    combinator::{opt, recognize, value, peek, not, eof},
    sequence::{tuple, pair},
    multi::{separated_list1, separated_list0, many0_count, many1_count},
    character::complete::{multispace0, alpha1, alphanumeric1, alphanumeric0, line_ending, not_line_ending},
    bytes::complete::{is_not, is_a, take_while}
};
use nom_locate::LocatedSpan;
use nom_supreme::{
    error::ErrorTree,
    tag::complete::tag,
    multi::collect_separated_terminated,
    parser_ext::ParserExt,
    final_parser::final_parser
};


use cedille2_core::utility::*;
use crate::syntax::*;

type In<'a> = LocatedSpan<&'a str>;
type Span = (usize, usize);
type IResult<I, O> = Result<(I, O), nom::Err<ErrorTree<I>>>;

pub fn parse_file(input: In) -> Result<Vec<Command>, ErrorTree<In>> {
    let mut result = final_parser(parse_command_sequence);
    result(input)
}

fn parse_command_sequence(mut input : In) -> IResult<In, Vec<Command>> {
    let mut result = Vec::with_capacity(8);

    let (rest, _) = many0_count(empty_line)(input)?;
    input = rest;

    while input.len() > 0 {
        let (rest, command) = parse_command(input)?;
        result.push(command);

        let (rest, _) = alt((
            eof.preceded_by(multispace0).map(|_| ()),
            many1_count(empty_line).map(|_| ()),
        ))(rest)?;

        input = rest;
    }

    Ok((input, result))
}

pub fn parse_command(input : In) -> IResult<In, Command> {
    let (_, keyword) = peek(alt((
        tag("module").preceded_by(bspace0(2)),
        tag("import").preceded_by(bspace0(2)),
        tag("").preceded_by(bspace0(2))
    )))(input)?;

    match *keyword {
        "module" => parse_module(input),
        "import" => parse_import(input),
        _ => parse_def(input)
    }
}

fn parse_module(input: In) -> IResult<In, Command> {
    let (rest, (_, path)) = context("module", tuple((
        tag("module").preceded_by(bspace0(2)),
        parse_path.preceded_by(bspace0(2))
    )))(input)?;

    let module = Command::Module(path, vec![]);
    Ok((rest, module))
}

fn parse_import(input: In) -> IResult<In, Command> {
    let (rest, (start, path))
    = context("import", tuple((
        tag("import").preceded_by(bspace0(2)),
        parse_path.preceded_by(bspace0(2))
    )))(input)?;

    let span = (start.location_offset(), path.1);
    let import = Import {
        span,
        public: false,
        path,
        namespace: None,
        args: vec![]
    };

    Ok((rest, Command::Import(import)))
}

fn parse_def(input: In) -> IResult<In, Command> {
    let (rest, (name, vars, kind, body))
    = context("def", tuple((
        parse_symbol.preceded_by(bspace0(2)),
        separated_list0(bspace1(2), parse_lambda_var).preceded_by(bspace0(2)),
        alt((tag(":="), tag(":"))).preceded_by(bspace0(2)),
        parse_term
    )))(input)?;

    let span = (name.1.0, body.span().1);
    let command = match *kind {
        ":" => {
            let decl = Declaration {
                span,
                name: name.0,
                body: body.boxed()
            };
            Command::Declare(decl)
        }
        ":=" => {
            let def = Definition {
                span,
                name: name.0,
                vars,
                body: body.boxed()
            };
            Command::Define(def)
        },
        _ => unreachable!()
    };
    Ok((rest, command))
}

pub fn parse_term(input : In) -> IResult<In, Term> {
    let inner = alt((
        parse_term_let,
        parse_term_binder,
        parse_term_lambda,
        parse_term_equal,
        parse_term_simple_binder,
        parse_term_application
    ));
    
    inner.preceded_by(bspace0(0)).parse(input)
}

fn parse_term_let(input : In) -> IResult<In, Term> {
    let (rest, (start, sym, ann, _, def, end, body))
    = context("let", tuple((
        tag("let").preceded_by(bspace0(2)),
        parse_symbol.preceded_by(bspace0(2)),
        opt(pair(
            tag(":").preceded_by(bspace0(2)), 
            parse_term
        )),
        tag(":=").preceded_by(bspace0(2)),
        parse_term,
        tag(";").preceded_by(bspace0(2)),
        parse_term
    )))(input)?;

    let def = DefineTerm {
        span: (start.location_offset(), end.location_offset()),
        opaque: false,
        name: sym.0,
        anno: ann.map(|(_, t)| t.boxed()),
        body: def.boxed()
    };

    let term = Term::Let {
        span: (start.location_offset(), body.span().1),
        mode: Mode::Free,
        def,
        body: body.boxed()
    };

    Ok((rest, term))
}

fn parse_term_binder(input : In) -> IResult<In, Term> {
    let (rest, (start, sym, _, ann, _, kind, body))
    = context("binder", tuple((
        tag("(").preceded_by(bspace0(2)),
        parse_symbol.preceded_by(bspace0(2)),
        tag(":").preceded_by(bspace0(2)),
        parse_term,
        tag(")").preceded_by(bspace0(2)),
        alt((tag("->"), tag("=>"), tag("∩"))).preceded_by(bspace0(2)),
        parse_term
    )))(input)?;

    let span = (start.location_offset(), body.span().1);
    let var = Some(sym.0);
    let domain = ann.boxed();
    let body = body.boxed();

    let term = match *kind.fragment() {
        "->" => Term::Pi { span, mode: Mode::Free, var, domain, body },
        "=>" => Term::Pi { span, mode: Mode::Erased, var, domain, body },
        "∩" => Term::Intersect { span, var, first: domain, second: body },
        _ => unreachable!()
    };

    Ok((rest, term))
}

fn parse_term_simple_binder(input : In) -> IResult<In, Term> {
    let (rest, (lhs, kind, rhs))
    = context("simple_binder", tuple((
        parse_term_atom.preceded_by(bspace0(2)),
        alt((tag("->"), tag("=>"), tag("∩"), tag("="))).preceded_by(bspace0(2)),
        parse_term.preceded_by(bspace0(2))
    )))(input)?;

    let span = (lhs.span().0, rhs.span().1);
    let lhs = lhs.boxed();
    let rhs = rhs.boxed();

    let term = match *kind.fragment() {
        "->" => Term::Pi { span, mode: Mode::Free, var: None, domain: lhs, body: rhs},
        "=>" => Term::Pi { span, mode: Mode::Erased, var: None, domain: lhs, body: rhs},
        "∩" => Term::Intersect { span, var: None, first: lhs, second: rhs },
        "=" => Term::Equality { span, left: lhs, right: rhs, domain: None },
        _ => unreachable!()
    };

    Ok((rest, term))
}

fn parse_term_lambda(input : In) -> IResult<In, Term> {
    let (rest, (start, vars, _, body))
    = context("lambda", tuple((
        tag("λ").preceded_by(bspace0(2)),
        separated_list1(bspace1(2), parse_lambda_var).preceded_by(bspace0(2)),
        tag(".").preceded_by(bspace0(2)),
        parse_term.preceded_by(bspace0(2))
    )))(input)?;

    let span = (start.location_offset(), body.span().1);
    let body = body.boxed();
    let term = Term::Lambda { span, vars, body };

    Ok((rest, term))
}

// atom "=[" term "]" term
fn parse_term_equal(input : In) -> IResult<In, Term> {
    let (rest, (lhs, _, ann, _, rhs))
    = context("equal", tuple((
        parse_term_atom,
        tag("=[").preceded_by(bspace0(2)),
        parse_term,
        tag("]").preceded_by(bspace0(2)),
        parse_term
    )))(input)?;

    let span = (lhs.span().0, rhs.span().1);
    let term = Term::Equality {
        span,
        left: lhs.boxed(),
        right: rhs.boxed(),
        domain: Some(ann.boxed())
    };

    Ok((rest, term))
}

fn parse_term_application(input : In) -> IResult<In, Term> {
    let (rest, mut args)
    = context("application",
        separated_list1(bspace1(2), parse_term_atom).preceded_by(bspace0(2))
    )(input)?;

    let mut tail = args.split_off(1);
    // Safety: Parser guarantees that args.len() > 0
    let head = args.drain(..).next().unwrap();
    let start = head.span().0;

    let term = tail.drain(..)
        .fold(head, |acc, t| {
            let span = (start, t.span().1);
            Term::Apply { span, fun: acc.boxed(), arg: t.boxed() }
        });

    Ok((rest, term))
}

/*
    atom ::=
    | "[" term "," term (";" term)? "]" (".1" | ".2")?
    | "φ" term "{" term "," term "}" (".1" | ".2")?
    | "(" term ")" (".1" | ".2")?
    | ident (".1" | ".2")?
*/
fn parse_term_atom(input: In) -> IResult<In, Term> {
    let inner = alt((
        parse_term_pair,
        parse_term_cast,
        parse_term_paren,
        parse_term_variable
    ));
    
    let (rest, (term, proj))
    = context("projection", tuple((
        inner.preceded_by(bspace0(2)),
        opt(alt((
            tag(".1"),
            tag(".2")
        ))),
    )))(input)?;

    let term = if let Some(proj) = proj {
        let span = (term.span().0, proj.location_offset() + 1);
        match *proj.fragment() {
            ".1" => Term::Project { span, variant:1, body:term.boxed() },
            ".2" => Term::Project { span, variant:2, body:term.boxed() },
            _ => unreachable!()
        }
    } else { term };

    Ok((rest, term))
}

// "[" term "," term (";" term)? "]"
fn parse_term_pair(input: In) -> IResult<In, Term> {
    let (rest, (start, lhs, _, rhs, ann, end))
    = context("pair", tuple((
        tag("[").preceded_by(bspace0(2)),
        parse_term,
        tag(",").preceded_by(bspace0(2)),
        parse_term,
        opt(pair(
            tag(";").preceded_by(bspace0(2)), 
            parse_term
        )),
        tag("]").preceded_by(bspace0(2))
    )))(input)?;

    let span = (start.location_offset(), end.location_offset());
    let ann = ann.map(|(_, t)| t.boxed());
    let term = Term::Pair {
        span,
        anno: ann,
        first: lhs.boxed(),
        second: rhs.boxed()
    };

    Ok((rest, term))
}

// "φ" term "{" term "," term "}"
fn parse_term_cast(input: In) -> IResult<In, Term> {
    let (rest, (start, input, _, witness, _, evidence, end))
    = context("cast", tuple((
        tag("φ").preceded_by(bspace0(2)),
        parse_term,
        tag("{").preceded_by(bspace0(2)),
        parse_term,
        tag(",").preceded_by(bspace0(2)),
        parse_term,
        tag("}").preceded_by(bspace0(2))
    )))(input)?;

    let span = (start.location_offset(), end.location_offset());
    let term = Term::Cast {
        span,
        input: input.boxed(),
        witness: witness.boxed(),
        evidence: evidence.boxed()
    };

    Ok((rest, term))
}

// "(" term ")"
fn parse_term_paren(input: In) -> IResult<In, Term> {
    let (rest, (_, term, _))
    = context("paren", tuple((
        tag("(").preceded_by(bspace0(2)),
        parse_term,
        tag(")").preceded_by(bspace0(2))
    )))(input)?;

    Ok((rest, term))
}

fn parse_term_variable(input: In) -> IResult<In, Term> {
    let (rest, id) = parse_ident(input)?;
    let term = Term::Variable { span: id.1, id: id.0 };
    Ok((rest, term))
}

fn parse_lambda_var(input: In) -> IResult<In, LambdaVar> {
    let parse_sym = pair(
        opt(tag("-")).preceded_by(bspace0(2)),
        parse_symbol.preceded_by(bspace0(2))
    ).map(|(is_erased, x)| {
        let mode = if is_erased.is_some() { Mode::Erased } else { Mode::Free };
        (mode, x.0, None)
    });

    let parse_ann = context("annotation", tuple((
        opt(tag("-")).preceded_by(bspace0(2)),
        tag("(").preceded_by(bspace0(2)),
        parse_symbol.preceded_by(bspace0(2)),
        tag(":").preceded_by(bspace0(2)),
        parse_term,
        tag(")").preceded_by(bspace0(2))
    ))).map(|(is_erased, _, sym, _, ann, _)| {
        let mode = if is_erased.is_some() { Mode::Erased } else { Mode::Free };
        (mode, sym.0, Some(ann))
    });

    let (rest, (mode, sym, ann)) = alt((parse_sym, parse_ann))(input)?;

    let var = LambdaVar {
        mode,
        var: Some(sym),
        anno: ann
    };

    Ok((rest, var))
}

fn parse_ident(input : In) -> IResult<In, (Id, Span)> {
    let inner = context("ident", separated_list1(tag("."), parse_symbol));
    let (rest, mut names) = inner.preceded_by(bspace0(2)).parse(input)?;

    let start =
        if let Some((_, (start, _))) = names.first() { *start }
        else { unreachable!() };
    let end =
        if let Some((_, (_, end))) = names.last() { *end }
        else { unreachable!() };
    let span = (start, end);

    let len = names.len();
    let iter = &mut names.drain(..);

    let namespace: Vec<_> = iter.take(len - 1).map(|(x, _)| x).collect();
    // Safety: Parser guarantees there is at least one symbol
    let name = unsafe { iter.last().unwrap_unchecked().0 };

    let id = Id { namespace, name };
    let result = (id, span);

    Ok((rest, result))
}

fn parse_symbol(input : In) -> IResult<In, (Symbol, Span)> {
    let (rest, symbol)
    = context("symbol", recognize(tuple((
        alpha1,
        alphanumeric0,
        opt(pair(
            alt((tag("-"), tag("_"))),
            alphanumeric0
        )),
    ))))(input)?;

    let span = (symbol.location_offset(), symbol.location_offset() + symbol.fragment().len());
    let sym: Symbol = (*symbol.fragment()).into();
    Ok((rest, (sym, span)))
}

fn parse_path(input : In) -> IResult<In, Span> {
    let (rest, path) = context("path", recognize(separated_list1(
        tag("/"),
        alt((alphanumeric1, tag(".."), tag(".")))
    )))(input)?;

    let span = (path.location_offset(), path.location_offset() + path.fragment().len());
    Ok((rest, span))
}

fn bspace0<'a>(margin: usize) -> impl FnMut(In<'a>) -> IResult<In<'a>, usize> {
    many0_count(alt((
        tag(" ").map(|_| ()),
        tuple((
            line_ending,
            take_while(|c| c == ' ')
                .verify(move |s: &In| s.len() == margin),
            not(alt((line_ending, tag(" "))))
        )).map(|_| ())
    )))
}

fn bspace1<'a>(margin: usize) -> impl FnMut(In<'a>) -> IResult<In<'a>, usize> {
    many1_count(alt((
        tag(" ").map(|_| ()),
        tuple((
            line_ending,
            take_while(|c| c == ' ')
                .verify(move |s: &In| s.len() == margin),
            not(alt((line_ending, tag(" "))))
        )).map(|_| ())
    )))
}

fn empty_line(input: In) -> IResult<In, ()> {
    let (rest, _) = tuple((
        line_ending,
        many0_count(tag(" ")),
        opt(tuple((
            tag("--"),
            many0_count(not_line_ending)
        )))
    ))(input)?;
    Ok((rest, ()))
}

mod tests {
    use super::*;

    #[test]
    fn basic_test() {
        let input = r#"
            module nat;
            --hmmm
        "#;
        let input = LocatedSpan::new(input);
        let output = parse_file(input);
        assert!(output.is_ok());
    }

}
