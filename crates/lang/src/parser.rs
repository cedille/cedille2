
use nom::{
    IResult,
    Parser,
    branch::alt,
    combinator::{opt, recognize, all_consuming},
    sequence::{delimited, tuple, pair},
    multi::{separated_list1, separated_list0},
    character::complete::{multispace0, multispace1, alpha1},
    bytes::complete::tag
};
use nom_locate::LocatedSpan;

use cedille2_core::utility::*;
use crate::syntax::*;

type In<'a> = LocatedSpan<&'a str>;
type Span = (usize, usize);

pub fn parse_file(input: In) -> IResult<In, Module> {
    let inner
    = tuple((
        separated_list0(multispace0, parse_command),
        tag("module"),
        parse_path,
        tag(";"),
        separated_list0(multispace0, parse_command)
    ));

    let (rest, (c1, _, path, _, c2)) = all_consuming(inner)(input)?;
    let module = Module {
        header_commands: c1,
        path,
        commands: c2,
        params: vec![]
    };

    Ok((rest, module))
}

pub fn parse_command(input : In) -> IResult<In, Command> {
    let inner = alt((
        parse_import,
        parse_def,
        parse_decl,
    ));
    
    delimited(multispace0, inner, multispace0)(input)
}

fn parse_import(input: In) -> IResult<In, Command> {
    let (rest, (start, path, end))
    = tuple((
        tag("import"),
        parse_path,
        tag(";")
    ))(input)?;

    let span = (start.location_offset(), end.location_offset());
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
    let (rest, (name, vars, _, body, end))
    = tuple((
        parse_symbol,
        separated_list0(multispace1, parse_lambda_var),
        tag(":="),
        parse_term,
        tag(";")
    ))(input)?;

    let span = (name.1.0, end.location_offset());
    let def = Definition {
        span,
        name: name.0,
        vars,
        body: body.boxed()
    };
    Ok((rest, Command::Define(def)))
}

fn parse_decl(input: In) -> IResult<In, Command> {
    let (rest, (name, _, body, end))
    = tuple((
        parse_symbol,
        tag(":"),
        parse_term,
        tag(";")
    ))(input)?;

    let span = (name.1.0, end.location_offset());
    let decl = Declaration {
        span,
        name: name.0,
        body: body.boxed()
    };
    Ok((rest, Command::Declare(decl)))
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
    
    delimited(multispace0, inner, multispace0)(input)
}

fn parse_term_let(input : In) -> IResult<In, Term> {
    let (rest, (start, sym, ann, _, def, end, body))
    = tuple((
        tag("let"),
        parse_symbol,
        opt(pair(tag(":"), parse_term)),
        tag(":="),
        parse_term,
        tag(";"),
        parse_term
    ))(input)?;

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
    let (rest, (start, sym, _, ann, _, _, kind, body))
    = tuple((
        tag("("),
        parse_symbol,
        tag(":"),
        parse_term,
        tag(")"),
        multispace1,
        alt((tag("->"), tag("=>"), tag("∩"))),
        parse_term
    ))(input)?;

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
    = tuple((
        parse_term_atom,
        alt((tag("->"), tag("=>"), tag("∩"), tag("="))),
        parse_term
    ))(input)?;

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
    let (rest, (start, _, vars, _, _, body))
    = tuple((
        alt((tag("λ"), tag("Λ"))),
        multispace0,
        separated_list1(multispace1, parse_lambda_var),
        multispace0,
        tag("."),
        parse_term
    ))(input)?;

    let span = (start.location_offset(), body.span().1);
    let body = body.boxed();
    let mode = match *start.fragment() {
        "λ" => Mode::Free,
        "Λ" => Mode::Erased,
        _ => unreachable!()
    };
    let term = Term::Lambda { span, vars, body };

    Ok((rest, term))
}

// atom "=[" term "]" term
fn parse_term_equal(input : In) -> IResult<In, Term> {
    let (rest, (lhs, _, ann, _, rhs))
    = tuple((
        parse_term_atom,
        tag("=["),
        parse_term,
        tag("]"),
        parse_term
    ))(input)?;

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
    let (rest, mut args) = separated_list1(multispace1, parse_term_atom)(input)?;

    // Safety: Parser guarantees that args.len() > 0
    let head = unsafe { args.pop().unwrap_unchecked() };

    let term = args.drain(..)
        .fold(head, |acc, t| {
            let span = (head.span().0, t.span().1);
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
        parse_term_variable
    ));
    
    let (rest, (_, term, proj, _))
    = tuple((
        multispace0,
        inner,
        opt(alt((
            tag(".1"),
            tag(".2")
        ))),
        multispace0
    ))(input)?;

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
    = tuple((
        tag("["),
        parse_term,
        tag(","),
        parse_term,
        opt(pair(tag(";"), parse_term)),
        tag("]")
    ))(input)?;

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
    = tuple((
        tag("φ"),
        parse_term,
        tag("{"),
        parse_term,
        tag(","),
        parse_term,
        tag("}")
    ))(input)?;

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
    = tuple((
        tag("("),
        parse_term,
        tag(")")
    ))(input)?;

    Ok((rest, term))
}

fn parse_term_variable(input: In) -> IResult<In, Term> {
    let (rest, id) = parse_ident(input)?;
    let term = Term::Variable { span: id.1, id: id.0 };
    Ok((rest, term))
}

fn parse_lambda_var(input: In) -> IResult<In, LambdaVar> {
    let parse_sym = pair(
        opt(tag("-")),
        parse_symbol
    ).map(|(is_erased, x)| {
        let mode = if is_erased.is_some() { Mode::Erased } else { Mode::Free };
        (mode, x.0, None)
    });

    let parse_ann = tuple((
        opt(tag("-")),
        tag("("),
        parse_symbol,
        tag(":"),
        parse_term,
        tag(")")
    )).map(|(is_erased, start, sym, _, ann, end)| {
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
    let (rest, mut names) = separated_list1(tag("."), parse_symbol)(input)?;

    let start =
        if let Some((_, (start, _))) = names.first() { *start }
        else { unreachable!() };
    let end =
        if let Some((_, (_, end))) = names.last() { *end }
        else { unreachable!() };
    let span = (start, end);

    let len = names.len();
    let mut iter = names.drain(..);
    let namespace: Vec<_> = iter.take(len - 1).map(|(x, _)| x).collect();

    // Safety: Parser guarantees there is at least one symbol
    let name = unsafe { iter.next().unwrap_unchecked().0 };

    let id = Id { namespace, name };
    let result = (id, span);

    Ok((rest, result))
}

fn parse_symbol(input : In) -> IResult<In, (Symbol, Span)> {
    let (rest, symbol)
    = recognize(tuple((
        alpha1,
        opt(pair(
            alt((tag("-"), tag("_"))),
            alpha1
        )),
    )))(input)?;

    let span = (symbol.location_offset(), symbol.location_offset() + symbol.fragment().len());
    let sym: Symbol = (*symbol.fragment()).into();
    Ok((rest, (sym, span)))
}

fn parse_path(input : In) -> IResult<In, Span> {
    unimplemented!()
}
