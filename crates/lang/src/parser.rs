
use std::sync::Mutex;

use nom::{
    Parser,
    branch::alt,
    error::context,
    combinator::{opt, recognize, peek, not, eof},
    sequence::{tuple, pair},
    multi::{separated_list1, separated_list0, many0_count, many0, many1_count},
    character::complete::{multispace0, alpha1, alphanumeric1, alphanumeric0, line_ending},
    bytes::complete::{is_not, take_while}
};
use nom_locate::LocatedSpan;
use nom_supreme::{
    error::{ErrorTree, BaseErrorKind, Expectation},
    tag::complete::tag,
    parser_ext::ParserExt,
    final_parser::final_parser
};

use imbl::Vector;

use cedille2_core::utility::*;
use crate::syntax::*;

type In<'a> = LocatedSpan<&'a str>;
type Span = (usize, usize);
type IResult<I, O> = Result<(I, O), nom::Err<ErrorTree<I>>>;

static MODULE: Mutex<Option<Symbol>> = Mutex::new(Option::None);

pub fn parse_file(module: Symbol, input: In) -> Result<Vec<Command>, ErrorTree<In>> {
    *MODULE.lock().unwrap() = Some(module);
    let mut result = final_parser(parse_command_sequence);
    result(input)
}

fn parse_command_sequence(mut input : In) -> IResult<In, Vec<Command>> {
    let mut result = Vec::with_capacity(8);

    let (rest, _) = many0_count(empty_line)(input)?;
    input = rest;

    while input.len() > 0 {
        let (rest, command) = parse_command(input)?;
        //dbg!((&rest, &command));
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
        tag("module").preceded_by(bspace0(0)),
        tag("import").preceded_by(bspace0(0)),
        tag("#erase").preceded_by(bspace0(0)),
        tag("").preceded_by(bspace0(0))
    )))(input)?;

    match *keyword {
        "module" => parse_module(input),
        "import" => parse_import(input),
        "#erase" => parse_erase_command(input),
        _ => parse_def(input)
    }
}

fn parse_erase_command(input: In) -> IResult<In, Command> {
    let (rest, (_, term)) = context("erase_command", tuple((
        tag("#erase").preceded_by(bspace0(0)),
        parse_term(2)
    )))(input)?;

    let command = Command::Erase(term);
    Ok((rest, command))
}

fn parse_module(input: In) -> IResult<In, Command> {
    let (rest, (_, path, params)) = context("module", tuple((
        tag("module").preceded_by(bspace0(0)),
        parse_path.preceded_by(bspace0(2)),
        separated_list0(bspace1(2), parse_parameter(2)).preceded_by(bspace0(2)),
    )))(input)?;

    let module = Command::Module(path, params);
    Ok((rest, module))
}

fn parse_import(input: In) -> IResult<In, Command> {
    let (rest, (start, path))
    = context("import", tuple((
        tag("import").preceded_by(bspace0(0)),
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
        parse_symbol.preceded_by(bspace0(0)),
        separated_list0(bspace1(2), parse_lambda_var(2)).preceded_by(bspace0(2)),
        alt((tag(":="), tag(":"))).preceded_by(bspace0(2)),
        parse_term(2)
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

pub fn parse_term(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let inner = alt((
            parse_term_let(margin),
            parse_term_binder(margin),
            parse_term_lambda(margin),
            parse_term_equal(margin),
            parse_term_simple_binder(margin),
            parse_term_application(margin)
        ));
        
        inner.preceded_by(bspace0(margin)).parse(input)
    }
}

fn parse_term_let(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, sym, ann, _, def, body))
        = context("let", tuple((
            tag("let").preceded_by(bspace0(margin)),
            parse_symbol.preceded_by(bspace0(margin + 2)),
            opt(pair(
                tag(":").preceded_by(bspace0(margin + 2)), 
                parse_term(margin + 2)
            )),
            tag(":=").preceded_by(bspace0(margin + 2)),
            parse_term(margin + 2),
            //tag(";").preceded_by(bspace0(margin)),
            parse_term(margin)
        )))(input)?;
    
        let def = DefineTerm {
            span: (start.location_offset(), def.span().1),
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
}

fn parse_term_binder(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, sym, _, ann, _, kind, body))
        = context("binder", tuple((
            tag("(").preceded_by(bspace0(margin)),
            parse_symbol.preceded_by(bspace0(margin)),
            tag(":").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(")").preceded_by(bspace0(margin)),
            alt((tag("->"), tag("=>"), tag("∩"))).preceded_by(bspace0(margin)),
            parse_term(margin)
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
}

fn parse_term_simple_binder(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (lhs, (kind, rhs)))
        = context("simple_binder", tuple((
            parse_term_spine(margin),
            alt((
                pair(tag("∩").preceded_by(bspace0(margin)),
                    parse_term_spine(margin)),
                pair(tag("=").preceded_by(bspace0(margin)),
                    parse_term_spine(margin)),
                pair(tag("->").preceded_by(bspace0(margin)),
                    parse_term(margin)),
                pair(tag("=>").preceded_by(bspace0(margin)),
                    parse_term(margin)),
            )).preceded_by(bspace0(margin))
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
}

fn parse_term_lambda(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, vars, _, body))
        = context("lambda", tuple((
            tag("λ").preceded_by(bspace0(margin)),
            separated_list1(bspace1(margin), parse_lambda_var(margin)).preceded_by(bspace0(margin)),
            tag(".").preceded_by(bspace0(margin)),
            parse_term(margin)
        )))(input)?;

        let span = (start.location_offset(), body.span().1);
        let body = body.boxed();
        let term = Term::Lambda { span, vars, body };

        Ok((rest, term))
    }
}

// atom "=[" term "]" term
fn parse_term_equal(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (lhs, _, ann, _, rhs))
        = context("equal", tuple((
            parse_term_application(margin),
            tag("=[").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag("]").preceded_by(bspace0(margin)),
            parse_term_application(margin)
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
}

fn parse_term_application(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, mut args)
        = context("application",
            separated_list1(bspace1(margin), parse_term_atom(margin)).preceded_by(bspace0(margin))
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
}

fn parse_term_spine(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, term) = alt((
            parse_term_variable_application(margin),
            parse_term_atom(margin),
        )).preceded_by(bspace0(margin))
            .parse(input)?;
        Ok((rest, term))
    }
}

fn parse_term_variable_application(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (head, tail))
        = context("variable_application",
            tuple((
                parse_term_variable.preceded_by(bspace0(margin)),
                opt(pair(bspace1(margin),
                    separated_list1(bspace1(margin), parse_term_atom(margin))
                        .preceded_by(bspace0(margin))
                ))
            ))
        )(input)?;

        let start = head.span().0;
        let term = if let Some((_, mut tail)) = tail {
            tail.drain(..)
                .fold(head, |acc, t| {
                    let span = (start, t.span().1);
                    Term::Apply { span, fun: acc.boxed(), arg: t.boxed() }
                })
        } else { head };

        Ok((rest, term))
    }
}

/*
    atom ::=
    | "[" term "," term (";" term)? "]" (".1" | ".2")*
    | "J" { term "," term "," term "," term "," term "," term } (".1" | ".2")*
    | "φ" term "{" term "," term "}" (".1" | ".2")*
    | "ϑ" { term } (".1" | ".2")*
    | "β" { term } (".1" | ".2")*
    | "δ" { term } (".1" | ".2")*
    | "(" term ")" (".1" | ".2")*
    | "_"
    | "?"
    | ident (".1" | ".2")*
    | "Set" (".1" | ".2")*
*/
fn parse_term_atom(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let inner = alt((
            parse_term_pair(margin),
            parse_term_equality_induction(margin),
            parse_term_cast(margin),
            parse_term_promote(margin),
            parse_term_refl(margin),
            parse_term_paren(margin),
            parse_term_omission,
            parse_term_hole,
            parse_term_variable,
            parse_set_keyword
        ));
        
        let (rest, (mut term, projs))
        = context("projection", tuple((
            inner.preceded_by(bspace0(margin)),
            many0(alt((
                tag(".1"),
                tag(".2")
            ))),
        )))(input)?;

        for proj in projs.iter() {
            let span = (term.span().0, proj.location_offset() + 1);
            term = match *proj.fragment() {
                ".1" => Term::Project { span, variant:1, body:term.boxed() },
                ".2" => Term::Project { span, variant:2, body:term.boxed() },
                _ => unreachable!()
            }
        }

        Ok((rest, term))
    }
}

// "_"
fn parse_term_omission(input: In) -> IResult<In, Term> {
    let (rest, result) = tag("_")(input)?;
    let span = (result.location_offset(), result.location_offset() + 1);
    let term = Term::Omission { span };
    Ok((rest, term))
}

// "?"
fn parse_term_hole(input: In) -> IResult<In, Term> {
    let (rest, result) = tag("?")(input)?;
    let span = (result.location_offset(), result.location_offset() + 1);
    let term = Term::Hole { span };
    Ok((rest, term))
}

// "[" term "," term (";" term)? "]"
fn parse_term_pair(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, lhs, _, rhs, ann, end))
        = context("pair", tuple((
            tag("[").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(",").preceded_by(bspace0(margin)),
            parse_term(margin),
            opt(pair(
                tag(";").preceded_by(bspace0(margin)), 
                parse_term(margin)
            )),
            tag("]").preceded_by(bspace0(margin))
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
}

// "𝜓" { term "," term } (".1" | ".2")?
fn parse_term_equality_induction(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, _, t1, _, t2, end))
        = context("induct", tuple((
            tag("𝜓").preceded_by(bspace0(margin)),
            tag("{").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(",").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag("}").preceded_by(bspace0(margin)),
        )))(input)?;

        let span = (start.location_offset(), end.location_offset());
        let term = Term::Subst {
            span,
            predicate: t2.boxed(),
            equation: t1.boxed(),
        };

        Ok((rest, term))
    }
}

// "φ" "{" term "," term "}"
fn parse_term_cast(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, _, witness, _, evidence, end))
        = context("cast", tuple((
            tag("φ").preceded_by(bspace0(margin)),
            tag("{").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(",").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag("}").preceded_by(bspace0(margin))
        )))(input)?;

        let span = (start.location_offset(), end.location_offset());
        let term = Term::Cast {
            span,
            witness: witness.boxed(),
            evidence: evidence.boxed()
        };

        Ok((rest, term))
    }
}

// "ϑ" (1 | 2) "{" term "," term "," term "}"
fn parse_term_promote(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, variant, _, t1, _, t2, _, t3, end))
        = context("promote", tuple((
            tag("ϑ"),
            alt((tag("1"), tag("2"))).preceded_by(bspace0(margin)),
            tag("{").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(",").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(",").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag("}").preceded_by(bspace0(margin))
        )))(input)?;

        let variant = if *variant == "1" { 1usize } else { 2 };
        let span = (start.location_offset(), end.location_offset());
        let term = Term::Promote {
            span,
            variant,
            equation: t1.boxed(),
            lhs: t2.boxed(),
            rhs: t3.boxed()
        };

        Ok((rest, term))
    }
}

// "β" { term }
fn parse_term_refl(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, _, term, end))
        = context("refl", tuple((
            tag("β").preceded_by(bspace0(margin)),
            tag("{").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag("}").preceded_by(bspace0(margin))
        )))(input)?;

        let span = (start.location_offset(), end.location_offset());
        let term = Term::Refl {
            span,
            input: term.boxed()
        };

        Ok((rest, term))
    }
}

// "δ" { term }
fn parse_term_separate(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (start, _, term, end))
        = context("separate", tuple((
            tag("δ").preceded_by(bspace0(margin)),
            tag("{").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag("}").preceded_by(bspace0(margin))
        )))(input)?;

        let span = (start.location_offset(), end.location_offset());
        let term = Term::Separate {
            span,
            equation: term.boxed()
        };

        Ok((rest, term))
    }
}

// "(" term ")"
fn parse_term_paren(margin: usize) -> impl FnMut(In) -> IResult<In, Term> {
    move |input| {
        let (rest, (_, term, _))
        = context("paren", tuple((
            tag("(").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(")").preceded_by(bspace0(margin))
        )))(input)?;

        Ok((rest, term))
    }
}

fn parse_term_variable(input: In) -> IResult<In, Term> {
    let (rest, id) = parse_ident(input)?;
    let term = Term::Variable { span: id.1, id: id.0 };
    Ok((rest, term))
}

fn parse_set_keyword(input: In) -> IResult<In, Term> {
    let (rest, keyword) = tag("Set")(input)?;
    let span = (keyword.location_offset(), keyword.location_offset() + keyword.len());
    let term = Term::Set { span };
    Ok((rest, term))
}

fn parse_parameter(margin: usize) -> impl FnMut(In) -> IResult<In, Parameter> {
    move |input| {
        let (rest, (mode, opn, (name, _), _, body, end)) = tuple((
            opt(tag("-")).preceded_by(bspace0(margin)),
            tag("(").preceded_by(bspace0(margin)),
            parse_symbol.preceded_by(bspace0(margin)),
            tag(":").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(")").preceded_by(bspace0(margin))
        ))(input)?;

        let start = mode.unwrap_or(opn).location_offset();
        let span = (start, end.location_offset() + 1);
        let mode = if mode.is_some() { Mode::Erased } else { Mode::Free };
        let parameter = Parameter {
            span,
            mode,
            name,
            body,
        };
        Ok((rest, parameter))
    }
}

fn parse_lambda_var(margin: usize) -> impl FnMut(In) -> IResult<In, LambdaVar> {
    move |input| {
        let parse_sym = pair(
            opt(tag("-")).preceded_by(bspace0(margin)),
            parse_symbol.preceded_by(bspace0(margin))
        ).map(|(is_erased, x)| {
            let mode = if is_erased.is_some() { Mode::Erased } else { Mode::Free };
            (mode, x.0, None)
        });

        let parse_ann = context("annotation", tuple((
            opt(tag("-")).preceded_by(bspace0(margin)),
            tag("(").preceded_by(bspace0(margin)),
            parse_symbol.preceded_by(bspace0(margin)),
            tag(":").preceded_by(bspace0(margin)),
            parse_term(margin),
            tag(")").preceded_by(bspace0(margin))
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

    let namespace: Vector<_> = iter.take(len - 1).map(|(x, _)| x).collect();
    // Safety: Parser guarantees there is at least one symbol
    let name = unsafe { iter.last().unwrap_unchecked().0 };

    // Disallow keywords
    match name.as_str() {
        "Set" | "module" | "import" | "let" => {
            let kind = BaseErrorKind::Expected(Expectation::Something);
            let location = LocatedSpan::new("fixme");
            let error = ErrorTree::Base { location, kind };
            Err(nom::Err::Error(error))
        }
        _ => {
            let module = (*MODULE.lock().unwrap()).unwrap();
            let id = Id { namespace, module, name };
            let result = (id, span);
        
            Ok((rest, result))
        }
    }
}

fn parse_symbol(input : In) -> IResult<In, (Symbol, Span)> {
    let (rest, symbol)
    = context("symbol", recognize(tuple((
        alpha1,
        separated_list1(tag("_"), alphanumeric0),
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
            opt(tuple((
                tag("--"),
                is_not("\n\r")
            ))),
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
            opt(tuple((
                tag("--"),
                is_not("\n\r")
            ))),
            line_ending,
            take_while(|c| c == ' ')
                .verify(move |s: &In| s.len() == margin),
            not(alt((line_ending, tag(" "))))
        )).map(|_| ())
    )))
}

fn empty_line(input: In) -> IResult<In, ()> {
    let (rest, _) = tuple((
        many0_count(tag(" ")),
        opt(tuple((
            tag("--"),
            is_not("\n\r")
        ))),
        line_ending,
    ))(input)?;
    Ok((rest, ()))
}

mod tests {
    use super::*;

    #[test]
    fn basic_test() {
        let input = r#"--        sdfgsfdggggsdfgsdfg sdfg sdfgser
        "#;
        let input = LocatedSpan::new(input);
        let output = empty_line(input);
        assert!(output.is_ok());
    }

}
