
use imbl::Vector;

use crate::term::*;
use crate::utility::*;
use crate::database::*;

#[derive(Debug, Clone)]
pub enum Sexp {
    Atom(Symbol),
    List(Vec<Sexp>)
}

impl Sexp {
    fn sym(&self) -> Option<Symbol> {
        match self {
            Sexp::Atom(x) => Some(*x),
            Sexp::List(_) => None,
        }
    }

    fn list(self) -> Option<Vec<Sexp>> {
        match self {
            Sexp::Atom(_) => None,
            Sexp::List(xs) => Some(xs),
        }
    }
}

pub fn parse(db: &mut Database, input: &str) -> Option<Module> {
    let words: Vec<_> = input.split_ascii_whitespace()
        .flat_map(|w| if w.starts_with(['(', ')']) { 
            let (x, y) = w.split_at(1);
            vec![x, y]
        } else {
            vec![w]
        })
        .flat_map(|w| if w.ends_with(['(', ')']) {
            let (x, y) = w.split_at(w.len() - 1);
            vec![x, y]
        } else {
            vec![w]
        })
        .filter(|w| !w.is_empty())
        .collect();
    let mut iter = words.iter().copied();
    let sexps = parse_list(&mut iter);
    to_module(db, sexps)
}

fn parse_sexp<'a>(input: &mut impl Iterator<Item=&'a str>) -> Option<Sexp> {
    match input.next() {
        Some("(") => {
            let inner = parse_list(input);
            Some(Sexp::List(inner))
        }
        Some(")") => None,
        Some(w) => Some(Sexp::Atom(Symbol::from(w))),
        None => None
    }
}

fn parse_list<'a>(input: &mut impl Iterator<Item=&'a str>) -> Vec<Sexp> {
    let mut result = vec![];
    while let Some(inner) = parse_sexp(input) {
        result.push(inner);
    }
    result
}

fn to_module(db: &mut Database, xs: Vec<Sexp>) -> Option<Module> {
    let mut decls = vec![];
    for x in xs.iter().cloned() {
        let xs = x.list()?;
        match xs.get(0)?.sym()?.as_ref() {
            "define" | "def" => {
                let name = xs.get(1)?.sym()?;
                let ty = xs.get(2)?.clone();
                let ty = to_term(db, Vector::new(), Sort::Type, ty)?;
                let body = xs.get(3)?.clone();
                let body = to_term(db, Vector::new(), Sort::Type, body)?;
                let decl = Decl { name, ty, body };
                decls.push(decl);
            }
            _ => return None
        }
    }
    let imports = vec![];
    let id = Id { namespace: Vector::new(), module: Symbol::from("FIXME"), name: Symbol::from("FIXME") };
    Some(Module { imports, id, decls })
}

fn to_term(db: &mut Database, mut ctx: Vector<Symbol>, sort: Sort, s: Sexp) -> Option<Term> {
    match s {
        Sexp::Atom(x) => {
            match x.as_ref() {
                "star" | "set" | "*" => {
                    let term = db.make_term(TermData::Star);
                    Some(term)
                }
                _ => {
                    let index = ctx.iter()
                        .rev()
                        .enumerate()
                        .find(|(_, s)| x == **s);
                    let term = if let Some((index, _)) = index {
                        let index: Index = index.into();
                        db.make_term(TermData::Bound { sort, index })
                    } else {
                        let id = Id { namespace: Vector::new(), module: Symbol::from("FIXME"), name: x };
                        db.make_term(TermData::Free { sort, id })
                    };
                    Some(term)
                }
            }
        }
        Sexp::List(xs) => {
            match xs.get(0)?.sym()?.as_ref() {
                "lam" | "lambda" | "\\" => {
                    let mode = xs.get(1)?.sym()?;
                    let mode = to_mode(mode)?;
                    let name = xs.get(2)?.sym()?;
                    let domain = xs.get(3)?.clone();
                    let domain = to_term(db, ctx.clone(), sort.promote(), domain)?;
                    ctx.push_back(name);
                    let body = xs.get(4)?.clone();
                    let body = to_term(db, ctx, sort, body)?;
                    let term = db.make_term(TermData::Lambda { sort, mode, name, domain, body });
                    Some(term)
                }
                "let" => {
                    let name = xs.get(1)?.sym()?;
                    let let_body = xs.get(2)?.clone();
                    let let_body = to_term(db, ctx.clone(), sort, let_body)?;
                    let body = xs.get(3)?.clone();
                    let body = to_term(db, ctx, sort, body)?;
                    let term = db.make_term(TermData::Let { sort, name, let_body, body });
                    Some(term)
                }
                "pi" | "fn" | "fun" | "function" => {
                    let mode = xs.get(1)?.sym()?;
                    let mode = to_mode(mode)?;
                    let name = xs.get(2)?.sym()?;
                    let domain = xs.get(3)?.clone();
                    let domain = to_term(db, ctx.clone(), sort.promote(), domain)?;
                    ctx.push_back(name);
                    let body = xs.get(4)?.clone();
                    let body = to_term(db, ctx, sort, body)?;
                    let term = db.make_term(TermData::Pi { sort, mode, name, domain, body });
                    Some(term)
                }
                "intersect" | "sect" => {
                    let name = xs.get(1)?.sym()?;
                    let first = xs.get(2)?.clone();
                    let first = to_term(db, ctx.clone(), sort, first)?;
                    let second = xs.get(3)?.clone();
                    let second = to_term(db, ctx, sort, second)?;
                    let term = db.make_term(TermData::Intersect { name, first, second });
                    Some(term)
                }
                "equality" | "eq" | "=" => {
                    let left = xs.get(1)?.clone();
                    let left = to_term(db, ctx.clone(), sort, left)?;
                    let right = xs.get(2)?.clone();
                    let right = to_term(db, ctx.clone(), sort, right)?;
                    let anno = xs.get(3)?.clone();
                    let anno = to_term(db, ctx, sort, anno)?;
                    let term = db.make_term(TermData::Equality { left, right, anno });
                    Some(term)
                }
                "project" | "proj" => {
                    let variant = xs.get(1)?.sym()?;
                    let variant = to_variant(variant)?;
                    let body = xs.get(2)?.clone();
                    let body = to_term(db, ctx, sort, body)?;
                    let term = db.make_term(TermData::Project { variant, body });
                    Some(term)
                }
                "separate" | "sep" | "delta" => {
                    let equation = xs.get(1)?.clone();
                    let equation = to_term(db, ctx, sort, equation)?;
                    let term = db.make_term(TermData::Separate { equation });
                    Some(term)
                }
                "refl" | "rfl" | "beta" => {
                    let input = xs.get(1)?.clone();
                    let input = to_term(db, ctx, sort, input)?;
                    let term = db.make_term(TermData::Refl { input });
                    Some(term)
                }
                "cast" | "phi" => {
                    let input = xs.get(1)?.clone();
                    let input = to_term(db, ctx.clone(), sort, input)?;
                    let witness = xs.get(2)?.clone();
                    let witness = to_term(db, ctx.clone(), sort, witness)?;
                    let evidence = xs.get(3)?.clone();
                    let evidence = to_term(db, ctx, sort, evidence)?;
                    let term = db.make_term(TermData::Cast { input, witness, evidence });
                    Some(term)
                }
                "promote" | "pr" | "theta" => {
                    let equation = xs.get(1)?.clone();
                    let equation = to_term(db, ctx, sort, equation)?;
                    let term = db.make_term(TermData::Promote { equation });
                    Some(term)
                }
                "subst" | "psi" => {
                    todo!()
                }
                "apply" | "app" | "@" => {
                    let mode = xs.get(1)?.sym()?;
                    let mode = to_mode(mode)?;
                    let fun = xs.get(2)?.clone();
                    let fun = to_term(db, ctx.clone(), sort, fun)?;
                    let arg = xs.get(3)?.clone();
                    let arg = to_term(db, ctx, sort, arg)?;
                    let term = db.make_term(TermData::Apply { sort, mode, fun, arg });
                    Some(term)
                }
                _ => None
            }
        }
    }
}

fn to_mode(s: Symbol) -> Option<Mode> {
    match s.as_ref() {
        "free" | "w" => Some(Mode::Free),
        "type" | "t" => Some(Mode::TypeLevel),
        "erased" | "0" => Some(Mode::Erased),
        _ => None
    }
}

fn to_variant(s: Symbol) -> Option<usize> {
    match s.as_ref() {
        "one" | "1" => Some(1),
        "two" | "2" => Some(2),
        _ => None
    }
}
