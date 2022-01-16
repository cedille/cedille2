// TODO: Modify this file so that all of the rule productions use an Extract combinator
// TODO: Centralize any of the possible panics in the Extract combinators

use pest::Parser;
use pest::iterators::{Pair, Pairs};
use pest::error::Error;

use crate::common::*;
use crate::lang::syntax::*;

type Span = (usize, usize);

#[derive(Parser)]
#[grammar = "lang/grammar.pest"]
pub struct CedilleParser;

pub fn parse(input : &str) -> Result<Pairs<Rule>, Error<Rule>> {
    CedilleParser::parse(Rule::main, input)
}

trait Extract {
    fn required<T, R>(&mut self, f: R) -> T
        where R: Fn(Pair<Rule>) -> T;
    fn optional<T, R>(&mut self, rule: Rule, f: R) -> Option<T>
        where R: Fn(Pair<Rule>) -> T;
    fn flag(&mut self, rule: Rule) -> bool;
    fn list<T, R>(&mut self, rule: Rule, f: R) -> Vec<T>
        where R: Fn(Pair<Rule>) -> T;
    fn variant_list<T, R>(&mut self, f: R) -> Vec<T>
        where R: Fn(Pair<Rule>) -> Option<T>;
    fn variant<T, R>(&mut self, f: R) -> T
        where R: Fn(Pair<Rule>) -> Option<T>;
}

impl<'a> Extract for Pairs<'a, Rule> {
    fn required<T, R>(&mut self, f: R) -> T
    where R: Fn(Pair<Rule>) -> T {
        f(self.next().unwrap())
    }

    fn optional<T, R>(&mut self, rule: Rule, f: R) -> Option<T>
    where R: Fn(Pair<Rule>) -> T {
        let mut result = None;
        if let Some(p) = self.peek() {
            if p.as_rule() == rule {
                self.next();
                result = Some(f(p));
            }
        }
        result
    }
    
    fn flag(&mut self, rule: Rule) -> bool {
        if let Some(p) = self.peek() {
            if p.as_rule() == rule { 
                self.next();
                return true;
            }
        }
        false
    }

    fn list<T, R>(&mut self, rule: Rule, f: R) -> Vec<T>
    where R: Fn(Pair<Rule>) -> T {
        let mut result = vec![];
        while let Some(p) = self.peek() {
            if p.as_rule() != rule { break; }
            self.next();
            result.push(f(p));
        }
        result
    }

    fn variant_list<T, R>(&mut self, f: R) -> Vec<T>
    where R: Fn(Pair<Rule>) -> Option<T> {
        let mut result = vec![];
        while let Some(p) = self.peek() {
            if let Some(t) = f(p) {
                self.next();
                result.push(t);
            } else { 
                break;
            }
        }
        result
    }

    fn variant<T, R>(&mut self, f: R) -> T
    where R: Fn(Pair<Rule>) -> Option<T> {
        let p = self.next().unwrap();
        f(p).unwrap()
    }
}

pub fn module(pairs: Pairs<Rule>) -> Module {
    fn decl(decl: Pair<Rule>) -> Option<Decl> {
        match decl.as_rule() {
            Rule::define_term => Some(Decl::Term(define_term(decl))),
            Rule::define_type => Some(Decl::Type(define_type(decl))),
            Rule::define_kind => Some(Decl::Kind(define_kind(decl))),
            Rule::define_datatype => Some(Decl::Datatype(define_datatype(decl))),
            Rule::import => Some(Decl::Import(import(decl))),
            _ => None
        }
    }
    fn module_header(header: Pair<Rule>) -> (Span, Vec<Parameter>) {
        let mut inner = header.into_inner();
        let path = inner.required(path);
        let params = inner.list(Rule::param, param);
        (path, params)
    }
    let mut pairs = pairs;
    let header_imports = pairs.list(Rule::import, import);
    let (path, params) = pairs.required(module_header);
    let decls = pairs.variant_list(decl);
    Module { header_imports, path, decls, params }
}

fn import(import: Pair<Rule>) -> Import {
    let span = span(import.as_span());
    let mut inner = import.into_inner();
    let public = inner.flag(Rule::public);
    let path = inner.required(path);
    let namespace = inner.optional(Rule::id, id);
    let args = inner.list(Rule::import_argument, import_argument);
    Import { span, public, path, namespace, args }
}

fn import_argument(pairs: Pair<Rule>) -> (Mode, Term) {
    let mut inner = pairs.into_inner();
    // An import argument must have at least one rule
    let p = inner.peek().unwrap();
    if p.as_rule() == Rule::type_ {
        let type_ = inner.required(type_);
        (Mode::Erased, type_)
    } else {
        let erased = inner.flag(Rule::erased_op);
        let mode = if erased { Mode::Erased } else { Mode::Free };
        let term = inner.required(term);
        (mode, term)
    }
}

fn param(pairs: Pair<Rule>) -> Parameter {
    fn relevant_param(param: Pair<Rule>) -> Parameter {
        let span = span(param.as_span());
        let mut inner = param.into_inner();
        let name = inner.required(id);
        inner.variant(|p| match p.as_rule() {
            Rule::kind => {
                let mode = Mode::Erased;
                let body = kind(p);
                Some(Parameter { span, name, mode, body })
            },
            Rule::type_ => {
                let mode = Mode::Free;
                let body = type_(p);
                Some(Parameter { span, name, mode, body })
            },
            _ => None
        })
    }
    fn erased_param(param: Pair<Rule>) -> Parameter {
        let span = span(param.as_span());
        let mut inner = param.into_inner();
        let name = inner.required(id);
        let mode = Mode::Erased;
        let body = inner.required(type_);
        Parameter { span, name, mode, body }
    }
    let mut inner = pairs.into_inner();
    inner.variant(|p| match p.as_rule() {
        Rule::relevant_param => Some(relevant_param(p)),
        Rule::erased_param => Some(erased_param(p)),
        _ => None
    })
}

fn define_term(def: Pair<Rule>) -> DefineTerm {
    let span = span(def.as_span());
    let mut inner = def.into_inner();
    let name = inner.required(id);
    let anno = inner.optional(Rule::type_, type_).map(Box::new);
    let body = Box::new(inner.required(term));
    DefineTerm { span, name, anno, body }
}

fn define_type(def: Pair<Rule>) -> DefineTerm {
    let span = span(def.as_span());
    let mut inner = def.into_inner();
    let name = inner.required(id);
    let anno = inner.optional(Rule::kind, kind).map(Box::new);
    let body = Box::new(inner.required(type_));
    DefineTerm { span, name, anno, body }
}

fn define_kind(def: Pair<Rule>) -> DefineKind {
    let span = span(def.as_span());
    let mut inner = def.into_inner();
    let name = inner.required(id);
    let args = inner.list(Rule::kind_arg, kind_arg);
    let body = Box::new(inner.required(kind));
    DefineKind { span, name, args, body }
}

fn define_datatype(def: Pair<Rule>) -> DefineDatatype {
    fn ctor(ctor: Pair<Rule>) -> Constructor {
        let mut inner = ctor.into_inner();
        let name = inner.required(id);
        let anno = inner.required(type_);
        Constructor { name, anno }
    }
    fn ctors(ctors: Pair<Rule>) -> Vec<Constructor> {
        let mut inner = ctors.into_inner();
        inner.list(Rule::ctor, ctor)
    }
    let span = span(def.as_span());
    let mut inner = def.into_inner();
    let name = inner.required(id);
    let params = inner.list(Rule::param, param);
    let kind = Box::new(inner.required(kind));
    let ctors = inner.required(ctors);
    DefineDatatype { span, name, params, kind, ctors }
}

fn term(pairs: Pair<Rule>) -> Term {
    let mut binders = vec![];
    let mut body = None;
    for p in pairs.into_inner() {
        match p.as_rule() {
            Rule::term_lambda
            | Rule::term_erased_lambda
            | Rule::term_let
            | Rule::term_erased_let
            | Rule::term_rewrite
            | Rule::term_annotate
            => binders.push(p),
            Rule::term_application => body = Some(term_application(p)),
            _ => unreachable!()
        }
    }
    // Terms must have a body
    let body = body.unwrap();
    binders.drain(..).rev().fold(body, term_binder)
}

fn term_binder(body: Term, binder: Pair<Rule>) -> Term {
    fn term_lambda_relevant_var(var: Pair<Rule>) -> LambdaVar {
        let mut inner = var.into_inner();
        let mode = Mode::Free;
        let var = inner.required(bound_id);
        let anno = inner.optional(Rule::type_, type_);
        LambdaVar { mode, var, anno }
    }
    fn term_lambda_erased_var(var: Pair<Rule>) -> LambdaVar {
        let mut inner = var.into_inner();
        let mode = Mode::Erased;
        let var = inner.required(bound_id);
        let anno =
            if let Some(ty) = inner.optional(Rule::type_, type_) { Some(ty) }
            else { inner.optional(Rule::kind, kind) };
        LambdaVar { mode, var, anno }
    }
    fn num(num: Pair<Rule>) -> usize {
        let num = num.as_str().parse::<usize>();
        // The grammar guarantees this is a usize
        num.ok().unwrap()
    }
    let (binder_start, _) = span(binder.as_span());
    let (_, binder_end) = body.span();
    let span = (binder_start, binder_end);
    let sort = Sort::Term;
    let body = Box::new(body);
    let rule = binder.as_rule();
    let mut inner = binder.into_inner();
    match rule {
        Rule::term_lambda => {
            let vars = inner.variant_list(|p| match p.as_rule() {
                Rule::term_lambda_relevant_var => Some(term_lambda_relevant_var(p)),
                Rule::term_lambda_erased_var => Some(term_lambda_erased_var(p)),
                _ => None
            });
            Term::Lambda { span, sort, vars, body }
        }
        Rule::term_erased_lambda => {
            let mode = Mode::Erased;
            let var= inner.required(bound_id);
            if let Some(k) = inner.optional(Rule::kind, kind) {
                let anno = Some(k);
                let var = LambdaVar { mode, var, anno };
                Term::Lambda { span, sort, vars: vec![var], body }
            } else {
                let anno = inner.optional(Rule::type_, type_);
                let var = LambdaVar { mode, var, anno };
                Term::Lambda { span, sort, vars: vec![var], body }
            }
        },
        Rule::term_let | Rule::term_erased_let => {
            let mode = if rule == Rule::term_let { Mode::Free } else { Mode::Erased };
            if inner.peek().map(|p| p.as_rule()) == Some(Rule::define_type) {
                let def = inner.required(define_type);
                Term::Let { span, mode, sort, def, body }
            } else {
                let def = inner.required(define_term);
                Term::Let { span, mode, sort, def, body }
            }
        },
        Rule::term_rewrite => {
            let reduce = inner.flag(Rule::reduce);
            let occurrence = inner.optional(Rule::num, num);
            let equation = Box::new(inner.required(term_atom));
            let guide = inner.optional(Rule::guide, guide);
            Term::Rewrite { span, reduce, occurrence, equation, guide, body }
        },
        Rule::term_annotate => {
            let anno = Box::new(inner.required(type_));
            Term::Annotate { span, anno, body }
        },
        _ => unreachable!()
    }
}

fn term_application(pairs: Pair<Rule>) -> Term {
    let mut iter = pairs.into_inner();
    let mut result = iter.required(term_atom);
    let (mut apply_type, sort) = (ApplyType::Free, Sort::Term);
    for p in iter {
        let outer_span = span(p.as_span());
        match p.as_rule() {
            Rule::erased_op => apply_type = ApplyType::TermErased,
            Rule::term_atom | Rule::term => {
                let fun = Box::new(result);
                let arg = Box::new(
                    if p.as_rule() == Rule::term { term(p) }
                    else { term_atom(p) });
                let span = (outer_span.0, arg.span().1);
                result = Term::Apply { span, apply_type, sort, fun, arg };
                apply_type = ApplyType::Free;
            },
            Rule::type_atom | Rule::type_ => {
                let fun = Box::new(result);
                let arg = Box::new(
                    if p.as_rule() == Rule::type_ { type_(p) }
                    else { type_atom(p) });
                let apply_type = ApplyType::TypeErased;
                let span = (outer_span.0, arg.span().1);
                result = Term::Apply { span, apply_type, sort, fun, arg};
            }
            _ => unreachable!()
        };
    }
    result
}

fn term_atom(atom: Pair<Rule>) -> Term {
    fn case_arg(arg: Pair<Rule>) -> CaseArg {
        let mut inner = arg.into_inner();
        let type_op = inner.flag(Rule::type_op);
        let erased_op = inner.flag(Rule::erased_op);
        let id = inner.required(id);
        if type_op { CaseArg::Type(id) }
        else if erased_op { CaseArg::Erased(id) }
        else { CaseArg::Free(id) }
    }
    fn case(case: Pair<Rule>) -> Case {
        let span = span(case.as_span());
        let mut inner = case.into_inner();
        let id = inner.required(qual_id);
        let args = inner.list(Rule::case_arg, case_arg);
        let body = inner.required(term);
        Case { span, id, args, body }
    }
    fn cases(cases: Pair<Rule>) -> Vec<Case> {
        let mut inner = cases.into_inner();
        inner.list(Rule::case, case)
    }
    fn proj(proj: Pair<Rule>) -> (Span, usize) {
        let span = span(proj.as_span());
        let v = proj.as_str().trim_start_matches('.')
            .parse::<usize>()
            .ok().unwrap();
        (span, v)
    }
    let mut inner = atom.into_inner();

    let term = inner.variant(|p| {
        let span = span(p.as_span());
        match p.as_rule() {
            Rule::term_intersection => {
                let mut inner = p.into_inner();
                let first = Box::new(inner.required(term));
                let second = Box::new(inner.required(term));
                Some(Term::Intersect { span, first, second })
            },
            Rule::term_refl => {
                let mut inner = p.into_inner();
                let guide = inner.optional(Rule::term_guide, term_guide).map(Box::new);
                let erasure = inner.optional(Rule::term, term).map(Box::new);
                Some(Term::Reflexivity { span, guide, erasure })
            },
            Rule::term_cast => {
                let mut inner = p.into_inner();
                let equation = Box::new(inner.required(term_atom));
                let input = inner.required(term_application);
                let input = Box::new(input);
                let erasure = Box::new(inner.required(term));
                Some(Term::Cast { span, equation, input, erasure })
            },
            Rule::term_induction => {
                let mut inner = p.into_inner();
                let var = inner.required(id);
                let inductee = inner.required(term_application);
                let inductee = Box::new(inductee);
                let motive = inner.optional(Rule::type_, type_).map(Box::new);
                let cases = inner.required(cases);
                Some(Term::Induct { span, var, inductee, motive, cases })
            },
            Rule::term_match => {
                let mut inner = p.into_inner();
                // Detect deprecated mu prime token header
                if inner.flag(Rule::mu_prime) {
                    println!("Warning, μ' is deprecated.");
                }
                let guide = inner.optional(Rule::term_guide, term_guide).map(Box::new);
                let matched = inner.required(term_application);
                let matched = Box::new(matched);
                let motive = inner.optional(Rule::type_, type_).map(Box::new);
                let cases = inner.required(cases);
                Some(Term::Match { span, guide, matched, motive, cases })
            },
            Rule::term_separate => {
                let mut inner = p.into_inner();
                let anno = inner.optional(Rule::type_, type_).map(Box::new);
                let equation = Box::new(inner.required(term));
                Some(Term::Separate { span, anno, equation })
            },
            Rule::term_symmetry => {
                let mut inner = p.into_inner();
                let equation = Box::new(inner.required(term_atom));
                Some(Term::Symmetry { span, equation })
            },
            Rule::term => Some(term(p)),
            Rule::hole => Some(Term::Hole { span, sort: Sort::Term }),
            Rule::qual_id => {
                let id = qual_id(p);
                let sort = Sort::Term;
                Some(Term::Variable { span, sort, id })
            },
            _ => None
        }
    });

    let mut projs = inner.list(Rule::proj, proj);
    projs.drain(..).fold(term, |acc, (span, variant)| {
        let body = Box::new(acc);
        let span = (body.span().0, span.1);
        Term::Project { span, variant, body }
    })
}

fn term_guide(pairs: Pair<Rule>) -> Term {
    // A term guide consists of exactly one term
    let inner = pairs.into_inner().next().unwrap();
    term(inner)
}

fn guide(guide: Pair<Rule>) -> RewriteGuide {
    let mut inner = guide.into_inner();
    let name = inner.required(id);
    let hint = inner.optional(Rule::term_guide, term_guide).map(Box::new);
    let equation = Box::new(inner.required(type_));
    RewriteGuide { name, hint, equation }
}

fn type_(pairs: Pair<Rule>) -> Term {
    let mut binders = vec![];
    let mut body = None;
    for p in pairs.into_inner() {
        match p.as_rule() {
            Rule::type_forall
            | Rule::type_erased_forall
            | Rule::type_lambda
            | Rule::type_intersection
            | Rule::type_let
            => binders.push(p),
            Rule::type_body => body = Some(type_body(p)),
            _ => unreachable!()
        }
    }
    // Types must have a body
    let body = body.unwrap();
    binders.drain(..).rev().fold(body, type_binder)
}

fn type_binder(body: Term, binder: Pair<Rule>) -> Term {
    fn type_lambda_var(var: Pair<Rule>) -> LambdaVar {
        let mut inner = var.into_inner();
        let mode = Mode::Free;
        let var = inner.required(bound_id);
        let anno =
            if let Some(ty) = inner.optional(Rule::kind, kind) { Some(ty) }
            else { inner.optional(Rule::type_, type_) };
        LambdaVar { mode, var, anno }
    }
    let (binder_start, _) = span(binder.as_span());
    let (_, binder_end) = body.span();
    let span = (binder_start, binder_end);
    let body = Box::new(body);
    let rule = binder.as_rule();
    let mut inner = binder.into_inner();
    let sort = Sort::Type;
    match rule {
        Rule::type_forall => {
            let mode = Mode::Free;
            let var = Some(inner.required(id));
            let domain = Box::new(inner.required(type_));
            Term::Pi { span, mode, sort, var, domain, body }
        },
        Rule::type_erased_forall => {
            let mode = Mode::Erased;
            let var = Some(inner.required(id));
            if inner.peek().map(|p| p.as_rule()) == Some(Rule::kind) {
                let domain = Box::new(inner.required(kind));
                Term::Pi { span, mode, sort, var, domain, body }
            } else {
                let domain = Box::new(inner.required(type_));
                Term::Pi { span, mode, sort, var, domain, body }
            }
        },
        Rule::type_lambda => {
            let vars = inner.list(Rule::type_lambda_var, type_lambda_var);
            Term::Lambda { span, sort, vars, body }
        },
        Rule::type_intersection => {
            let var = inner.required(bound_id);
            let first = Box::new(inner.required(type_));
            let second = body;
            Term::IntersectType { span, var, first, second }
        },
        Rule::type_let => {
            let mode = Mode::Free;
            if inner.peek().map(|p| p.as_rule()) == Some(Rule::define_type) {
                let def = inner.required(define_type);
                Term::Let { span, mode, sort, def, body }
            } else {
                let def = inner.required(define_term);
                Term::Let { span, mode, sort, def, body }
            }
        },
        _ => unreachable!()
    }
}

fn type_body(pairs: Pair<Rule>) -> Term {
    let mut inner = pairs.into_inner();
    let mut result = inner.required(type_atom);
    let mut outer_span = result.span();
    let sort = Sort::Type;
    while let Some(p) = inner.next() {
        let inner_span = span(p.as_span());
        match p.as_rule() {
            Rule::erased_arrow | Rule::arrow  => {
                let mode = if p.as_rule() == Rule::arrow { Mode::Free } else { Mode::Erased };
                let var = None;
                let domain = Box::new(result);
                let body = Box::new(inner.required(type_));
                let span = (outer_span.0, body.span().1);
                outer_span = inner_span;
                result = Term::Pi { span, mode, sort, var, domain, body }
            },
            Rule::type_atom => {
                let fun = Box::new(result);
                let arg = Box::new(type_atom(p));
                let span = (outer_span.0, arg.span().1);
                let apply_type = ApplyType::TypeErased;
                result = Term::Apply { span, apply_type, sort, fun, arg }
            },
            Rule::term_atom => {
                let fun = Box::new(result);
                let arg = Box::new(term_atom(p));
                let span = (outer_span.0, arg.span().1);
                let apply_type = ApplyType::Free;
                result = Term::Apply { span, apply_type, sort, fun, arg }
            },
            _ => unreachable!()
        }
    }
    result
}

fn type_atom(pairs: Pair<Rule>) -> Term {
    let mut inner = pairs.into_inner();
    let p = inner.next().unwrap();
    let span = span(p.as_span());
    match p.as_rule() {
        Rule::term => {
            let left = Box::new(term(p));
            let right = Box::new(inner.required(term));
            Term::Equality { span, left, right }
        },
        Rule::type_ => type_(p),
        Rule::hole => Term::Hole { span, sort: Sort::Type },
        Rule::qual_id => {
            let sort = Sort::Type;
            let id = qual_id(p);
            Term::Variable { span, sort, id }
        },
        _ => unreachable!()
    }
}

fn kind(pairs: Pair<Rule>) -> Term {
    fn kind_binder(body: Term, pairs: Pair<Rule>) -> Term {
        let body = Box::new(body);
        let mut inner = pairs.into_inner();
        let var = inner.required(bound_id);
        let p = inner.next().unwrap();
        let outer_span = span(p.as_span());
        let (mode, sort) = (Mode::Free, Sort::Kind);
        if p.as_rule() == Rule::kind {
            let domain = Box::new(kind(p));
            let span = (outer_span.0, body.span().1);
            Term::Pi { span, mode, sort, var, domain, body }
        } else {
            let domain = Box::new(type_(p));
            let span = (outer_span.0, body.span().1);
            Term::Pi { span, mode, sort, var, domain, body }
        }
    }
    fn kind_atom(pairs: Pair<Rule>) -> Term {
        let mut inner = pairs.into_inner();
        let p = inner.next().unwrap();
        let full_span = span(p.as_span());
        let sort = Sort::Kind;
        match p.as_rule() {
            Rule::kind => kind(p),
            Rule::star => Term::Star { span: full_span },
            Rule::qual_kind_id => {
                let id = qual_id(p);
                let head = Term::Variable { span: full_span, sort, id };
                let mut args = inner.variant_list(|p| {
                    let span = span(p.as_span());
                    match p.as_rule() {
                        Rule::type_atom => Some((type_(p), ApplyType::TypeErased, span)),
                        Rule::term_atom => Some((term(p), ApplyType::TermErased, span)),
                        _ => None
                    }});
                // TODO: fix the spans here
                args.drain(..).fold(head, |acc, (arg, apply_type, span)| {
                    let (fun, arg) = (Box::new(acc), Box::new(arg));
                    let span = (full_span.0, span.1);
                    Term::Apply { span, apply_type, sort, fun, arg }
                })
            },
            _ => unreachable!()
        }
    }
    fn type_application(body: Term, pairs: Pair<Rule>) -> Term {
        let outer_span = span(pairs.as_span());
        let var = None;
        let mut inner = pairs.into_inner();
        // A type application must be headed by a type atom
        let mut result = inner.required(type_atom);
        let (mode, sort) = (Mode::Free, Sort::Kind);
        for p in inner {
            let span = span(p.as_span());
            match p.as_rule() {
                Rule::type_atom => {
                    let fun = Box::new(result);
                    let arg = Box::new(type_atom(p));
                    let apply_type = ApplyType::TypeErased;
                    result = Term::Apply { span, apply_type, sort, fun, arg }
                },
                Rule::term_atom => {
                    let fun = Box::new(result);
                    let arg = Box::new(term_atom(p));
                    let apply_type = ApplyType::Free;
                    result = Term::Apply { span, apply_type, sort, fun, arg }
                },
                _ => unreachable!()
            }
        }
        let span = (outer_span.0, body.span().1);
        let domain = Box::new(result);
        let body = Box::new(body);
        Term::Pi { span, mode, sort, var, domain, body }
    }
    fn rec(pairs: Pairs<Rule>) -> Term {
        let mut iter = pairs;
        if let Some(p) = iter.next() {
            let outer_span = span(p.as_span());
            match p.as_rule() {
                Rule::kind_binder => {
                    let body = rec(iter);
                    kind_binder(body, p)
                },
                Rule::type_application => {
                    let body = rec(iter);
                    type_application(body, p)
                },
                Rule::kind_atom => {
                    let mut result = kind_atom(p);
                    // The remaining rules must be `kind`
                    for p2 in iter {
                        let (mode, sort) = (Mode::Free, Sort::Kind);
                        let var = None;
                        let domain = Box::new(result);
                        let body = Box::new(kind(p2));
                        let span = (outer_span.0, body.span().1);
                        result = Term::Pi { span, mode, sort, var, domain, body };
                    }
                    result
                },
                _ => unreachable!()
            }
        } else { unreachable!() }
    }
    rec(pairs.into_inner())
}

fn kind_arg(pairs: Pair<Rule>) -> KindArg {
    let mut inner = pairs.into_inner();
    let name = inner.required(id);
    if inner.peek().map(|p| p.as_rule()) == Some(Rule::kind) {
        let body = inner.required(kind);
        KindArg { name, body }
    } else {
        let body = inner.required(type_);
        KindArg { name, body }
    }
}

fn path(pairs: Pair<Rule>) -> Span {
    span(pairs.as_span())
}

fn bound_id(pairs: Pair<Rule>) -> Option<Symbol> {
    let mut inner = pairs.into_inner();
    inner.variant(|p| match p.as_rule() {
        | Rule::id => Some(Some(id(p))),
        | Rule::omission => Some(None),
        | _ => None
    })
}

fn id(id: Pair<Rule>) -> Symbol {
    Symbol::from(id.as_str())
}

fn qual_id(pairs: Pair<Rule>) -> Id {
    let mut inner = pairs.into_inner();
    let mut namespace = inner.list(Rule::id, id);
    // Grammar guarantees there is at least one id
    let name = namespace.pop().unwrap();
    Id { namespace, name }
}

fn span(span: pest::Span) -> Span {
    (span.start(), span.end())
}
