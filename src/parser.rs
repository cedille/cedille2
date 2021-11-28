// TODO: Modify this file so that all of the rule productions use an Extract combinator
// TODO: Centralize any of the possible panics in the Extract combinators
// TODO: Switch to a two phased extraction so that we aren't cloning the pairs parse tree

use pest::Parser;
use pest::iterators::{Pair, Pairs};
use pest::error::Error;
use internment::Intern;

use crate::syntax::*;
use crate::database::*;

type Symbol = Intern<String>;
type Span = (usize, usize);
type Data<'a> = (&'a str, Context);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Context {
    module: Symbol,
    decl: Option<Symbol>,
}

impl Context {
    pub fn new(module: Symbol) -> Context {
        Context { module, decl:None }
    }
}

#[derive(Parser)]
#[grammar = "cedille.pest"]
pub struct CedilleParser;

pub fn parse(input : &str) -> Result<Pairs<Rule>, Error<Rule>> {
    CedilleParser::parse(Rule::main, input)
}

trait Extract {
    fn required<D, T, R>(&mut self, data: D, f: R) -> T
        where R: Fn(D, Pair<Rule>) -> T;
    fn optional<D, T, R>(&mut self, data: D, rule: Rule, f: R) -> Option<T>
        where R: Fn(D, Pair<Rule>) -> T;
    fn flag(&mut self, rule: Rule) -> bool;
    fn list<D: Clone, T, R>(&mut self, data: D, rule: Rule, f: R) -> Vec<T>
        where R: Fn(D, Pair<Rule>) -> T;
    fn variant_list<D: Clone, T, R>(&mut self, data: D, f: R) -> Vec<T>
        where R: Fn(D, Pair<Rule>) -> Option<T>;
    fn variant<D, T, R>(&mut self, data: D, f: R) -> T
        where R: Fn(D, Pair<Rule>) -> Option<T>;
}

impl<'a> Extract for Pairs<'a, Rule> {
    fn required<D, T, R>(&mut self, data: D, f: R) -> T
    where R: Fn(D, Pair<Rule>) -> T {
        f(data, self.next().unwrap())
    }

    fn optional<D, T, R>(&mut self, data: D, rule: Rule, f: R) -> Option<T>
    where R: Fn(D, Pair<Rule>) -> T {
        let mut result = None;
        if let Some(p) = self.peek() {
            if p.as_rule() == rule {
                self.next();
                result = Some(f(data, p));
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

    fn list<D: Clone, T, R>(&mut self, data: D, rule: Rule, f: R) -> Vec<T>
    where R: Fn(D, Pair<Rule>) -> T {
        let mut result = vec![];
        while let Some(p) = self.peek() {
            if p.as_rule() != rule { break; }
            self.next();
            result.push(f(data.clone(), p));
        }
        result
    }

    fn variant_list<D: Clone, T, R>(&mut self, data: D, f: R) -> Vec<T>
    where R: Fn(D, Pair<Rule>) -> Option<T> {
        let mut result = vec![];
        while let Some(p) = self.peek() {
            if let Some(t) = f(data.clone(), p) {
                self.next();
                result.push(t);
            } else { 
                break;
            }
        }
        result
    }

    fn variant<D, T, R>(&mut self, data: D, f: R) -> T
    where R: Fn(D, Pair<Rule>) -> Option<T> {
        let p = self.next().unwrap();
        f(data, p).unwrap()
    }
}

pub fn extract_imports(mut pairs: Pairs<Rule>) -> Vec<Span> {
    let import_closure = |_:(), p:Pair<Rule>| {
        let mut inner = p.into_inner();
        inner.optional((), Rule::public, |_, _| { });
        inner.required((), |_, p| span(p.as_span()))
    };
    let mut imports = pairs.list((), Rule::import, import_closure);
    pairs.required((), |_, _| { }); // Skip module_header
    let mut decl_imports = pairs.variant_list((), |_, p|
        match p.as_rule() {
        | Rule::import => Some(Some(import_closure((), p))),
        | Rule::define_term | Rule::define_type | Rule::define_kind | Rule::define_datatype
            => Some(None),
        | _ => None
    });
    let decl_imports = decl_imports.drain(..).flatten();
    imports.extend(decl_imports);
    imports
}

pub fn module(data: Data, pairs: Pairs<Rule>) -> Module {
    enum DeclOrImport {
        Decl(Decl),
        Import(Import)
    }
    fn split(mut decls_and_imports: Vec<DeclOrImport>) -> (Vec<Decl>, Vec<Import>) {
        let (mut decls, mut imports) = (vec![], vec![]);
        for x in decls_and_imports.drain(..) {
            match x {
                DeclOrImport::Import(import) => imports.push(import),
                DeclOrImport::Decl(decl) => decls.push(decl)
            }
        }
        (decls, imports)
    }
    fn decl(data: Data, decl: Pair<Rule>) -> Option<DeclOrImport> {
        match decl.as_rule() {
            Rule::define_term => Some(DeclOrImport::Decl(Decl::Term(define_term(data, decl)))),
            Rule::define_type => Some(DeclOrImport::Decl(Decl::Type(define_type(data, decl)))),
            Rule::define_kind => Some(DeclOrImport::Decl(Decl::Kind(define_kind(data, decl)))),
            Rule::define_datatype => Some(DeclOrImport::Decl(Decl::Datatype(define_datatype(data, decl)))),
            Rule::import => Some(DeclOrImport::Import(import(data, decl))),
            _ => None
        }
    }
    fn module_header(data: Data, header: Pair<Rule>) -> (Id, Vec<Parameter>) {
        let mut inner = header.into_inner();
        let qual_id = inner.required(data, qual_id);
        let params = inner.list(data, Rule::param, param);
        (qual_id, params)
    }
    let mut pairs = pairs;
    let mut imports = pairs.list(data, Rule::import, import);
    let (id, params) = pairs.required(data, module_header);
    let (decls, mut decl_imports) = split(pairs.variant_list(data, decl));
    imports.append(&mut decl_imports);
    Module { imports, id, decls, params }
}

fn import(data: Data, import: Pair<Rule>) -> Import {
    let span = span(import.as_span());
    let mut inner = import.into_inner();
    let public = inner.flag(Rule::public);
    let path = inner.required(data, path);
    let namespace = inner.optional(data, Rule::id, id);
    let args = inner.list(data, Rule::import_argument, import_argument);
    Import { span, public, path, namespace, args }
}

fn import_argument(data: Data, pairs: Pair<Rule>) -> ImportArg {
    let mut inner = pairs.into_inner();
    // An import argument must have at least one rule
    let p = inner.peek().unwrap();
    if p.as_rule() == Rule::type_ {
        let type_ = inner.required(data, type_);
        ImportArg::Type(type_)
    } else {
        let erased = inner.flag(Rule::erased_op);
        let mode = if erased { Mode::Erased } else { Mode::Free };
        let term = inner.required(data, term);
        ImportArg::Term(mode, term)
    }
}

fn param(data: Data, pairs: Pair<Rule>) -> Parameter {
    fn relevant_param(data: Data, param: Pair<Rule>) -> Parameter {
        let span = span(param.as_span());
        let mut inner = param.into_inner();
        let id = inner.required(data, id);
        inner.variant(data, |data, p| match p.as_rule() {
            Rule::kind => {
                let mode = Mode::Erased;
                let body = TypeOrKind::Kind(kind(data, p));
                Some(Parameter { span, id, mode, body })
            },
            Rule::type_ => {
                let mode = Mode::Free;
                let body = TypeOrKind::Type(type_(data, p));
                Some(Parameter { span, id, mode, body })
            },
            _ => None
        })
    }
    fn erased_param(data: Data, param: Pair<Rule>) -> Parameter {
        let span = span(param.as_span());
        let mut inner = param.into_inner();
        let id = inner.required(data, id);
        let mode = Mode::Erased;
        let body = TypeOrKind::Type(inner.required(data, type_));
        Parameter { span, id, mode, body }
    }
    let mut inner = pairs.into_inner();
    inner.variant(data, |data, p| match p.as_rule() {
        Rule::relevant_param => Some(relevant_param(data, p)),
        Rule::erased_param => Some(erased_param(data, p)),
        _ => None
    })
}

fn define_term(mut data: Data, def: Pair<Rule>) -> DefineTerm {
    let span = span(def.as_span());
    let mut inner = def.into_inner();
    let id = inner.required(data, decl_id);
    data.1.decl = id.decl;
    let annotation = inner.optional(data, Rule::type_, type_).map(Box::new);
    let body = Box::new(inner.required(data, term));
    DefineTerm { span, id, annotation, body }
}

fn define_type(mut data: Data, def: Pair<Rule>) -> DefineType {
    let span = span(def.as_span());
    let mut inner = def.into_inner();
    let id = inner.required(data, decl_id);
    data.1.decl = id.decl;
    let annotation = Box::new(inner.required(data, kind));
    let body = Box::new(inner.required(data, type_));
    DefineType { span, id, annotation, body }
}

fn define_kind(mut data: Data, def: Pair<Rule>) -> DefineKind {
    let span = span(def.as_span());
    let mut inner = def.into_inner();
    let id = inner.required(data, decl_id);
    data.1.decl = id.decl;
    let args = inner.list(data, Rule::kind_arg, kind_arg);
    let body = Box::new(inner.required(data, kind));
    DefineKind { span, id, args, body }
}

fn define_datatype(mut data: Data, def: Pair<Rule>) -> DefineDatatype {
    fn ctor(data: Data, ctor: Pair<Rule>) -> Constructor {
        let mut inner = ctor.into_inner();
        let id = inner.required(data, id);
        let annotation = inner.required(data, type_);
        Constructor { id, annotation }
    }
    fn ctors(data: Data, ctors: Pair<Rule>) -> Vec<Constructor> {
        let mut inner = ctors.into_inner();
        inner.list(data, Rule::ctor, ctor)
    }
    let span = span(def.as_span());
    let mut inner = def.into_inner();
    let id = inner.required(data, decl_id);
    data.1.decl = id.decl;
    let params = inner.list(data, Rule::param, param);
    let kind = Box::new(inner.required(data, kind));
    let ctors = inner.required(data, ctors);
    DefineDatatype { span, id, params, kind, ctors }
}

fn term(data: Data, pairs: Pair<Rule>) -> Term {
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
            Rule::term_application => body = Some(term_application(data, p)),
            _ => unreachable!()
        }
    }
    // Terms must have a body
    let body = body.unwrap();
    binders.drain(..).rev().fold(body, |acc, b| term_binder(data, acc, b))
}

fn term_binder(data: Data, body: Term, binder: Pair<Rule>) -> Term {
    fn num(_data: Data, num: Pair<Rule>) -> usize {
        let num = num.as_str().parse::<usize>();
        // The grammar should not allow the num rule to error at this point
        num.ok().unwrap()
    }
    let span = span(binder.as_span());
    let body = Box::new(body);
    let rule = binder.as_rule();
    let mut inner = binder.into_inner();
    match rule {
        Rule::term_lambda | Rule::term_erased_lambda => {
            let mode = if rule == Rule::term_lambda { Mode::Free } else { Mode::Erased };
            let id = inner.required(data, id);
            if let Some(k) = inner.optional(data, Rule::kind, kind) {
                let annotation = Box::new(k);
                Term::TypeLambda { span, id, annotation, body }
            } else {
                let annotation = inner.optional(data, Rule::type_, type_).map(Box::new);
                Term::Lambda { span, mode, id, annotation, body }
            }
        },
        Rule::term_let | Rule::term_erased_let => {
            let mode = if rule == Rule::term_let { Mode::Free } else { Mode::Erased };
            if inner.peek().map(|p| p.as_rule()) == Some(Rule::define_type) {
                let def = inner.required(data, define_type);
                Term::TypeLet { span, def, body }
            } else {
                let def = inner.required(data, define_term);
                Term::Let { span, mode, def, body }
            }
        },
        Rule::term_rewrite => {
            let reduce = inner.flag(Rule::reduce);
            let occurrence = inner.optional(data, Rule::num, num);
            let equation = Box::new(inner.required(data, term_atom));
            let guide = inner.optional(data, Rule::guide, guide);
            Term::Rewrite { span, reduce, occurrence, equation, guide, body }
        },
        Rule::term_annotate => {
            let annotation = Box::new(inner.required(data, type_));
            Term::Annotate { span, annotation, body }
        },
        _ => unreachable!()
    }
}

fn term_application(data: Data, pairs: Pair<Rule>) -> Term {
    let mut iter = pairs.into_inner();
    // A term application must begin with a term atom
    let mut result = iter.required(data, term_atom);
    let mut mode = Mode::Free;
    for p in iter {
        let span = span(p.as_span());
        match p.as_rule() {
            Rule::erased_op => mode = Mode::Erased,
            Rule::term_atom | Rule::term => {
                let fun = Box::new(result);
                let arg = Box::new(
                    if p.as_rule() == Rule::term { term(data, p) }
                    else { term_atom(data, p) });
                result = Term::Apply { span, mode, fun, arg };
                mode = Mode::Free;
            },
            Rule::type_atom | Rule::type_ => {
                let fun = Box::new(result);
                let arg = Box::new(
                    if p.as_rule() == Rule::type_ { type_(data, p) }
                    else { type_atom(data, p) });
                result = Term::TypeApply { span, fun, arg};
            }
            _ => unreachable!()
        };
    }
    result
}

fn term_atom(data: Data, atom: Pair<Rule>) -> Term {
    fn case_arg(data: Data, arg: Pair<Rule>) -> CaseArg {
        let mut inner = arg.into_inner();
        let type_op = inner.flag(Rule::type_op);
        let erased_op = inner.flag(Rule::erased_op);
        let id = inner.required(data, id);
        if type_op { CaseArg::Type(id) }
        else if erased_op { CaseArg::Erased(id) }
        else { CaseArg::Free(id) }
    }
    fn case(data: Data, case: Pair<Rule>) -> Case {
        let span = span(case.as_span());
        let mut inner = case.into_inner();
        let id = inner.required(data, qual_id);
        let args = inner.list(data, Rule::case_arg, case_arg);
        let body = inner.required(data, term);
        Case { span, id, args, body }
    }
    fn cases(data: Data, cases: Pair<Rule>) -> Vec<Case> {
        let mut inner = cases.into_inner();
        inner.list(data, Rule::case, case)
    }
    fn proj(_data: Data, proj: Pair<Rule>) -> (Span, usize) {
        let span = span(proj.as_span());
        let v = proj.as_str().trim_start_matches('.')
            .parse::<usize>()
            .ok().unwrap();
        (span, v)
    }
    let mut inner = atom.into_inner();

    let term = inner.variant(data, |data, p| {
        let span = span(p.as_span());
        match p.as_rule() {
            Rule::term_intersection => {
                let mut inner = p.into_inner();
                let first = Box::new(inner.required(data, term));
                let second = Box::new(inner.required(data, term));
                Some(Term::Intersection { span, first, second })
            },
            Rule::term_refl => {
                let mut inner = p.into_inner();
                let guide = inner.optional(data, Rule::term_guide, term_guide).map(Box::new);
                let erasure = inner.optional(data, Rule::term, term).map(Box::new);
                Some(Term::Refl { span, guide, erasure })
            },
            Rule::term_cast => {
                let mut inner = p.into_inner();
                let equation = Box::new(inner.required(data, term_atom));
                let input = inner.required(data, term_application);
                let input = Box::new(input);
                let erasure = Box::new(inner.required(data, term));
                Some(Term::Cast { span, equation, input, erasure })
            },
            Rule::term_induction => {
                let mut inner = p.into_inner();
                let id = inner.required(data, id);
                let inductee = inner.required(data, term_application);
                let inductee = Box::new(inductee);
                let motive = inner.optional(data, Rule::type_, type_).map(Box::new);
                let cases = inner.required(data, cases);
                Some(Term::Induct { span, id, inductee, motive, cases })
            },
            Rule::term_match => {
                let mut inner = p.into_inner();
                // Detect deprecated mu prime token header
                if inner.flag(Rule::mu_prime) {
                    println!("Warning, μ' is deprecated.");
                }
                let guide = inner.optional(data, Rule::term_guide, term_guide).map(Box::new);
                let matched = inner.required(data, term_application);
                let matched = Box::new(matched);
                let motive = inner.optional(data, Rule::type_, type_).map(Box::new);
                let cases = inner.required(data, cases);
                Some(Term::Match { span, guide, matched, motive, cases })
            },
            Rule::term_separate => {
                let mut inner = p.into_inner();
                let annotation = inner.optional(data, Rule::type_, type_).map(Box::new);
                let equation = Box::new(inner.required(data, term));
                Some(Term::Separate { span, annotation, equation })
            },
            Rule::term_symmetry => {
                let mut inner = p.into_inner();
                let equation = Box::new(inner.required(data, term_atom));
                Some(Term::Symmetry { span, equation })
            },
            Rule::term => Some(term(data, p)),
            Rule::hole => Some(Term::Hole { span }),
            Rule::qual_id => {
                let id = qual_id(data, p);
                Some(Term::Var { span, id })
            },
            _ => None
        }
    });

    let mut projs = inner.list(data, Rule::proj, proj);
    projs.drain(..).fold(term, |acc, (span, variant)| {
        let body = Box::new(acc);
        Term::Project { span, variant, body }
    })
}

fn term_guide(data: Data, pairs: Pair<Rule>) -> Term {
    // A term guide consists of exactly one term
    let inner = pairs.into_inner().next().unwrap();
    term(data, inner)
}

fn guide(data: Data, guide: Pair<Rule>) -> RewriteGuide {
    let mut inner = guide.into_inner();
    let id = inner.required(data, id);
    let hint = inner.optional(data, Rule::term_guide, term_guide).map(Box::new);
    let equation = Box::new(inner.required(data, type_));
    RewriteGuide { id, hint, equation }
}

fn type_(data: Data, pairs: Pair<Rule>) -> Type {
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
            Rule::type_body => body = Some(type_body(data, p)),
            _ => unreachable!()
        }
    }
    // Types must have a body
    let body = body.unwrap();
    binders.drain(..).rev().fold(body, |acc, b| type_binder(data, acc, b))
}

fn type_binder(data: Data, body: Type, binder: Pair<Rule>) -> Type {
    let span = span(binder.as_span());
    let body = Box::new(body);
    let rule = binder.as_rule();
    let mut inner = binder.into_inner();
    match rule {
        Rule::type_forall => {
            let mode = Mode::Free;
            let id = inner.required(data, id);
            let domain = Box::new(inner.required(data, type_));
            Type::TermFn { span, mode, id, domain, body }
        },
        Rule::type_erased_forall => {
            let mode = Mode::Erased;
            let id = inner.required(data, id);
            if inner.peek().map(|p| p.as_rule()) == Some(Rule::kind) {
                let domain = Box::new(inner.required(data, kind));
                Type::Fn { span, id, domain, body }
            } else {
                let domain = Box::new(inner.required(data, type_));
                Type::TermFn { span, mode, id, domain, body }
            }
        },
        Rule::type_lambda => {
            let id = inner.required(data, id);
            if inner.peek().map(|p| p.as_rule()) == Some(Rule::kind) {
                let annotation = Box::new(inner.required(data, kind));
                Type::Lambda { span, id, annotation, body }
            } else {
                let annotation = Box::new(inner.required(data, type_));
                Type::TermLambda { span, id, annotation, body }
            }
        },
        Rule::type_intersection => {
            let id = inner.required(data, id);
            let first = Box::new(inner.required(data, type_));
            let second = body;
            Type::Intersection { span, id, first, second }
        },
        Rule::type_let => {
            if inner.peek().map(|p| p.as_rule()) == Some(Rule::define_type) {
                let def = inner.required(data, define_type);
                Type::Let { span, def, body }
            } else {
                let def = inner.required(data, define_term);
                Type::TermLet { span, def, body }
            }
        },
        _ => unreachable!()
    }
}

fn type_body(data: Data, pairs: Pair<Rule>) -> Type {
    let mut inner = pairs.into_inner();
    let mut result = inner.required(data, type_atom);
    while let Some(p) = inner.next() {
        let span = span(p.as_span());
        match p.as_rule() {
            Rule::erased_arrow | Rule::arrow  => {
                let mode = if p.as_rule() == Rule::arrow { Mode::Free } else { Mode::Erased };
                let id = dummy_id(data.1.module);
                let domain = Box::new(result);
                let body = Box::new(inner.required(data, type_));
                result = Type::TermFn { span, mode, id, domain, body }
            },
            Rule::type_atom => {
                let fun = Box::new(result);
                let arg = Box::new(type_atom(data, p));
                result = Type::Apply { span, fun, arg }
            },
            Rule::term_atom => {
                let fun = Box::new(result);
                let arg = Box::new(term_atom(data, p));
                result = Type::TermApply { span, fun, arg }
            },
            _ => unreachable!()
        }
    }
    result
}

fn type_atom(data: Data, pairs: Pair<Rule>) -> Type {
    let mut inner = pairs.into_inner();
    let p = inner.next().unwrap();
    let span = span(p.as_span());
    match p.as_rule() {
        Rule::term => {
            let left = Box::new(term(data, p));
            let right = Box::new(inner.required(data, term));
            Type::Equality { span, left, right }
        },
        Rule::type_ => type_(data, p),
        Rule::hole => Type::Hole { span },
        Rule::qual_id => {
            let id = qual_id(data, p);
            Type::Var { span, id }
        },
        _ => unreachable!()
    }
}

fn kind(data: Data, pairs: Pair<Rule>) -> Kind {
    fn kind_binder(data: Data, body: Kind, pairs: Pair<Rule>) -> Kind {
        let body = Box::new(body);
        let mut inner = pairs.into_inner();
        let id = inner.required(data, id);
        let p = inner.next().unwrap();
        let span = span(p.as_span());
        if p.as_rule() == Rule::kind {
            let domain = Box::new(kind(data, p));
            Kind::Fn { span, id, domain, body }
        } else {
            let domain = Box::new(type_(data, p));
            Kind::TypeFn { span, id, domain, body }
        }
    }
    fn kind_atom(data: Data, pairs: Pair<Rule>) -> Kind {
        let mut inner = pairs.into_inner();
        let p = inner.next().unwrap();
        let span = span(p.as_span());
        match p.as_rule() {
            Rule::kind => kind(data, p),
            Rule::star => Kind::Star { span },
            Rule::qual_kind_id => {
                let id = qual_id(data, p);
                let args = inner.variant_list(data, |data, p|
                    match p.as_rule() {
                        Rule::type_atom => Some(TermOrType::Type(type_(data, p))),
                        Rule::term_atom => Some(TermOrType::Term(term(data, p))),
                        _ => None
                    });
                Kind::Apply { span, id, args }
            },
            _ => unreachable!()
        }
    }
    fn type_application(data: Data, body: Kind, pairs: Pair<Rule>) -> Kind {
        let outer_span = span(pairs.as_span());
        let id = dummy_id(data.1.module);
        let mut inner = pairs.into_inner();
        // A type application must be headed by a type atom
        let mut result = inner.required(data, type_atom);
        for p in inner {
            let span = span(p.as_span());
            match p.as_rule() {
                Rule::type_atom => {
                    let fun = Box::new(result);
                    let arg = Box::new(type_atom(data, p));
                    result = Type::Apply { span, fun, arg }
                },
                Rule::term_atom => {
                    let fun = Box::new(result);
                    let arg = Box::new(term_atom(data, p));
                    result = Type::TermApply { span, fun, arg }
                },
                _ => unreachable!()
            }
        }
        let span = outer_span;
        let domain = Box::new(result);
        let body = Box::new(body);
        Kind::TypeFn { span, id, domain, body }
    }
    fn rec(data: Data, pairs: Pairs<Rule>) -> Kind {
        let mut iter = pairs;
        if let Some(p) = iter.next() {
            match p.as_rule() {
                Rule::kind_binder => {
                    let body = rec(data, iter);
                    kind_binder(data, body, p)
                },
                Rule::type_application => {
                    let body = rec(data, iter);
                    type_application(data, body, p)
                },
                Rule::kind_atom => {
                    let mut result = kind_atom(data, p);
                    // The remaining rules must be `kind`
                    for p2 in iter {
                        let span = span(p2.as_span());
                        let id = dummy_id(data.1.module);
                        let domain = Box::new(result);
                        let body = Box::new(kind(data, p2));
                        result = Kind::Fn { span, id, domain, body };
                    }
                    result
                },
                _ => unreachable!()
            }
        } else { unreachable!() }
    }
    rec(data, pairs.into_inner())
}

fn kind_arg(data: Data, pairs: Pair<Rule>) -> KindArg {
    let mut inner = pairs.into_inner();
    let id = inner.required(data, id);
    if inner.peek().map(|p| p.as_rule()) == Some(Rule::kind) {
        let arg = TypeOrKind::Kind(inner.required(data, kind));
        KindArg { id, arg }
    } else {
        let arg = TypeOrKind::Type(inner.required(data, type_));
        KindArg { id, arg }
    }
}

fn path(_data: Data, pairs: Pair<Rule>) -> Span {
    span(pairs.as_span())
}

fn id(data: Data, id: Pair<Rule>) -> Id {
    let (start, end) = span(id.as_span());
    let (module, decl) = (data.1.module, data.1.decl);
    let namespace = None;
    let index = Some(Intern::from(&data.0[start..end]));
    Id { module, namespace, decl, index }
}

fn decl_id(data: Data, _id: Pair<Rule>) -> Id {
    let (module, decl) = (data.1.module, data.1.decl);
    let namespace = None;
    let index = None;
    Id { module, namespace, decl, index }
}

fn qual_id(data: Data, pairs: Pair<Rule>) -> Id {
    // TODO:
    dummy_id(data.1.module)
}

fn dummy_id(module: Symbol) -> Id {
    Id { module, namespace:None, decl:None, index:None }
}

fn span(span: pest::Span) -> Span {
    (span.start(), span.end())
}
