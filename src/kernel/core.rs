
use std::rc::Rc;
use std::fmt;

use crate::common::*;
use crate::kernel::value::EnvBound;

type Span = (usize, usize);

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Module {
    pub imports: Vec<Import>,
    pub id: Id,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Parameter {
    pub name: Symbol,
    pub mode: Mode,
    pub body: Rc<Term>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Import {
    pub public: bool,
    pub path: Span,
    pub namespace: Id,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Decl {
    pub name: Symbol,
    pub ty: Rc<Term>,
    pub body: Rc<Term>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RewriteGuide {
    pub name: Symbol,
    pub hint: Rc<Term>,
    pub ty: Rc<Term>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Lambda {
        sort: Sort,
        domain_sort: Sort,
        mode: Mode,
        name: Symbol,
        body: Rc<Term>
    },
    Let {
        sort: Sort,
        mode: Mode,
        name: Symbol,
        let_body: Rc<Term>,
        body: Rc<Term>
    },
    Pi {
        sort: Sort,
        mode: Mode,
        name: Symbol,
        domain: Rc<Term>,
        body: Rc<Term>
    },
    IntersectType {
        name: Symbol,
        first: Rc<Term>,
        second: Rc<Term>
    },
    Equality {
        left: Rc<Term>,
        right: Rc<Term>
    },
    Rewrite {
        equation: Rc<Term>,
        guide: RewriteGuide,
        body: Rc<Term>
    },
    Annotate {
        anno: Rc<Term>,
        body: Rc<Term>
    },
    Project {
        variant: usize,
        body: Rc<Term>
    },
    Intersect {
        first: Rc<Term>,
        second: Rc<Term>
    },
    Separate {
        equation: Rc<Term>
    },
    Refl {
        erasure: Rc<Term>
    },
    Cast {
        equation: Rc<Term>,
        input: Rc<Term>,
        erasure: Rc<Term>
    },
    Apply {
        sort: Sort,
        mode: Mode,
        fun: Rc<Term>,
        arg: Rc<Term>
    },
    Bound {
        sort: Sort,
        index: Index
    },
    Free {
        sort: Sort,
        id: Id
    },
    Meta {
        sort: Sort,
        name: Symbol
    },
    InsertedMeta {
        sort: Sort,
        name: Symbol,
        mask: Vec<EnvBound>
    },
    Star,
    SuperStar,
}

impl RewriteGuide {
    pub fn to_string_with_context(&self, mut ctx: im_rc::Vector<Symbol>) -> String {
        let hint = self.hint.to_string_with_context(ctx.clone());
        ctx.push_back(self.name);
        let ty = self.ty.to_string_with_context(ctx);
        format!("@ {} <{}>. {}", self.name, hint, ty)
    }
}

impl fmt::Display for Decl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} : {} = {}", self.name, self.ty, self.body)
    }
}

impl Term {
    pub fn id() -> Term {
        let (sort, domain_sort, mode, name) = (Sort::Term, Sort::Term, Mode::Free, Symbol::from("x"));
        let body = Rc::new(Term::Bound { sort, index:0.into() });
        Term::Lambda { sort, domain_sort, mode, name, body }
    }

    // This is meant for pretty-printing erased terms, we intentionally don't erase lambdas so that we don't have to
    // fix indices, plus the extra lambda abstractions don't obfuscate output very much
    pub fn partial_erase(&self) -> Term {
        match self {
            Term::Lambda { sort, domain_sort, mode, name, body } => {
                Term::Lambda {
                    sort:*sort,
                    domain_sort:*domain_sort,
                    mode:*mode,
                    name:*name,
                    body:Rc::new(body.partial_erase())
                }
            }
            Term::Let { sort, mode, name, let_body, body } => {
                if *mode == Mode::Erased { body.partial_erase() }
                else {
                    Term::Let {
                        sort:*sort,
                        mode:*mode,
                        name:*name,
                        let_body:Rc::new(let_body.partial_erase()),
                        body:Rc::new(body.partial_erase())
                    }
                }
            }
            t @ Term::Pi { .. }
            | t @ Term::IntersectType { .. }
            | t @ Term::Equality { .. } => t.clone(),
            Term::Rewrite { body, .. } => body.partial_erase(),
            Term::Annotate { body, .. } => body.partial_erase(),
            Term::Project { body, .. } => body.partial_erase(),
            Term::Intersect { first, .. } => first.partial_erase(),
            Term::Separate { .. } => Term::id(),
            Term::Refl { erasure } => erasure.partial_erase(),
            Term::Cast { erasure, .. } => erasure.partial_erase(),
            Term::Apply { sort, mode, fun, arg } => {
                if *mode == Mode::Erased { fun.partial_erase() }
                else {
                    Term::Apply {
                        sort:*sort,
                        mode:*mode,
                        fun:Rc::new(fun.partial_erase()),
                        arg:Rc::new(arg.partial_erase())
                    }
                }
            }
            t @ Term::Bound { .. }
            | t @ Term::Free { .. }
            | t @ Term::Meta { .. }
            | t @ Term::InsertedMeta { .. }
            | t @ Term::Star
            | t @ Term::SuperStar => t.clone()
        }
    }

    pub fn sort(&self) -> Sort {
        match self {
            Term::Lambda { sort, .. }
            | Term::Let { sort, .. }
            | Term::Pi { sort, .. } => *sort,
            Term::IntersectType { .. }
            | Term::Equality { .. } => Sort::Type,
            Term::Rewrite { .. }
            | Term::Annotate { .. }
            | Term::Project { .. }
            | Term::Intersect { .. }
            | Term::Separate { .. }
            | Term::Refl { .. }
            | Term::Cast { .. } => Sort::Term,
            Term::Apply { sort, .. }
            | Term::Bound { sort, .. }
            | Term::Free { sort, .. }
            | Term::Meta { sort, .. }
            | Term::InsertedMeta { sort, .. } => *sort,
            Term::Star => Sort::Kind,
            Term::SuperStar => Sort::Kind,
        }
    }

    pub fn ambiguous(&self) -> bool {
        match self {
            Term::Lambda { .. }
            | Term::Let { .. }
            | Term::Pi { .. }
            | Term::IntersectType { .. } => true,
            Term::Equality { .. } => false,
            Term::Rewrite { .. }
            | Term::Annotate { .. } => true,
            Term::Project { .. }
            | Term::Intersect { .. } => false,
            Term::Separate { .. } => true,
            Term::Refl { .. } => false,
            Term::Cast { .. } => true,
            Term::Apply { .. } => true,
            Term::Bound { .. }
            | Term::Free { .. }
            | Term::Meta { .. }
            | Term::InsertedMeta { .. }
            | Term::Star
            | Term::SuperStar => false,
        }
    }

    pub fn is_apply(&self) -> bool { matches!(self, Term::Apply { .. }) }

    pub fn to_string_with_context(&self, mut ctx: im_rc::Vector<Symbol>) -> String {
        match self {
            Term::Lambda { mode, name, body, .. } => {
                let binder = match mode {
                    Mode::Erased => "Λ",
                    Mode::Free => "λ",
                };
                ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                format!("{} {}. {}", binder, name, body)
            }
            Term::Let { mode, name, let_body, body, .. } => {
                let (left, right) = match mode {
                    Mode::Erased => ("{", "}"),
                    Mode::Free => ("[", "]")
                };
                let let_body = let_body.to_string_with_context(ctx.clone());
                ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                format!("{}{} = {}{} - {}", left, name, let_body, right, body)
            }
            Term::Pi { mode, name, domain, body, .. } => {
                let binder = match mode {
                    Mode::Erased => "∀",
                    Mode::Free => "Π"
                };
                let domain_str = domain.to_string_with_context(ctx.clone());
                ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                if domain.ambiguous() { format!("{} {}:({}). {}", binder, name, domain_str, body) }
                else { format!("{} {}:{}. {}", binder, name, domain_str, body) }
            }
            Term::IntersectType { name, first, second } => {
                let first_str = first.to_string_with_context(ctx.clone());
                ctx.push_back(*name);
                let second = second.to_string_with_context(ctx);
                if first.ambiguous() { format!("ι {}:({}), {}", name, first_str, second) }
                else { format!("ι {}:{}, {}", name, first_str, second) }
            }
            Term::Equality { left, right } => {
                let left = left.to_string_with_context(ctx.clone());
                let right = right.to_string_with_context(ctx);
                format!("{{{} ≃ {}}}", left, right)
            }
            Term::Rewrite { equation, guide, body } => {
                let equation = equation.to_string_with_context(ctx.clone());
                let guide = guide.to_string_with_context(ctx.clone());
                let body = body.to_string_with_context(ctx);
                format!("ρ {} {} - {}", equation, guide, body)
            }
            Term::Annotate { anno, body } => {
                let anno = anno.to_string_with_context(ctx.clone());
                let body = body.to_string_with_context(ctx);
                format!("χ {} - {}", anno, body)
            }
            Term::Project { variant, body } => {
                let body = body.to_string_with_context(ctx);
                format!("{}.{}", body, variant)
            }
            Term::Intersect { first, second } => {
                let first = first.to_string_with_context(ctx.clone());
                let second = second.to_string_with_context(ctx);
                format!("[{}, {}]", first, second)
            }
            Term::Separate { equation } => {
                let equation = equation.to_string_with_context(ctx);
                format!("δ - {}", equation)
            }
            Term::Refl { erasure } => {
                let erasure = erasure.to_string_with_context(ctx);
                format!("β{{{}}}", erasure)
            }
            Term::Cast { equation, input, erasure } => {
                let equation_str = equation.to_string_with_context(ctx.clone());
                let input = input.to_string_with_context(ctx.clone());
                let erasure = erasure.to_string_with_context(ctx);
                if equation.ambiguous() { format!("φ ({}) - {} {{{}}}", equation_str, input, erasure) }
                else { format!("φ {} - {} {{{}}}", equation_str, input, erasure) }
            }
            Term::Apply { mode, fun, arg, .. } => {
                let operator = match mode {
                    Mode::Free => "",
                    Mode::Erased => "-",
                };
                let fun_str = fun.to_string_with_context(ctx.clone());
                let arg_str = arg.to_string_with_context(ctx);
                match (fun.is_apply() || !fun.ambiguous(), arg.ambiguous()) {
                    (true, true) => format!("{} {}({})", fun_str, operator, arg_str),
                    (true, false) => format!("{} {}{}", fun_str, operator, arg_str),
                    (false, true) => format!("({}) {}({})", fun_str, operator, arg_str),
                    (false, false) => format!("({}) {}{}", fun_str, operator, arg_str),
                }
            }
            Term::Bound { index, .. } => {
                let mut result = index.to_string();
                if ctx.len() > **index {
                    let level = index.to_level(ctx.len());
                    if let Some(var) = ctx.get(*level) { 
                        result = var.to_string()
                    }
                }
                result
            }
            Term::Meta { name, .. } => name.to_string(),
            Term::InsertedMeta { name, mask, .. } => {
                let mut args = String::new();
                for i in 0..mask.len() {
                    if mask[i] == EnvBound::Bound {
                        args.push(' ');
                        let symbol = ctx.get(i)
                            .copied()
                            .unwrap_or_default();
                        args.push_str(symbol.as_str());
                    }
                }
                format!("({}{})", name, args)
            }
            Term::Free { id, .. } => id.to_string(),
            Term::Star => "★".to_string(),
            Term::SuperStar => "□".to_string(),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_with_context(im_rc::Vector::new()))
    }
}
