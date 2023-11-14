
use std::fmt;

use rpds::Vector;

use crate::hc::*;
use crate::utility::*;
use crate::value::EnvBound;

type Span = (usize, usize);

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Module {
    pub imports: Vec<Import>,
    pub id: Id,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub name: Symbol,
    pub mode: Mode,
    pub body: Term
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Import {
    pub public: bool,
    pub path: Span,
    pub namespace: Id,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub struct Decl {
    pub name: Symbol,
    pub ty: Term,
    pub body: Term
}

pub type Term = Hc<TermData>;

#[derive(Debug, Hash, Clone, PartialEq, Eq)]
pub enum TermData {
    Lambda {
        sort: Sort,
        mode: Mode,
        name: Symbol,
        domain: Term,
        body: Term
    },
    Let {
        sort: Sort,
        name: Symbol,
        let_body: Term,
        body: Term
    },
    Pi {
        sort: Sort,
        mode: Mode,
        name: Symbol,
        domain: Term,
        body: Term
    },
    Intersect {
        name: Symbol,
        first: Term,
        second: Term
    },
    Equality {
        left: Term,
        right: Term,
        anno: Term
    },
    Project {
        variant: usize,
        body: Term
    },
    Pair {
        first: Term,
        second: Term,
        anno: Term
    },
    Separate {
        equation: Term
    },
    Refl {
        input: Term
    },
    Cast {
        input: Term,
        witness: Term,
        evidence: Term,
    },
    Promote {
        equation: Term
    },
    Subst {
        predicate: Term,
        equation: Term
    },
    Apply {
        sort: Sort,
        mode: Mode,
        fun: Term,
        arg: Term
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

impl fmt::Display for Decl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} : {} = {}", self.name, self.ty, self.body)
    }
}

impl TermData {
    pub fn sort(&self) -> Sort {
        match self {
            TermData::Lambda { sort, .. }
            | TermData::Let { sort, .. }
            | TermData::Pi { sort, .. } => *sort,
            TermData::Intersect { .. }
            | TermData::Equality { .. } => Sort::Type,
            | TermData::Project { .. }
            | TermData::Pair { .. }
            | TermData::Separate { .. }
            | TermData::Refl { .. }
            | TermData::Cast { .. }
            | TermData::Promote { .. }
            | TermData::Subst { .. } => Sort::Term,
            TermData::Apply { sort, .. }
            | TermData::Bound { sort, .. }
            | TermData::Free { sort, .. }
            | TermData::Meta { sort, .. }
            | TermData::InsertedMeta { sort, .. } => *sort,
            TermData::Star => Sort::Kind,
            TermData::SuperStar => Sort::Kind,
        }
    }

    pub fn ambiguous(&self) -> bool {
        match self {
            TermData::Lambda { .. }
            | TermData::Let { .. }
            | TermData::Pi { .. }
            | TermData::Intersect { .. } => true,
            TermData::Equality { .. } => false,
            TermData::Project { .. }
            | TermData::Pair { .. } => false,
            TermData::Separate { .. } => true,
            TermData::Refl { .. } => false,
            TermData::Promote { .. } => false,
            TermData::Cast { .. } => true,
            TermData::Subst { .. } => false,
            TermData::Apply { .. } => true,
            TermData::Bound { .. }
            | TermData::Free { .. }
            | TermData::Meta { .. }
            | TermData::InsertedMeta { .. }
            | TermData::Star
            | TermData::SuperStar => false,
        }
    }

    pub fn is_apply(&self) -> bool { matches!(self, TermData::Apply { .. }) }

    pub fn to_string_with_context(&self, ctx: Vector<Symbol>) -> String {
        match self {
            TermData::Lambda { mode, name, body, .. } => {
                let binder = match mode {
                    Mode::Erased => "Λ",
                    Mode::Free => "λ",
                    Mode::TypeLevel => "λ"
                };
                let ctx = ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                format!("{} {}. {}", binder, name, body)
            }
            TermData::Let { name, let_body, body, .. } => {
                let let_body = let_body.to_string_with_context(ctx.clone());
                let ctx = ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                format!("let {} := {}; {}", name, let_body, body)
            }
            TermData::Pi { mode, name, domain, body, .. } => {
                let binder = match mode {
                    Mode::Erased => "∀",
                    Mode::Free => "Π",
                    Mode::TypeLevel => "Π"
                };
                let domain_str = domain.to_string_with_context(ctx.clone());
                let ctx = ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                if domain.ambiguous() { format!("{} {}:({}). {}", binder, name, domain_str, body) }
                else { format!("{} {}:{}. {}", binder, name, domain_str, body) }
            }
            TermData::Intersect { name, first, second } => {
                let first_str = first.to_string_with_context(ctx.clone());
                let ctx = ctx.push_back(*name);
                let second = second.to_string_with_context(ctx);
                if first.ambiguous() { format!("ι {}:({}), {}", name, first_str, second) }
                else { format!("ι {}:{}, {}", name, first_str, second) }
            }
            TermData::Equality { left, right, anno } => {
                let left = left.to_string_with_context(ctx.clone());
                let right = right.to_string_with_context(ctx.clone());
                let anno = anno.to_string_with_context(ctx);
                format!("{{{} =[{}] {}}}", left, anno, right)
            }
            TermData::Project { variant, body } => {
                let body = body.to_string_with_context(ctx);
                format!("{}.{}", body, variant)
            }
            TermData::Pair { first, second, anno } => {
                let first = first.to_string_with_context(ctx.clone());
                let second = second.to_string_with_context(ctx.clone());
                let anno = anno.to_string_with_context(ctx);
                format!("[{}, {}; {}]", first, second, anno)
            }
            TermData::Separate { equation } => {
                let equation = equation.to_string_with_context(ctx);
                format!("δ {}", equation)
            }
            TermData::Refl { input } => {
                let input = input.to_string_with_context(ctx);
                format!("rfl {}", input)
            }
            TermData::Promote { equation } => {
                let equation = equation.to_string_with_context(ctx);
                format!("θ {}", equation)
            }
            TermData::Cast { input, witness, evidence } => {
                let equation_str = evidence.to_string_with_context(ctx.clone());
                let input = input.to_string_with_context(ctx.clone());
                let witness = witness.to_string_with_context(ctx);
                if evidence.ambiguous() { format!("φ ({}) - {} {{{}}}", equation_str, input, witness) }
                else { format!("φ {} - {} {{{}}}", equation_str, input, witness) }
            }
            TermData::Promote { equation } => {
                let equation_str = equation.to_string_with_context(ctx.clone());
                format!("ϑ {{ {} }}", equation_str)
            }
            TermData::Subst { predicate, equation } => {
                todo!()
            }
            TermData::Apply { mode, fun, arg, .. } => {
                let operator = match mode {
                    Mode::Free => "",
                    Mode::Erased => "-",
                    Mode::TypeLevel => ""
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
            TermData::Bound { index, .. } => {
                let mut result = index.to_string();
                if ctx.len() > **index {
                    let level = index.to_level(ctx.len());
                    if let Some(var) = ctx.get(*level) { 
                        result = var.to_string()
                    }
                }
                result
            }
            TermData::Meta { name, .. } => name.to_string(),
            TermData::InsertedMeta { name, mask, .. } => {
                let mut args = String::new();
                for i in 0..mask.len() {
                    if mask[i] == EnvBound::Bound {
                        args.push(' ');
                        let symbol = ctx.get(i)
                            .cloned()
                            .unwrap_or_default();
                        args.push_str(symbol.as_str());
                    }
                }
                format!("({}{})", name, args)
            }
            TermData::Free { id, .. } => id.to_string(),
            TermData::Star => "★".to_string(),
            TermData::SuperStar => "□".to_string(),
        }
    }
}

impl fmt::Display for TermData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_with_context(Vector::new()))
    }
}
