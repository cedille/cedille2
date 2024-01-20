
use std::fmt;

use imbl::Vector;

use crate::hc::*;
use crate::utility::*;
use crate::value::EnvBound;
use crate::database::Database;

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
        witness: Term,
        evidence: Term,
    },
    Promote {
        equation: Term
    },
    EqInduct {
        domain: Term,
        predicate: Term,
        lhs: Term,
        rhs: Term,
        equation: Term,
        case: Term
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
            | TermData::EqInduct { .. } => Sort::Term,
            TermData::Apply { sort, .. }
            | TermData::Bound { sort, .. }
            | TermData::Free { sort, .. }
            | TermData::Meta { sort, .. }
            | TermData::InsertedMeta { sort, .. } => *sort,
            TermData::Star => Sort::Kind,
            TermData::SuperStar => Sort::Kind,
        }
    }

    pub fn fv_empty_index(&self, index: Index) -> bool {
        match self {
            TermData::Lambda { domain, body, .. } => {
                domain.fv_empty_index(index) && body.fv_empty_index(index + 1)
            }
            TermData::Let { let_body, body, .. } => {
                let_body.fv_empty_index(index) && body.fv_empty_index(index + 1)
            }
            TermData::Pi { domain, body, .. } => {
                domain.fv_empty_index(index) && body.fv_empty_index(index + 1)
            }
            TermData::Intersect { first, second, .. } => {
                first.fv_empty_index(index) && second.fv_empty_index(index + 1)
            }
            TermData::Equality { left, right, anno } => {
                left.fv_empty_index(index) && right.fv_empty_index(index) && anno.fv_empty_index(index)
            }
            TermData::Project { body, .. } => body.fv_empty_index(index),
            TermData::Pair { first, second, anno } => {
                first.fv_empty_index(index) && second.fv_empty_index(index) && anno.fv_empty_index(index)
            }
            TermData::Separate { equation } => equation.fv_empty_index(index),
            TermData::Refl { input } => input.fv_empty_index(index),
            TermData::Cast { witness, evidence } => {
                witness.fv_empty_index(index) && evidence.fv_empty_index(index)
            }
            TermData::Promote { equation } => equation.fv_empty_index(index),
            TermData::EqInduct { domain, predicate, lhs, rhs, equation, case } => {
                domain.fv_empty_index(index) && predicate.fv_empty_index(index) && lhs.fv_empty_index(index)
                && rhs.fv_empty_index(index) && equation.fv_empty_index(index) && case.fv_empty_index(index)
            }
            TermData::Apply { fun, arg, .. } => {
                fun.fv_empty_index(index) && arg.fv_empty_index(index)
            }
            TermData::Bound { index:var, .. } => **var < *index,
            TermData::Free { .. } => true,
            TermData::Meta { .. } => true,
            TermData::InsertedMeta { .. } => true,
            TermData::Star => true,
            TermData::SuperStar => true,
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
            TermData::EqInduct { .. } => false,
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

    pub fn to_string_with_context(&self, mut ctx: Vector<Symbol>) -> String {
        match self {
            TermData::Lambda { mode, name, body, .. } => {
                let binder = match mode {
                    Mode::Erased => "Λ",
                    Mode::Free => "λ",
                    Mode::TypeLevel => "λₜ"
                };
                ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                format!("{} {}. {}", binder, name, body)
            }
            TermData::Let { name, let_body, body, .. } => {
                let let_body = let_body.to_string_with_context(ctx.clone());
                ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                format!("let {} := {}; {}", name, let_body, body)
            }
            TermData::Pi { mode, name, domain, body, .. } => {
                let binder = match mode {
                    Mode::Erased => "∀",
                    Mode::Free => "Π",
                    Mode::TypeLevel => "Πₜ"
                };
                let domain_str = domain.to_string_with_context(ctx.clone());
                ctx.push_back(*name);
                let body = body.to_string_with_context(ctx);
                if domain.ambiguous() { format!("{} {}:({}). {}", binder, name, domain_str, body) }
                else { format!("{} {}:{}. {}", binder, name, domain_str, body) }
            }
            TermData::Intersect { name, first, second } => {
                let first_str = first.to_string_with_context(ctx.clone());
                ctx.push_back(*name);
                let second = second.to_string_with_context(ctx);
                if first.ambiguous() { format!("ι {}:({}), {}", name, first_str, second) }
                else { format!("ι {}:{}, {}", name, first_str, second) }
            }
            TermData::Equality { left, right, anno } => {
                let left = left.to_string_with_context(ctx.clone());
                let right = right.to_string_with_context(ctx.clone());
                let anno = anno.to_string_with_context(ctx);
                format!("{} =[{}] {}", left, anno, right)
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
                let equation_str = equation.to_string_with_context(ctx.clone());
                format!("ϑ {{ {} }}", equation_str)
            }
            TermData::Cast { witness, evidence } => {
                let equation_str = evidence.to_string_with_context(ctx.clone());
                let witness = witness.to_string_with_context(ctx);
                format!("φ {{{}, {}}}", witness, equation_str)
            }
            TermData::EqInduct { domain, predicate, lhs, rhs, equation, case } => {
                let domain_str = domain.to_string_with_context(ctx.clone());
                let predicate_str = predicate.to_string_with_context(ctx.clone());
                let lhs_str = lhs.to_string_with_context(ctx.clone());
                let rhs_str = rhs.to_string_with_context(ctx.clone());
                let equation_str = equation.to_string_with_context(ctx.clone());
                let case_str = case.to_string_with_context(ctx);
                format!("J {{ {}, {}, {}, {}, {}, {} }}", domain_str, predicate_str, lhs_str, rhs_str, equation_str, case_str)
            }
            TermData::Apply { mode, fun, arg, .. } => {
                let operator = match mode {
                    Mode::Free => "",
                    Mode::Erased => "-",
                    Mode::TypeLevel => "∙"
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

pub trait TermExt {
    fn shift(&self, db: &Database, amount: usize, cutoff: usize) -> Self;
}

impl TermExt for Term {
    fn shift(&self, db: &Database, amount: usize, cutoff: usize) -> Self {
        match self.cloned() {
            TermData::Lambda { sort, mode, name, domain, body } => {
                let domain = domain.shift(db, amount, cutoff);
                let body = body.shift(db, amount, cutoff + 1);
                db.make_term(TermData::Lambda { sort, mode, name, domain, body })
            }
            TermData::Let { sort, name, let_body, body } => {
                let let_body = let_body.shift(db, amount, cutoff);
                let body = body.shift(db, amount, cutoff + 1);
                db.make_term(TermData::Let { sort, name, let_body, body })
            }
            TermData::Pi { sort, mode, name, domain, body } => {
                let domain = domain.shift(db, amount, cutoff);
                let body = body.shift(db, amount, cutoff + 1);
                db.make_term(TermData::Pi { sort, mode, name, domain, body })
            }
            TermData::Intersect { name, first, second } => {
                let first = first.shift(db, amount, cutoff);
                let second = second.shift(db, amount, cutoff + 1);
                db.make_term(TermData::Intersect { name, first, second })
            }
            TermData::Equality { left, right, anno } => {
                let left = left.shift(db, amount, cutoff);
                let right = right.shift(db, amount, cutoff);
                let anno = anno.shift(db, amount, cutoff);
                db.make_term(TermData::Equality { left, right, anno })
            }
            TermData::Project { variant, body } => {
                let body = body.shift(db, amount, cutoff);
                db.make_term(TermData::Project { variant, body })
            }
            TermData::Pair { first, second, anno } => {
                let first = first.shift(db, amount, cutoff);
                let second = second.shift(db, amount, cutoff);
                let anno = anno.shift(db, amount, cutoff);
                db.make_term(TermData::Pair { first, second, anno })
            }
            TermData::Separate { equation } => {
                let equation = equation.shift(db, amount, cutoff);
                db.make_term(TermData::Separate { equation })
            }
            TermData::Refl { input } => {
                let input = input.shift(db, amount, cutoff);
                db.make_term(TermData::Refl { input })
            }
            TermData::Cast { witness, evidence } => {
                let witness = witness.shift(db, amount, cutoff);
                let evidence = evidence.shift(db, amount, cutoff);
                db.make_term(TermData::Cast { witness, evidence })
            }
            TermData::Promote { equation } => {
                let equation = equation.shift(db, amount, cutoff);
                db.make_term(TermData::Promote { equation })
            }
            TermData::EqInduct { domain, predicate, lhs, rhs, equation, case } => {
                let domain = domain.shift(db, amount, cutoff);
                let predicate = predicate.shift(db, amount, cutoff);
                let lhs = lhs.shift(db, amount, cutoff);
                let rhs = rhs.shift(db, amount, cutoff);
                let equation = equation.shift(db, amount, cutoff);
                let case = case.shift(db, amount, cutoff);
                db.make_term(TermData::EqInduct { domain, predicate, lhs, rhs, equation, case })
            }
            TermData::Apply { sort, mode, fun, arg } => {
                let fun = fun.shift(db, amount, cutoff);
                let arg = arg.shift(db, amount, cutoff);
                db.make_term(TermData::Apply { sort, mode, fun, arg })
            }
            TermData::Bound { sort, index } => {
                let index = if *index < cutoff { index } else { index + amount };
                db.make_term(TermData::Bound { sort, index })
            }
            TermData::Free { .. } => self.clone(),
            TermData::Meta { .. } => self.clone(),
            TermData::InsertedMeta { .. } => self.clone(),
            TermData::Star => self.clone(),
            TermData::SuperStar => self.clone(),
        }
    }
}
