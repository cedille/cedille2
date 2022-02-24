
use std::rc::Rc;

use crate::common::*;
use crate::database::Database;
use crate::lang::elaborator::{Context, ElabError};
use crate::kernel::core::Term;
use crate::kernel::value::{Value, ValueEx, Spine, SpineEntry, EnvEntry};

#[derive(Debug, Clone, Copy)]
struct MatchArg<'a> {
    occurrence: Option<usize>,
    index: Index,
    level: Level,
    term: &'a Rc<Value>,
    ty: &'a Rc<Value>
}

impl<'a> MatchArg<'a> {
    fn update(mut self, ty: &'a Rc<Value>) -> Self {
        self.ty = ty;
        self
    }

    fn increment(mut self) -> Self {
        self.index = self.index + 1;
        self.level = self.level + 1;
        self
    }
}

struct MatchMutArg<'a> {
    db: &'a mut Database,
    matched: bool,
    current: usize
}

pub fn match_term(db: &mut Database
    , ctx: Context
    , occurrence: Option<usize>
    , term: &Rc<Value>
    , ty: &Rc<Value>)
    -> Result<Rc<Term>, ElabError>
{
    let level = ctx.env_lvl();
    let arg = MatchArg {
        occurrence,
        index: 0.into(),
        level,
        term,
        ty
    };
    let mut mut_arg = MatchMutArg {
        db,
        matched: false,
        current: 0
    };

    let matched_ty = match_term_helper(arg, &mut mut_arg)
        .map_err(|_| ElabError::RewriteFailed)?;
    Ok(Rc::new(matched_ty))
}

fn match_term_helper(arg: MatchArg, mut_arg: &mut MatchMutArg) -> Result<Term, ()>
{
    fn process_spine_entry(arg: MatchArg, mut_arg: &mut MatchMutArg, entry: &SpineEntry) -> Result<(ApplyType, Term), ()> {
        let term = entry.value.force(mut_arg.db);
        let term = match_term_helper(arg.update(&term), mut_arg)?;
        Ok((entry.apply_type, term))
    }

    let build_apply = |acc:Term, (apply_type, t)| {
        let sort = acc.sort();
        Term::Apply {
            sort,
            apply_type,
            fun: Rc::new(acc),
            arg: Rc::new(t),
        }
    };

    if Value::unify(mut_arg.db, arg.level, arg.term, arg.ty)? {
        let result = if arg.occurrence.map_or(true, |occ| occ == mut_arg.current) {
            mut_arg.matched = true;
            Term::Bound { sort: Sort::Term, index: arg.index }
        } else { arg.ty.quote(mut_arg.db, arg.level) };
        mut_arg.current += 1;
        Ok(result)
    } else {
        let result = match arg.ty.as_ref() {
            Value::Variable { sort, level:vlevel, spine } => {
                let mut result = Value::variable(*sort, *vlevel).quote(mut_arg.db, arg.level);
                for entry in spine.iter() {
                    let entry = process_spine_entry(arg, mut_arg, entry)?;
                    result = build_apply(result, entry);
                }
                result
            }
            Value::MetaVariable { name, module, spine }  => {
                Value::meta(*name, *module, spine.clone()).quote(mut_arg.db, arg.level)
            }
            Value::Reference { sort, id, spine, .. } if spine.len() == 0 => {
                Term::Free { sort: *sort, id: id.clone() }
            }
            Value::Reference { sort, id, spine, .. } => {
                let head = Value::reference(*sort, id.clone(), Spine::new(), None);
                let mut result = match_term_helper(arg.update(&head), mut_arg)?;
                for entry in spine.iter() {
                    let entry = process_spine_entry(arg, mut_arg, entry)?;
                    result = build_apply(result, entry);
                }
                result
            }
            Value::Lambda { sort, domain_sort, mode, name, closure } => {
                let closure = closure.eval(mut_arg.db, EnvEntry::new(*name, *mode, Value::variable(*domain_sort, arg.level)));
                let closure = match_term_helper(arg.update(&closure).increment(), mut_arg)?;
                Term::Lambda {
                    sort: *sort,
                    domain_sort: *domain_sort,
                    mode: *mode,
                    name: *name,
                    body: Rc::new(closure)
                }
            }
            Value::Pi { sort, mode, name, domain, closure } => {
                let closure = closure.eval(mut_arg.db, EnvEntry::new(*name, *mode, Value::variable(domain.sort(mut_arg.db), arg.level)));
                let domain = match_term_helper(arg.update(domain), mut_arg)?;
                let closure = match_term_helper(arg.update(&closure).increment(), mut_arg)?;
                Term::Pi {
                    sort: *sort,
                    mode: *mode,
                    name: *name,
                    domain: Rc::new(domain),
                    body: Rc::new(closure)
                }
            }
            Value::IntersectType { name, first, second } => {
                let second = second.eval(mut_arg.db, EnvEntry::new(*name, Mode::Free, Value::variable(first.sort(mut_arg.db), arg.level)));
                let first = match_term_helper(arg.update(first), mut_arg)?;
                let second = match_term_helper(arg.update(&second).increment(), mut_arg)?;
                Term::IntersectType {
                    name: *name,
                    first: Rc::new(first),
                    second: Rc::new(second)
                }
            }
            Value::Equality { left, right } => {
                let left = match_term_helper(arg.update(left), mut_arg)?;
                let right = match_term_helper(arg.update(right), mut_arg)?;
                Term::Equality {
                    left: Rc::new(left),
                    right: Rc::new(right)
                }
            }
            Value::Star => Term::Star,
            Value::SuperStar => unreachable!(),
        };
        Ok(result)
    }
}

