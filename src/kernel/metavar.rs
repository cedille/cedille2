
use std::collections::HashMap;
use std::rc::Rc;

use colored::Colorize;

use crate::common::*;
use crate::kernel::core::Term;
use crate::kernel::value::{Value, Spine, Environment, EnvEntry, ValueEx};
use crate::database::Database;

#[derive(Debug, Clone)]
pub enum MetaState {
    Unsolved,
    Frozen,
    Solved(Rc<Value>),
}

struct PartialRenaming {
    domain: Level,
    codomain: Level,
    renaming: HashMap<Level, Level>
}

fn lift(renaming: &PartialRenaming) -> PartialRenaming {
    let PartialRenaming { domain , codomain, renaming } = renaming;
    let mut renaming = renaming.clone();
    renaming.insert(*codomain, *domain);
    PartialRenaming {
        domain: *domain + 1,
        codomain: *codomain + 1,
        renaming
    }
}

fn invert(db: &Database, env: Level, spine: Spine) -> Result<(PartialRenaming, Vec<(Mode, Sort)>), ()> {
    let mut result = PartialRenaming { 
        domain: 0.into(),
        codomain: env,
        renaming: HashMap::new()
    };
    let mut modes = vec![];
    for entry in spine.iter() {
        let mode = entry.apply_type.to_mode();
        modes.push((mode, entry.value.sort(db)));
        let value = entry.value.force(db);
        let value = Value::unfold_meta_to_head(db, value);
        match value.as_ref() {
            Value::Variable { level, spine, .. }
            if spine.is_empty() && !result.renaming.contains_key(level) =>
            {
                result.renaming.insert(*level, result.domain);
                result.domain = result.domain + 1;
            },
            _ => return Err(())
        }
    }
    Ok((result, modes))
}

fn rename(db: &Database, meta: Symbol, renaming: &PartialRenaming, value: Rc<Value>) -> Result<Rc<Term>, ()> {
    fn rename_spine(db: &Database, meta: Symbol, renaming: &PartialRenaming, head: Term, spine: Spine) -> Result<Rc<Term>, ()> {
        let mut result = head;
        for entry in spine.iter() {
            let arg = rename(db, meta, renaming, entry.value.force(db))?;
            result = Term::Apply {
                sort: result.sort(),
                apply_type: entry.apply_type,
                fun: Rc::new(result),
                arg
            };
        }
        Ok(Rc::new(result))
    }

    let value = Value::unfold_meta_to_head(db, value);
    match value.as_ref() {
        Value::Variable { sort, level, spine } => {
            if let Some(renamed) = renaming.renaming.get(level) {
                let head = Term::Bound { sort: *sort, index: renamed.to_index(*renaming.domain) };
                rename_spine(db, meta, renaming, head, spine.clone())
            } else {
                Err(())
            }
        }
        Value::MetaVariable { name, module, spine } => {
            let sort = value.sort(db);
            if *name == meta {
                Err(())
            } else {
                let head = Term::Meta { sort, name: meta };
                rename_spine(db, meta, renaming, head, spine.clone())
            }
        }
        Value::Reference { sort, id, spine, .. } => {
            let head = Term::Free { sort: *sort, id: id.clone() };
            rename_spine(db, meta, renaming, head, spine.clone())
        }
        Value::Lambda { sort, domain_sort, mode, name, closure } => {
            let arg = EnvEntry::new(*name, *mode, Value::variable(*domain_sort, renaming.codomain));
            let body = closure.eval(db, arg);
            let body = rename(db, meta, &lift(renaming), body)?;
            Ok(Rc::new(Term::Lambda {
                sort: *sort,
                domain_sort: *domain_sort,
                mode: *mode,
                name: *name,
                body
            }))
        }
        Value::Pi { sort, mode, name, domain, closure } => {
            let domain = rename(db, meta, renaming, domain.clone())?;
            let arg = EnvEntry::new(*name, *mode, Value::variable(domain.sort(), renaming.codomain));
            let body = closure.eval(db, arg);
            let body = rename(db, meta, &lift(renaming), body)?;
            Ok(Rc::new(Term::Pi {
                sort: *sort,
                mode: *mode,
                name: *name,
                domain,
                body
            }))
        }
        Value::IntersectType { name, first, second } => {
            let first = rename(db, meta, renaming, first.clone())?;
            let arg = EnvEntry::new(*name, Mode::Free, Value::variable(first.sort(), renaming.codomain));
            let second = second.eval(db, arg);
            let second = rename(db, meta, &lift(renaming), second)?;
            Ok(Rc::new(Term::IntersectType {
                name: *name,
                first,
                second
            }))
        }
        Value::Equality { left, right } => {
            let left = rename(db, meta, renaming, left.clone())?;
            let right = rename(db, meta, renaming, right.clone())?;
            Ok(Rc::new(Term::Equality { left, right }))
        }
        Value::Star => Ok(Rc::new(Term::Star)),
        Value::SuperStar => unreachable!(),
    }
}

fn wrap_in_lambdas(env: Level, modes: Vec<(Mode, Sort)>, term: Rc<Term>) -> Rc<Term> {
    let mut result = term;
    for i in 0..*env {
        let (mode, domain_sort) = modes[i];
        result = Rc::new(Term::Lambda {
            sort: result.sort(),
            domain_sort,
            mode,
            name: Symbol::from(format!("x{}", i).as_str()),
            body: result
        })
    }
    result
}

pub fn solve(db: &mut Database, module: Symbol, env: Level, meta: Symbol, spine: Spine, rhs: Rc<Value>) -> Result<(), ()> {
    let (renaming, mut modes) = invert(db, env, spine)?;
    modes.reverse();
    let domain = renaming.domain;
    let rhs = rename(db, meta, &renaming, rhs)?;
    let solution = wrap_in_lambdas(domain, modes, rhs);
    let solution = Value::eval(db, module, Environment::new(), solution);
    db.insert_meta(module, meta, solution)
        .map_err(|_| ())?;
    Ok(())
}
