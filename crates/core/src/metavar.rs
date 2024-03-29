
use std::collections::HashMap;
use std::rc::Rc;

use crate::utility::*;
use crate::eval::*;
use crate::term::*;
use crate::value::*;
use crate::unify::*;
use crate::database::Database;

#[derive(Debug, Clone)]
pub enum MetaState {
    Unsolved,
    Frozen,
    Solved(Value),
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
    for action in spine.iter() {
        let Action::Apply(mode, arg) = action.clone() else { unimplemented!() };
        modes.push((mode, arg.sort()));
        let value = arg.force(db);
        let value = unfold_meta_to_head(db, value);
        match value.as_ref() {
            ValueData::Variable { level, spine, .. }
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

fn rename(db: &mut Database, meta: Symbol, renaming: &PartialRenaming, value: Value) -> Result<Term, ()> {
    fn rename_spine(db: &mut Database, meta: Symbol, renaming: &PartialRenaming, head: Term, spine: Spine) -> Result<Term, ()> {
        let mut result = head;
        for action in spine.iter() {
            let Action::Apply(mode, arg) = action else { unimplemented!() };
            let arg = rename(db, meta, renaming, arg.force(db))?;
            result = db.make_term(TermData::Apply {
                sort: result.sort(),
                mode: *mode,
                fun: result,
                arg
            });
        }
        Ok(result)
    }

    let value = unfold_meta_to_head(db, value);
    match value.as_ref() {
        ValueData::Variable { sort, level, spine } => {
            if let Some(renamed) = renaming.renaming.get(level) {
                let head = db.make_term(TermData::Bound { sort: *sort, index: renamed.to_index(*renaming.domain) });
                rename_spine(db, meta, renaming, head, spine.clone())
            } else {
                Err(())
            }
        }
        ValueData::MetaVariable { sort, name, module, spine } => {
            let sort = value.sort();
            if *name == meta {
                Err(())
            } else {
                let head = db.make_term(TermData::Meta { sort, module: *module, name: *name });
                rename_spine(db, meta, renaming, head, spine.clone())
            }
        }
        ValueData::Reference { sort, id, spine, .. } => {
            let head = db.make_term(TermData::Free { sort: *sort, id: id.clone() });
            rename_spine(db, meta, renaming, head, spine.clone())
        }
        ValueData::Pair { first, second, anno } => {
            let first = rename(db, meta, renaming, first.clone())?;
            let second = rename(db, meta, renaming, second.clone())?;
            let anno = rename(db, meta, renaming, anno.clone())?;
            Ok(db.make_term(TermData::Pair {
                first,
                second,
                anno,
            }))
        }
        ValueData::Refl { input } => {
            let input = rename(db, meta, renaming, input.force(db))?;
            Ok(db.make_term(TermData::Refl { input }))
        }
        ValueData::Cast { input, witness, evidence, spine } => {
            let input = rename(db, meta, renaming, input.clone())?;
            let witness = rename(db, meta, renaming, witness.clone())?;
            let evidence = rename(db, meta, renaming, evidence.clone())?;
            let head = db.make_term(TermData::Cast { input, witness, evidence });
            rename_spine(db, meta, renaming, head, spine.clone())
        }
        ValueData::Lambda { sort, mode, name, domain, closure } => {
            let domain = rename(db, meta, renaming, domain.clone())?;
            let v = LazyValueData::var(db, domain.sort(), renaming.codomain);
            let arg = EnvEntry::new(*name, *mode, v);
            let body = closure.eval(db, arg);
            let body = rename(db, meta, &lift(renaming), body)?;
            Ok(db.make_term(TermData::Lambda {
                sort: *sort,
                domain,
                mode: *mode,
                name: *name,
                body
            }))
        }
        ValueData::Pi { sort, mode, name, domain, closure } => {
            let domain = rename(db, meta, renaming, domain.clone())?;
            let v = LazyValueData::var(db, domain.sort(), renaming.codomain);
            let arg = EnvEntry::new(*name, *mode, v);
            let body = closure.eval(db, arg);
            let body = rename(db, meta, &lift(renaming), body)?;
            Ok(db.make_term(TermData::Pi {
                sort: *sort,
                mode: *mode,
                name: *name,
                domain,
                body
            }))
        }
        ValueData::Intersect { name, first, second } => {
            let first = rename(db, meta, renaming, first.clone())?;
            let v = LazyValueData::var(db, first.sort(), renaming.codomain);
            let arg = EnvEntry::new(*name, Mode::Free, v);
            let second = second.eval(db, arg);
            let second = rename(db, meta, &lift(renaming), second)?;
            Ok(db.make_term(TermData::Intersect {
                name: *name,
                first,
                second
            }))
        }
        ValueData::Equality { left, right, anno } => {
            let anno = rename(db, meta, renaming, anno.clone())?;
            let left = rename(db, meta, renaming, left.force(db))?;
            let right = rename(db, meta, renaming, right.force(db))?;
            Ok(db.make_term(TermData::Equality { left, right, anno }))
        }
        ValueData::Star => Ok(db.make_term(TermData::Star)),
        ValueData::SuperStar => Ok(db.make_term(TermData::SuperStar)),
    }
}

fn wrap_in_lambdas(db: &Database, env: Level, modes: Vec<(Mode, Sort)>, term: Term) -> Term {
    let mut result = term;
    for i in 0..*env {
        let (mode, domain_sort) = modes[i];
        result = db.make_term(TermData::Lambda {
            sort: result.sort(),
            mode,
            name: Symbol::from(format!("x{}", i).as_str()),
            body: result,
            domain: db.make_term(TermData::SuperStar),
        })
    }
    result
}

pub fn solve(db: &mut Database, module: Symbol, env: Level, meta: Symbol, spine: Spine, rhs: Value) -> Result<(), ()> {
    let (renaming, mut modes) = invert(db, env, spine)?;
    modes.reverse();
    let domain = renaming.domain;
    let rhs = rename(db, meta, &renaming, rhs)?;
    let solution = wrap_in_lambdas(db, domain, modes, rhs);
    let solution = eval(db, Env::new(), solution);
    db.insert_meta(module, meta, solution)
        .map_err(|_| ())?;
    Ok(())
}
