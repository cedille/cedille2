
use std::collections::HashMap;
use std::rc::Rc;

use crate::utility::*;
use crate::term::*;
use crate::value::*;
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
    todo!()
    // let mut result = PartialRenaming { 
    //     domain: 0.into(),
    //     codomain: env,
    //     renaming: HashMap::new()
    // };
    // let mut modes = vec![];
    // for entry in spine.iter() {
    //     let mode = entry.mode;
    //     modes.push((mode, entry.value.sort(db)));
    //     let value = entry.value.force(db);
    //     let value = Value::unfold_meta_to_head(db, value);
    //     match value.as_ref() {
    //         Value::Variable { level, spine, .. }
    //         if spine.is_empty() && !result.renaming.contains_key(level) =>
    //         {
    //             result.renaming.insert(*level, result.domain);
    //             result.domain = result.domain + 1;
    //         },
    //         _ => return Err(())
    //     }
    // }
    // Ok((result, modes))
}

fn rename(db: &mut Database, meta: Symbol, renaming: &PartialRenaming, value: Rc<Value>) -> Result<Term, ()> {
    todo!()
    // fn rename_spine(db: &mut Database, meta: Symbol, renaming: &PartialRenaming, head: Term, spine: Spine) -> Result<Term, ()> {
    //     let mut result = head;
    //     for entry in spine.iter() {
    //         let arg = rename(db, meta, renaming, entry.value.force(db))?;
    //         result = db.make(TermData::Apply {
    //             sort: result.sort(),
    //             mode: entry.mode,
    //             fun: result,
    //             arg
    //         });
    //     }
    //     Ok(result)
    // }

    // let value = Value::unfold_meta_to_head(db, value);
    // match value.as_ref() {
    //     Value::Variable { sort, level, spine } => {
    //         if let Some(renamed) = renaming.renaming.get(level) {
    //             let head = db.make(TermData::Bound { sort: *sort, index: renamed.to_index(*renaming.domain) });
    //             rename_spine(db, meta, renaming, head, spine.clone())
    //         } else {
    //             Err(())
    //         }
    //     }
    //     Value::MetaVariable { name, spine, .. } => {
    //         let sort = value.sort(db);
    //         if *name == meta {
    //             Err(())
    //         } else {
    //             let head = db.make(TermData::Meta { sort, name: *name });
    //             rename_spine(db, meta, renaming, head, spine.clone())
    //         }
    //     }
    //     Value::Reference { sort, id, spine, .. } => {
    //         let head = db.make(TermData::Free { sort: *sort, id: id.clone() });
    //         rename_spine(db, meta, renaming, head, spine.clone())
    //     }
    //     Value::Lambda { sort, domain_sort, mode, name, closure } => {
    //         let arg = EnvEntry::new(*name, *mode, Value::variable(*domain_sort, renaming.codomain));
    //         let body = closure.eval(db, arg);
    //         let body = rename(db, meta, &lift(renaming), body)?;
    //         Ok(db.make(TermData::Lambda {
    //             sort: *sort,
    //             domain_sort: *domain_sort,
    //             mode: *mode,
    //             name: *name,
    //             body
    //         }))
    //     }
    //     Value::Pi { sort, mode, name, domain, closure } => {
    //         let domain = rename(db, meta, renaming, domain.clone())?;
    //         let arg = EnvEntry::new(*name, *mode, Value::variable(domain.sort(), renaming.codomain));
    //         let body = closure.eval(db, arg);
    //         let body = rename(db, meta, &lift(renaming), body)?;
    //         Ok(db.make(TermData::Pi {
    //             sort: *sort,
    //             mode: *mode,
    //             name: *name,
    //             domain,
    //             body
    //         }))
    //     }
    //     Value::Intersect { name, first, second } => {
    //         let first = rename(db, meta, renaming, first.clone())?;
    //         let arg = EnvEntry::new(*name, Mode::Free, Value::variable(first.sort(), renaming.codomain));
    //         let second = second.eval(db, arg);
    //         let second = rename(db, meta, &lift(renaming), second)?;
    //         Ok(db.make(TermData::Intersect {
    //             name: *name,
    //             first,
    //             second
    //         }))
    //     }
    //     Value::Equality { left, right } => {
    //         let left = rename(db, meta, renaming, left.clone())?;
    //         let right = rename(db, meta, renaming, right.clone())?;
    //         Ok(db.make(TermData::Equality { left, right }))
    //     }
    //     Value::Star => Ok(db.make(TermData::Star)),
    //     Value::SuperStar => unreachable!(),
    // }
}

fn wrap_in_lambdas(db: &mut Database, env: Level, modes: Vec<(Mode, Sort)>, term: Term) -> Term {
    todo!()
    // let mut result = term;
    // for i in 0..*env {
    //     let (mode, domain_sort) = modes[i];
    //     result = db.make(TermData::Lambda {
    //         sort: result.sort(),
    //         domain_sort,
    //         mode,
    //         name: Symbol::from(format!("x{}", i).as_str()),
    //         body: result
    //     })
    // }
    // result
}

pub fn solve(db: &mut Database, module: Symbol, env: Level, meta: Symbol, spine: Spine, rhs: Rc<Value>) -> Result<(), ()> {
    let (renaming, mut modes) = invert(db, env, spine)?;
    modes.reverse();
    let domain = renaming.domain;
    let rhs = rename(db, meta, &renaming, rhs)?;
    let solution = wrap_in_lambdas(db, domain, modes, rhs);
    // TODO:
    // let solution = Value::eval(db, module, Environment::new(), solution);
    // db.insert_meta(module, meta, solution)
    //     .map_err(|_| ())?;
    Ok(())
}
