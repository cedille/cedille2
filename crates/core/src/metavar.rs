
use std::collections::HashMap;

use imbl::Vector;

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

#[derive(Debug)]
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
        match value.head() {
            Head::Variable { level, .. }
            if value.spine().is_empty() && !result.renaming.contains_key(&level) =>
            {
                result.renaming.insert(level, result.domain);
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
            match action.clone() {
                Action::Apply(mode, arg) => {
                    let arg = rename(db, meta, renaming, arg.force(db))?;
                    result = db.make_term(TermData::Apply {
                        sort: result.sort(),
                        mode,
                        fun: result,
                        arg
                    });
                }
                Action::Project(variant) => {
                    result = db.make_term(TermData::Project {
                        variant,
                        body: result,
                    });
                }
                Action::Subst(predicate) => {
                    let predicate = rename(db, meta, renaming, predicate)?;
                    result = db.make_term(TermData::Subst {
                        predicate,
                        equation: result,
                    });
                }
                Action::Promote(variant, lhs, rhs) => {
                    let lhs = rename(db, meta, renaming, lhs.force(db))?;
                    let rhs = rename(db, meta, renaming, rhs.force(db))?;
                    result = db.make_term(TermData::Promote {
                        variant,
                        equation: result,
                        lhs,
                        rhs,
                    });
                }
                Action::Separate => {
                    result = db.make_term(TermData::Separate {
                        equation: result
                    })
                }
            }
        }
        Ok(result)
    }

    let value = unfold_meta_to_head(db, value);
    match value.head() {
        Head::Variable { sort, level, .. } => {
            if let Some(renamed) = renaming.renaming.get(&level) {
                let head = db.make_term(TermData::Bound { sort, index: renamed.to_index(*renaming.domain) });
                rename_spine(db, meta, renaming, head, value.spine())
            } else {
                Err(())
            }
        }
        Head::MetaVariable { sort, name, module } => {
            let sort = value.sort();
            if name == meta {
                Err(())
            } else {
                let head = db.make_term(TermData::Meta { sort, module, name });
                rename_spine(db, meta, renaming, head, value.spine())
            }
        }
        Head::Reference { sort, id, .. } => {
            let head = db.make_term(TermData::Free { sort, id });
            rename_spine(db, meta, renaming, head, value.spine())
        }
        Head::Pair { first, second, anno } => {
            let first = rename(db, meta, renaming, first.clone())?;
            let second = rename(db, meta, renaming, second.clone())?;
            let anno = rename(db, meta, renaming, anno.clone())?;
            Ok(db.make_term(TermData::Pair {
                first,
                second,
                anno,
            }))
        }
        Head::Refl { input } => {
            let input = rename(db, meta, renaming, input.force(db))?;
            Ok(db.make_term(TermData::Refl { input }))
        }
        Head::Cast { input, witness, evidence } => {
            let input = rename(db, meta, renaming, input.clone())?;
            let witness = rename(db, meta, renaming, witness.clone())?;
            let evidence = rename(db, meta, renaming, evidence.clone())?;
            let head = db.make_term(TermData::Cast { input, witness, evidence });
            rename_spine(db, meta, renaming, head, value.spine())
        }
        Head::Lambda { sort, mode, name, domain, closure } => {
            let domain = rename(db, meta, renaming, domain.clone())?;
            let v = LazyValueData::var(db, domain.sort(), renaming.codomain);
            let arg = EnvEntry::new(name, mode, v);
            let body = closure.eval(db, arg);
            let body = rename(db, meta, &lift(renaming), body)?;
            Ok(db.make_term(TermData::Lambda {
                sort,
                domain,
                mode,
                name,
                body
            }))
        }
        Head::Pi { sort, mode, name, domain, closure } => {
            let domain = rename(db, meta, renaming, domain.clone())?;
            let v = LazyValueData::var(db, domain.sort(), renaming.codomain);
            let arg = EnvEntry::new(name, mode, v);
            let body = closure.eval(db, arg);
            let body = rename(db, meta, &lift(renaming), body)?;
            Ok(db.make_term(TermData::Pi {
                sort,
                mode,
                name,
                domain,
                body
            }))
        }
        Head::Intersect { name, first, second } => {
            let first = rename(db, meta, renaming, first.clone())?;
            let v = LazyValueData::var(db, first.sort(), renaming.codomain);
            let arg = EnvEntry::new(name, Mode::Free, v);
            let second = second.eval(db, arg);
            let second = rename(db, meta, &lift(renaming), second)?;
            Ok(db.make_term(TermData::Intersect {
                name,
                first,
                second
            }))
        }
        Head::Equality { left, right, anno } => {
            let anno = rename(db, meta, renaming, anno.clone())?;
            let left = rename(db, meta, renaming, left.force(db))?;
            let right = rename(db, meta, renaming, right.force(db))?;
            Ok(db.make_term(TermData::Equality { left, right, anno }))
        }
        Head::Star => Ok(db.make_term(TermData::Star)),
        Head::SuperStar => Ok(db.make_term(TermData::SuperStar)),
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
    // eprintln!("SOLVING:");
    // eprint!("  {}", meta);
    // for action in spine.iter() {
    //     eprint!(" {}", action);
    // }
    // eprintln!();
    // eprint!("  {}", rhs.head());
    // for action in rhs.spine().iter() {
    //     eprint!(" {}", action);
    // }
    // eprintln!();
    let (renaming, mut modes) = invert(db, env, spine)?;
    //eprintln!("RENAMING: {:#?}", renaming);
    modes.reverse();
    let domain = renaming.domain;
    let rhs = rename(db, meta, &renaming, rhs)?;
    //eprintln!("RENAMED RHS: {}", rhs);
    let solution = wrap_in_lambdas(db, domain, modes, rhs);
    let solution = eval(db, Env::new(), solution);
    db.insert_meta(module, meta, solution)
        .map_err(|_| ())?;
    Ok(())
}

fn is_meta_spine(term: &Term) -> bool {
    match term.cloned() {
        TermData::Apply { fun, .. } => is_meta_spine(&fun),
        TermData::Meta { .. } => true,
        TermData::InsertedMeta { .. } => true,
        _ => false
    }
}

fn zonk_meta(db: &Database, env: Env, mut term: Term) -> Term {
    let mut spine = Vector::new();
    while let TermData::Apply { mode, fun, arg, .. } = term.cloned() {
        spine.push_front((mode, arg));
        term = fun;
    }
    match term.cloned() {
        TermData::Meta { module, name, .. } => {
            match db.lookup_meta(module, name) {
                MetaState::Unsolved | MetaState::Frozen => term,
                MetaState::Solved(mut result) => {
                    for (mode, arg) in spine.iter().cloned() {
                        let arg = LazyValueData::lazy(db, env.clone(), arg);
                        let action = Action::Apply(mode, arg);
                        result = result.perform(db, action);
                    }
                    quote(db, result, env.len().into())
                }
            }
        }
        TermData::InsertedMeta { module, name, mask, .. } => {
            match db.lookup_meta(module, name) {
                MetaState::Unsolved | MetaState::Frozen => term,
                MetaState::Solved(mut result) => {
                    for (i, b) in mask.iter().enumerate() {
                        let EnvBound::Bound = b else { continue };
                        let arg = env.get(i).unwrap();
                        let action = Action::Apply(arg.mode, arg.value.clone());
                        result = result.perform(db, action)
                    }
                    quote(db, result, env.len().into())
                }
            }
        }
        _ => unreachable!()
    }
}

pub fn zonk(db: &Database, env: Env, term: Term) -> Term {
    return term;
    match term.cloned() {
        TermData::Lambda { sort, mode, name, domain, body } => {
            let domain = zonk(db, env.clone(), domain);
            let body = zonk(db, env.clone(), body);
            db.make_term(TermData::Lambda { sort, mode, name, domain, body })
        }
        TermData::Let { sort, name, let_body, body } => {
            let let_body = zonk(db, env.clone(), let_body);
            let body = zonk(db, env.clone(), body);
            db.make_term(TermData::Let { sort, name, let_body, body })
        }
        TermData::Pi { sort, mode, name, domain, body } => {
            let domain = zonk(db, env.clone(), domain);
            let body = zonk(db, env.clone(), body);
            db.make_term(TermData::Pi { sort, mode, name, domain, body })
        }
        TermData::Intersect { name, first, second } => {
            let first = zonk(db, env.clone(), first);
            let second = zonk(db, env.clone(), second);
            db.make_term(TermData::Intersect { name, first, second })
        }
        TermData::Equality { left, right, anno } => {
            let left = zonk(db, env.clone(), left);
            let right = zonk(db, env.clone(), right);
            let anno = zonk(db, env.clone(), anno);
            db.make_term(TermData::Equality { left, right, anno })
        }
        TermData::Project { variant, body } => {
            let body = zonk(db, env.clone(), body);
            db.make_term(TermData::Project { variant, body })
        }
        TermData::Pair { first, second, anno } => {
            let first = zonk(db, env.clone(), first);
            let second = zonk(db, env.clone(), second);
            let anno = zonk(db, env.clone(), anno);
            db.make_term(TermData::Pair { first, second, anno })
        }
        TermData::Separate { equation } => {
            let equation = zonk(db, env.clone(), equation);
            db.make_term(TermData::Separate { equation })
        }
        TermData::Refl { input } => {
            let input = zonk(db, env.clone(), input);
            db.make_term(TermData::Refl { input })
        }
        TermData::Cast { input, witness, evidence } => {
            let input = zonk(db, env.clone(), input);
            let witness = zonk(db, env.clone(), witness);
            let evidence = zonk(db, env.clone(), evidence);
            db.make_term(TermData::Cast { input, witness, evidence })
        }
        TermData::Promote { variant, equation, lhs, rhs } => {
            let equation = zonk(db, env.clone(), equation);
            let lhs = zonk(db, env.clone(), lhs);
            let rhs = zonk(db, env.clone(), rhs);
            db.make_term(TermData::Promote { variant, equation, lhs, rhs })
        }
        TermData::Subst { predicate, equation } => {
            let predicate = zonk(db, env.clone(), predicate);
            let equation = zonk(db, env.clone(), equation);
            db.make_term(TermData::Subst { predicate, equation })
        }
        TermData::Apply { sort, mode, fun, arg } => {
            if is_meta_spine(&term) {
                zonk_meta(db, env, term)
            } else {
                let fun = zonk(db, env.clone(), fun);
                let arg = zonk(db, env.clone(), arg);
                db.make_term(TermData::Apply { sort, mode, fun, arg })
            }
        }
        TermData::Bound { .. } | TermData::Free { .. } => term,
        TermData::Meta { .. } | TermData::InsertedMeta { .. } => term,
        TermData::Star => term,
        TermData::SuperStar => term,
    }
}