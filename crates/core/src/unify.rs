
use std::borrow::Borrow;

use crate::utility::*;
use crate::value::*;
use crate::eval::*;
use crate::database::*;

pub fn unfold_to_head(db: &mut Database, value: Value) -> Value {
    let mut result = value;
    loop {
        match result.as_ref() {
            ValueData::Reference { unfolded, spine, .. } => {
                if let Some(unfolded) = unfolded {
                    let mut term = unfolded.clone();
                    term = term.perform_spine(db, spine.clone());
                    result = term;
                } else { break }
            },
            ValueData::MetaVariable { name, module, spine, .. } => {
                todo!()
                // match db.lookup_meta(*module, *name) {
                //     MetaState::Solved(v) => result = v.apply_spine(db, spine.clone()),
                //     MetaState::Unsolved | MetaState::Frozen => break
                // }
            },
            _ => break
        }
    }
    result
}

fn unify_spine(db: &mut Database, level: Level, lhs: Spine, rhs: Spine) -> bool {
    let mut result = true;
    for (a1, a2) in lhs.iter().cloned().zip(rhs.iter().cloned()) {
        let update = match (a1, a2) {
            (Action::Apply(m1, v1), Action::Apply(m2, v2)) => {
                let v1 = v1.force(db);
                let v2 = v2.force(db);
                m1 == m2 && unify(db, level, v1, v2)
            }
            (Action::Project(v1), Action::Project(v2)) => v1 == v2,
            (Action::EqInduct(d1), Action::EqInduct(d2)) => {
                let (p1, p2) = (d1.predicate.force(db), d2.predicate.force(db));
                let (l1, l2) = (d1.lhs.force(db), d2.lhs.force(db));
                let (r1, r2) = (d1.rhs.force(db), d2.rhs.force(db));
                let (c1, c2) = (d1.case.force(db), d2.case.force(db));
                let (d1, d2) = (d1.domain.force(db), d2.domain.force(db));
                unify(db, level, p1, p2)
                && unify(db, level, l1, l2)
                && unify(db, level, r1, r2)
                && unify(db, level, c1, c2)
                && unify(db, level, d1, d2)
            }
            (Action::Promote, Action::Promote) => true,
            (Action::Separate, Action::Separate) => true,
            _ => false
        };
        result &= update;
    }
    result
}

// Unification is _proof-unification_, lhs and rhs should be erased to get object unification
pub fn unify(db: &mut Database, level: Level, lhs: Value, rhs: Value) -> bool {
    // eprintln!("UNIFY:");
    // eprintln!("  {}", quote(db, lhs.clone(), level));
    // eprintln!("  {}", quote(db, rhs.clone(), level));
    let lhs_borrow: &ValueData = lhs.borrow();
    let rhs_borrow: &ValueData = rhs.borrow();
    match (lhs_borrow.clone(), rhs_borrow.clone()) {
        (ValueData::Star, ValueData::Star) => true,
        (ValueData::SuperStar, ValueData::SuperStar) => true,
        (ValueData::Pi { sort:s1, mode:m1, name:n1, domain:d1, closure:c1 }
        , ValueData::Pi { sort:s2, mode:m2, name:n2, domain:d2, closure:c2 })
        => {
            let input = LazyValueData::var(db, s1, level);
            let c1 = c1.eval(db, EnvEntry::new(n1, m1, input.clone()));
            let c2 = c2.eval(db, EnvEntry::new(n2, m2, input));
            s1 == s2 && m1 == m2
            && unify(db, level, d1, d2)
            && unify(db, level + 1, c1, c2)
        }
        (ValueData::Intersect { name:n1, first:f1, second:s1 }
        , ValueData::Intersect { name:n2, first:f2, second:s2 })
        => {
            let input = LazyValueData::var(db, Sort::Term, level);
            let s1 = s1.eval(db, EnvEntry::new(n1, Mode::Free, input.clone()));
            let s2 = s2.eval(db, EnvEntry::new(n2, Mode::Free, input));
            unify(db, level, f1, f2)
            && unify(db, level + 1, s1, s2)
        }
        (ValueData::Equality { left:l1, right:r1, anno:a1 }
        , ValueData::Equality { left:l2, right:r2, anno:a2 })
        => {
            let (l1, l2) = (l1.force(db), l2.force(db));
            let (r1, r2) = (r1.force(db), r2.force(db));
            unify(db, level, l1, l2)
            && unify(db, level, r1 ,r2)
            && unify(db, level, a1, a2)
        }
        (ValueData::Lambda { sort:s1, mode:m1, name:n1, domain:d1, closure:c1 }
        , ValueData::Lambda { sort:s2, mode:m2, name:n2, domain:d2, closure:c2, .. })
        => {
            let input = LazyValueData::var(db, s1, level);
            let c1 = c1.eval(db, EnvEntry::new(n1, m1, input.clone()));
            let c2 = c2.eval(db, EnvEntry::new(n2, m2, input));
            s1 == s2 && m1 == m2
            && unify(db, level, d1, d2)
            && unify(db, level + 1, c1, c2)
        }
        (ValueData::Pair { first:f1, second:s1, anno:a1 }
        , ValueData::Pair { first:f2, second:s2, anno:a2 })
        => {
            unify(db, level, f1, f2)
            && unify(db, level, s1, s2)
            && unify(db, level, a1, a2)
        }
        (ValueData::Refl { input:i1 }, ValueData::Refl { input:i2 }) => {
            let i1 = i1.force(db);
            let i2 = i2.force(db);
            unify(db, level, i1, i2)
        }
        (ValueData::Cast { witness:w1, evidence:e1, spine:s1 }
        , ValueData::Cast { witness:w2, evidence:e2, spine:s2 })
        => {
            unify(db, level, w1, w2)
            && unify(db, level, e1, e2)
            && unify_spine(db, level, s1, s2)
        }
        (ValueData::Variable { level:l1, spine:p1, .. }
        , ValueData::Variable { level:l2, spine:p2, .. })
        => {
            l1 == l2 && unify_spine(db, level, p1, p2)
        }
        (ValueData::Reference { id:i1, spine:p1, unfolded:u1, .. }
        , ValueData::Reference { id:i2, spine:p2, unfolded:u2, .. })
        => {
            let folded_check = i1 == i2 && unify_spine(db, level, p1.clone(), p2.clone());
            let check_unfolded = || {
                let mut result = false;
                if let Some(u1) = u1 {
                    if let Some(u2) = u2 {
                        let u1 = u1.perform_spine(db, p1);
                        let u2 = u2.perform_spine(db, p2);
                        result = unify(db, level, u1, u2);
                    }
                }
                result
            };
            folded_check || check_unfolded()
        }
        (ValueData::Reference { unfolded, spine, .. }, _) => {
            unfolded.as_ref()
                .map_or(false, |u| {
                    let u = u.clone().perform_spine(db, spine);
                    unify(db, level, u, rhs)
                })
        }
        (_, ValueData::Reference { unfolded, spine, .. }) => {
            unfolded.as_ref()
                .map_or(false, |u| {
                    let u = u.clone().perform_spine(db, spine);
                    unify(db, level, lhs, u)
                })
        }
        _ => false
    }
}

// (Value::MetaVariable { name:n1, spine:s1, .. },
//     Value::MetaVariable { name:n2, spine:s2, .. }) =>
// {
//     let sort = left.sort(db);
//     Ok(n1 == n2 && Value::unify_spine(db, sort, env, s1.clone(), s2.clone())?)
// }
// (Value::MetaVariable { name, module, spine, .. }, _) => {
//     metavar::solve(db, *module, env, *name, spine.clone(), right.clone())?;
//     Ok(true)
// }
// (_, Value::MetaVariable { name, module, spine, .. }) => {
//     metavar::solve(db, *module, env, *name, spine.clone(), left.clone())?;
//     Ok(true)
// }
