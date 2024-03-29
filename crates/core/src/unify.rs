
use std::borrow::Borrow;

use crate::utility::*;
use crate::value::*;
use crate::eval::*;
use crate::database::*;
use crate::metavar::*;

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
                match db.lookup_meta(*module, *name) {
                    MetaState::Solved(v) => result = v.perform_spine(db, spine.clone()),
                    MetaState::Unsolved | MetaState::Frozen => break
                }
            },
            _ => break
        }
    }
    result
}

pub fn unfold_meta_to_head(db: &Database, value: Value) -> Value {
    let mut result = value;
    while let ValueData::MetaVariable { name, module, spine, .. } = result.as_ref() {
        match db.lookup_meta(*module, *name) {
            MetaState::Solved(v) => result = v.perform_spine(db, spine.clone()),
            MetaState::Unsolved | MetaState::Frozen => break
        }
    }
    result
}

fn unify_spine(db: &mut Database, level: Level, lhs: Spine, rhs: Spine) -> Result<bool, ()> {
    if lhs.len() != rhs.len() { return Ok(false); }
    let mut result = true;
    for (a1, a2) in lhs.iter().cloned().zip(rhs.iter().cloned()) {
        let update = match (a1, a2) {
            (Action::Apply(m1, v1), Action::Apply(m2, v2)) => {
                m1 == m2 && unify(db, level, v1.force(db), v2.force(db))?
            }
            (Action::Project(v1), Action::Project(v2)) => v1 == v2,
            (Action::Subst(p1), Action::Subst(p2)) => {
                unify(db, level, p1, p2)?
            }
            (Action::Promote(v1, a1, b1), Action::Promote(v2, a2, b2)) => {
                v1 == v2 && unify(db, level, a1.force(db), a2.force(db))?
                && unify(db, level, b1.force(db), b2.force(db))?
            }
            (Action::Separate, Action::Separate) => true,
            _ => false
        };
        result &= update;
    }
    Ok(result)
}

// Unification is _proof-unification_, lhs and rhs should be erased to get object unification
pub fn unify(db: &mut Database, level: Level, lhs: Value, rhs: Value) -> Result<bool, ()> {
    // eprintln!("UNIFY:");
    // eprintln!("  {}", quote(db, lhs.clone(), level));
    // eprintln!("  {}", quote(db, rhs.clone(), level));
    let (lhst, rhst) = (lhs.clone(), rhs.clone());
    let lhs_borrow: &ValueData = lhs.borrow();
    let rhs_borrow: &ValueData = rhs.borrow();
    let result : bool = match (lhs_borrow.clone(), rhs_borrow.clone()) {
        (ValueData::Star, ValueData::Star) => true,
        (ValueData::SuperStar, ValueData::SuperStar) => true,
        (ValueData::Pi { sort:s1, mode:m1, name:n1, domain:d1, closure:c1 }
        , ValueData::Pi { sort:s2, mode:m2, name:n2, domain:d2, closure:c2 })
        => {
            let input = LazyValueData::var(db, s1, level);
            let c1 = c1.eval(db, EnvEntry::new(n1, m1, input.clone()));
            let c2 = c2.eval(db, EnvEntry::new(n2, m2, input));
            s1 == s2 && m1 == m2
            && unify(db, level, d1, d2)?
            && unify(db, level + 1, c1, c2)?
        }
        (ValueData::Intersect { name:n1, first:f1, second:s1 }
        , ValueData::Intersect { name:n2, first:f2, second:s2 })
        => {
            let input = LazyValueData::var(db, Sort::Term, level);
            let s1 = s1.eval(db, EnvEntry::new(n1, Mode::Free, input.clone()));
            let s2 = s2.eval(db, EnvEntry::new(n2, Mode::Free, input));
            unify(db, level, f1, f2)?
            && unify(db, level + 1, s1, s2)?
        }
        (ValueData::Equality { left:l1, right:r1, anno:a1 }
        , ValueData::Equality { left:l2, right:r2, anno:a2 })
        => {
            let (l1, l2) = (l1.force(db), l2.force(db));
            let (r1, r2) = (r1.force(db), r2.force(db));
            unify(db, level, l1, l2)?
            && unify(db, level, r1 ,r2)?
            && unify(db, level, a1, a2)?
        }
        (ValueData::Lambda { sort:s1, mode:m1, name:n1, domain:d1, closure:c1 }
        , ValueData::Lambda { sort:s2, mode:m2, name:n2, domain:d2, closure:c2, .. })
        => {
            let input = LazyValueData::var(db, s1, level);
            let c1 = c1.eval(db, EnvEntry::new(n1, m1, input.clone()));
            let c2 = c2.eval(db, EnvEntry::new(n2, m2, input));
            s1 == s2
            && unify(db, level, d1, d2)?
            && unify(db, level + 1, c1, c2)?
        }
        (ValueData::Pair { first:f1, second:s1, anno:a1 }
        , ValueData::Pair { first:f2, second:s2, anno:a2 })
        => {
            unify(db, level, f1, f2)?
            && unify(db, level, s1, s2)?
            && unify(db, level, a1, a2)?
        }
        (ValueData::Refl { input:i1 }, ValueData::Refl { input:i2 }) => {
            let i1 = i1.force(db);
            let i2 = i2.force(db);
            unify(db, level, i1, i2)?
        }
        (ValueData::Cast { input:i1, witness:w1, evidence:e1, spine:s1 }
        , ValueData::Cast { input:i2, witness:w2, evidence:e2, spine:s2 })
        => {
            unify(db, level, i1, i2)?
            && unify(db, level, w1, w2)?
            && unify(db, level, e1, e2)?
            && unify_spine(db, level, s1, s2)?
        }
        (ValueData::Variable { level:l1, spine:p1, .. }
        , ValueData::Variable { level:l2, spine:p2, .. })
        => {
            l1 == l2 && unify_spine(db, level, p1, p2)?
        }
        (ValueData::Reference { id:i1, spine:p1, unfolded:u1, .. }
        , ValueData::Reference { id:i2, spine:p2, unfolded:u2, .. })
        => {
            let folded_check = i1 == i2 && unify_spine(db, level, p1.clone(), p2.clone())?;
            let check_unfolded = || {
                let mut result = Ok(false);
                if let Some(u1) = u1 {
                    if let Some(u2) = u2 {
                        let u1 = u1.perform_spine(db, p1);
                        let u2 = u2.perform_spine(db, p2);
                        result = unify(db, level, u1, u2);
                    }
                }
                result
            };
            folded_check || check_unfolded()?
        }
        (ValueData::Reference { unfolded, spine, .. }, _) => {
            unfolded.as_ref()
                .map_or(Ok(false), |u| {
                    let u = u.clone().perform_spine(db, spine);
                    unify(db, level, u, rhs)
                })?
        }
        (_, ValueData::Reference { unfolded, spine, .. }) => {
            unfolded.as_ref()
                .map_or(Ok(false), |u| {
                    let u = u.clone().perform_spine(db, spine);
                    unify(db, level, lhs, u)
                })?
        }
        (ValueData::MetaVariable { module:m1, name:n1, spine:s1, .. },
            ValueData::MetaVariable { module:m2, name:n2, spine:s2, .. }) =>
        {
            let folded = n1 == n2 && unify_spine(db, level, s1.clone(), s2.clone())?;
            let unfolded = || {
                match (db.lookup_meta(m1, n1), db.lookup_meta(m2, n2)) {
                    (MetaState::Solved(lhs), MetaState::Solved(rhs)) => unify(db, level, lhs, rhs),
                    (MetaState::Solved(lhs), MetaState::Unsolved) => unify(db, level, lhs, rhs),
                    (MetaState::Unsolved, MetaState::Solved(rhs)) => unify(db, level, lhs, rhs),
                    _ => Ok(false)
                }
            };
            folded || unfolded()?
        }
        (ValueData::MetaVariable { name, module, spine, .. }, rhs) => {
            match db.lookup_meta(module, name) {
                MetaState::Unsolved => {
                    solve(db, module, level, name, spine.clone(), rhs.rced())?;
                    true
                }
                MetaState::Frozen => false,
                MetaState::Solved(lhs) => {
                    let lhs = lhs.perform_spine(db, spine);
                    unify(db, level, lhs, rhs.rced())?
                }
            }
        }
        (lhs, ValueData::MetaVariable { name, module, spine, .. }) => {
            match db.lookup_meta(module, name) {
                MetaState::Unsolved => {
                    solve(db, module, level, name, spine.clone(), lhs.rced())?;
                    true
                }
                MetaState::Frozen => false,
                MetaState::Solved(rhs) => {
                    let rhs = rhs.perform_spine(db, spine);
                    unify(db, level, lhs.rced(), rhs)?
                }
            }
        }
        _ => false
    };
    // eprintln!("UNIFY {}", result);
    // eprintln!("  {}", quote(db, lhst, level));
    // eprintln!("  {}", quote(db, rhst, level));
    Ok(result)
}


