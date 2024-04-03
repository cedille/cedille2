
use std::borrow::Borrow;

use crate::utility::*;
use crate::value::*;
use crate::eval::*;
use crate::database::*;
use crate::metavar::*;

pub fn unfold_to_head(db: &mut Database, value: Value) -> Value {
    let mut result = value;
    loop {
        match result.head() {
            Head::Reference { unfolded, .. } => {
                if let Some(unfolded) = unfolded {
                    let mut term = unfolded.clone();
                    term = term.perform_spine(db, result.spine());
                    result = term;
                } else { break }
            },
            Head::MetaVariable { name, module, .. } => {
                match db.lookup_meta(module, name) {
                    MetaState::Solved(v) => result = v.perform_spine(db, result.spine()),
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
    while let Head::MetaVariable { name, module, .. } = result.head() {
        match db.lookup_meta(module, name) {
            MetaState::Solved(v) => result = v.perform_spine(db, result.spine()),
            MetaState::Unsolved | MetaState::Frozen => break
        }
    }
    result
}

fn erase_spine(spine: Spine) -> Result<Spine, ()> {
    let mut result = Spine::new();
    for action in spine.iter() {
        match action {
            Action::Apply(Mode::Free, _) => { result.push_back(action.clone()) }
            Action::Apply(Mode::TypeLevel, _) => { return Err(()) }
            _ => { }
        }
    }
    Ok(result)
}

fn unify_spine(db: &mut Database, typed: bool, level: Level, lhs: Value, rhs: Value) -> Result<bool, ()> {
    let (lhs_head, rhs_head) = (lhs.head(), rhs.head());
    let (mut lhs, mut rhs) = (lhs.spine(), rhs.spine());
    let mut result = true;
    // First, try to unify assuming a typed setting
    while !lhs.is_empty() || !rhs.is_empty() {
        // eprintln!("UNIFY SPINE");
        // eprintln!("  {}", lhs.get(0).map_or("None".to_string(), |a| a.to_string()));
        // eprintln!("  {}", rhs.get(0).map_or("None".to_string(), |a| a.to_string()));
        match (lhs.get(0).cloned(), rhs.get(0).cloned()) {
            (Some(Action::Apply(Mode::TypeLevel, v1)), Some(Action::Apply(Mode::TypeLevel, v2)))
            | (Some(Action::Apply(Mode::Free, v1)), Some(Action::Apply(Mode::Free, v2))) => {
                result &= unify(db, typed, level, v1.force(db), v2.force(db))?;
            }
            (Some(Action::Apply(Mode::Erased, v1)), Some(Action::Apply(Mode::Erased, v2))) => {
                if typed { unify(db, typed, level, v1.force(db), v2.force(db)).ok(); }
            }
            (Some(Action::Project(_)), Some(Action::Project(_))) => { },
            (Some(Action::Subst(p1)), Some(Action::Subst(p2))) => {
                if typed { unify(db, typed, level, p1, p2).ok(); }
            }
            (Some(Action::Promote(_, a1, b1)), Some(Action::Promote(_, a2, b2))) => {
                if typed {
                    unify(db, typed, level, a1.force(db), a2.force(db)).ok();
                    unify(db, typed, level, b1.force(db), b2.force(db)).ok();
                }
            }
            (Some(Action::Separate), Some(Action::Separate)) => {  },
            _ => break
        }
        lhs.pop_front();
        rhs.pop_front();
    }
    // If there is still stuff in either spine, it must be a non-well-typed conversion
    // Second, erase the spine
    if !lhs.is_empty() || !rhs.is_empty() {
        let erase_lhs_spine = erase_spine(lhs)?;
        let erase_rhs_spine = erase_spine(rhs)?;
        let lhs: Value = lhs_head.into();
        let lhs = lhs.perform_spine(db, erase_lhs_spine);
        let rhs: Value = rhs_head.into();
        let rhs = rhs.perform_spine(db, erase_rhs_spine);
        result &= unify(db, false, level, lhs, rhs)?;
    }
    Ok(result)
}

pub fn unify(db: &mut Database, typed: bool, level: Level, lhs: Value, rhs: Value) -> Result<bool, ()> {
    stacker::maybe_grow(32 * 1024, 1024, || {
        unify_inner(db, typed, level, lhs, rhs)
    })
}

fn unify_inner(db: &mut Database, typed: bool, level: Level, lhs: Value, rhs: Value) -> Result<bool, ()> {
    let (lhst, rhst) = (lhs.clone(), rhs.clone());
    // eprintln!("UNIFY:");
    // eprintln!("  {}", quote(db, lhst, level));
    // eprintln!("  {}", quote(db, rhst, level));
    let result : bool = match (lhs.head(), rhs.head()) {
        (Head::MetaVariable { module:m1, name:n1, .. },
            Head::MetaVariable { module:m2, name:n2, .. }) =>
        {
            let (s1, s2) = (lhs.spine(), rhs.spine());
            let folded = n1 == n2 && unify_spine(db, typed, level, lhs.clone(), rhs.clone())?;
            let unfolded = || {
                match (db.lookup_meta(m1, n1), db.lookup_meta(m2, n2)) {
                    (MetaState::Solved(lhs), MetaState::Solved(rhs)) => unify(db, typed, level, lhs, rhs),
                    (MetaState::Solved(lhs), MetaState::Unsolved) => unify(db, typed, level, lhs, rhs),
                    (MetaState::Unsolved, MetaState::Solved(rhs)) => unify(db, typed, level, lhs, rhs),
                    _ => Ok(false)
                }
            };
            folded || unfolded()?
        }
        (Head::MetaVariable { name, module, .. }, _) => {
            let spine = lhs.spine();
            match db.lookup_meta(module, name) {
                MetaState::Unsolved => {
                    if typed { solve(db, module, level, name, spine.clone(), rhs)? }
                    typed
                }
                MetaState::Frozen => false,
                MetaState::Solved(lhs) => {
                    let lhs = lhs.perform_spine(db, spine);
                    unify(db, typed, level, lhs, rhs)?
                }
            }
        }
        (_, Head::MetaVariable { name, module, .. }) => {
            let spine = rhs.spine();
            match db.lookup_meta(module, name) {
                MetaState::Unsolved => {
                    if typed { solve(db, module, level, name, spine.clone(), lhs)? }
                    typed
                }
                MetaState::Frozen => false,
                MetaState::Solved(rhs) => {
                    let rhs = rhs.perform_spine(db, spine);
                    unify(db, typed, level, lhs, rhs)?
                }
            }
        }
        (Head::Reference { id:i1, unfolded:u1, .. },
            Head::Reference { id:i2, unfolded:u2, .. }) =>
        {
            let (p1, p2) = (lhs.spine(), rhs.spine());
            let folded_check = i1 == i2 && unify_spine(db, typed, level, lhs, rhs)?;
            let check_unfolded = || {
                let mut result = Ok(false);
                if let Some(u1) = u1 {
                    if let Some(u2) = u2 {
                        let u1 = u1.perform_spine(db, p1);
                        let u2 = u2.perform_spine(db, p2);
                        result = unify(db, typed, level, u1, u2);
                    }
                }
                result
            };
            folded_check || check_unfolded()?
        }
        (Head::Reference { unfolded, .. }, _) => {
            let spine = lhs.spine();
            unfolded.as_ref()
                .map_or(Ok(false), |u| {
                    let u = u.clone().perform_spine(db, spine);
                    unify(db, typed, level, u, rhs)
                })?
        }
        (_, Head::Reference { unfolded, .. }) => {
            let spine = rhs.spine();
            unfolded.as_ref()
                .map_or(Ok(false), |u| {
                    let u = u.clone().perform_spine(db, spine);
                    unify(db, typed, level, lhs, u)
                })?
        }
        (Head::Star, Head::Star) => rhs.spine().is_empty() && lhs.spine().is_empty(),
        (Head::SuperStar, Head::SuperStar) => rhs.spine().is_empty() && lhs.spine().is_empty(),
        (Head::Pi { sort:s1, mode:m1, name:n1, domain:d1, closure:c1 }
        , Head::Pi { sort:s2, mode:m2, name:n2, domain:d2, closure:c2 })
        => {
            let input = LazyValueData::var(db, s1, level);
            let c1 = c1.eval(db, EnvEntry::new(n1, m1, input.clone()));
            let c2 = c2.eval(db, EnvEntry::new(n2, m2, input));
            m1 == m2
            && unify(db, typed, level, d1, d2)?
            && unify(db, typed, level + 1, c1, c2)?
            && rhs.spine().is_empty()
            && lhs.spine().is_empty()
        }
        (Head::Intersect { name:n1, first:f1, second:s1 }
        , Head::Intersect { name:n2, first:f2, second:s2 })
        => {
            let input = LazyValueData::var(db, Sort::Term, level);
            let s1 = s1.eval(db, EnvEntry::new(n1, Mode::Free, input.clone()));
            let s2 = s2.eval(db, EnvEntry::new(n2, Mode::Free, input));
            unify(db, typed, level, f1, f2)?
            && unify(db, typed, level + 1, s1, s2)?
            && rhs.spine().is_empty()
            && lhs.spine().is_empty()
        }
        (Head::Equality { left:l1, right:r1, anno:a1 }
        , Head::Equality { left:l2, right:r2, anno:a2 })
        => {
            let (l1, l2) = (l1.force(db), l2.force(db));
            let (r1, r2) = (r1.force(db), r2.force(db));
            unify(db, typed, level, l1, l2)?
            && unify(db, typed, level, r1 ,r2)?
            && unify(db, typed, level, a1, a2)?
            && rhs.spine().is_empty()
            && lhs.spine().is_empty()
        }
        (Head::Lambda { sort:s1, mode:m1, name:n1, domain:d1, closure:c1 }
        , Head::Lambda { sort:s2, mode:m2, name:n2, domain:d2, closure:c2, .. })
        if m1 == Mode::TypeLevel && m2 == Mode::TypeLevel
        => {
            let input = LazyValueData::var(db, s1, level);
            let c1 = c1.eval(db, EnvEntry::new(n1, m1, input.clone()));
            let c2 = c2.eval(db, EnvEntry::new(n2, m2, input));
            unify(db, typed, level, d1, d2)?
            && unify(db, typed, level + 1, c1, c2)?
            && unify_spine(db, typed, level, lhs, rhs)?
        }
        (Head::Lambda { sort:s1, mode:m1, name:n1, domain:d1, closure:c1 }
        , Head::Lambda { sort:s2, mode:m2, name:n2, domain:d2, closure:c2, .. })
        if (m1 == Mode::Free && m2 == Mode::Free) || (m1 == Mode::Erased && m2 == Mode::Erased)
        => {
            let input = LazyValueData::var(db, s1, level);
            let c1 = c1.eval(db, EnvEntry::new(n1, m1, input.clone()));
            let c2 = c2.eval(db, EnvEntry::new(n2, m2, input));
            unify(db, typed, level, d1, d2).ok();
            unify(db, typed, level + 1, c1, c2)?
            && unify_spine(db, typed, level, lhs, rhs)?
        }
        (Head::Lambda { mode:Mode::Free, .. }, _) if !lhs.spine().is_empty() => {
            let spine = erase_spine(lhs.spine())?;
            let head: Value = lhs.head().into();
            let lhs = head.perform_spine(db, spine);
            unify(db, false, level, lhs, rhs)?
        }
        (_, Head::Lambda { mode:Mode::Free, .. }) if !rhs.spine().is_empty() => {
            let spine = erase_spine(rhs.spine())?;
            let head: Value = lhs.head().into();
            let rhs = head.perform_spine(db, spine);
            unify(db, false, level, lhs, rhs)?
        }
        (Head::Lambda { mode, name, closure, .. }, _) if mode == Mode::Erased => {
            let input = LazyValueData::var(db, Sort::Term, level);
            let body = closure
                .eval(db, EnvEntry::new(name, mode, input.clone()))
                .perform_spine(db, lhs.spine());
            unify(db, false, level + 1, body, rhs)?
        }
        (_, Head::Lambda { mode, name, closure, .. }) if mode == Mode::Erased => {
            let input = LazyValueData::var(db, Sort::Term, level);
            let body = closure
                .eval(db, EnvEntry::new(name, mode, input.clone()))
                .perform_spine(db, rhs.spine());
            unify(db, false, level + 1, lhs, body)?
        }
        (Head::Pair { first:f1, second:s1, anno:a1 }
        , Head::Pair { first:f2, second:s2, anno:a2 })
        => {
            unify(db, typed, level, s1, s2).ok();
            unify(db, typed, level, a1, a2).ok();
            unify(db, typed, level, f1, f2)?
            && unify_spine(db, typed, level, lhs, rhs)?
        }
        (Head::Pair { first, .. }, _) => {
            let first = first.perform_spine(db, lhs.spine());
            unify(db, false, level, first, rhs)?
        }
        (_, Head::Pair { first, .. }) => {
            let first = first.perform_spine(db, rhs.spine());
            unify(db, false, level, lhs, first)?
        }
        (Head::Refl { input:i1 }, Head::Refl { input:i2 }) => {
            let i1 = i1.force(db);
            let i2 = i2.force(db);
            unify(db, typed, level, i1, i2).ok();
            unify_spine(db, typed, level, lhs, rhs)?
        }
        (Head::Refl { .. }, _) => {
            let lhs =
                Value::id(db, Sort::Term, Mode::Free, Head::SuperStar.into())
                .perform_spine(db, lhs.spine());
            unify(db, false, level, lhs, rhs)?
        }
        (_, Head::Refl { .. }) => {
            let rhs = 
                Value::id(db, Sort::Term, Mode::Free, Head::SuperStar.into())
                .perform_spine(db, rhs.spine());
            unify(db, false, level, lhs, rhs)?
        }
        (Head::Cast { input, .. }, _) => {
            let spine = lhs.spine();
            let input = input.perform_spine(db, spine);
            unify(db, false, level, input, rhs)?
        }
        (_, Head::Cast { input, .. }) => {
            let spine = rhs.spine();
            let input = input.perform_spine(db, spine);
            unify(db, false, level, lhs, input)?
        }
        (Head::Variable { level:l1, erasure:e1, .. }
        , Head::Variable { level:l2, erasure:e2, .. })
        => {
            let (p1, p2) = (lhs.spine(), rhs.spine());
            if l1 == l2 {
                unify_spine(db, typed, level, lhs, rhs)?
            } else {
                match (e1, e2) {
                    (Some(e1), Some(e2)) => {
                        let e1 = e1.force(db).perform_spine(db, p1);
                        let e2 = e2.force(db).perform_spine(db, p2);
                        unify(db, false, level, e1, e2)?
                    }
                    (Some(e1), None) => {
                        let e1 = e1.force(db).perform_spine(db, p1);
                        unify(db, false, level, e1, rhs)?
                    }
                    (None, Some(e2)) => {
                        let e2 = e2.force(db).perform_spine(db, p2);
                        unify(db, false, level, lhs, e2)?
                    }
                    (None, None) => false
                }
            }
        }
        (Head::Variable { level, erasure, .. }, _) => {
            let spine = lhs.spine();
            let Some(erasure) = erasure else { return Ok(false) };
            let erasure = erasure.force(db).perform_spine(db, spine);
            unify(db, false, level, erasure, rhs)?
        }
        (_, Head::Variable { level, erasure, .. }) => {
            let spine = rhs.spine();
            let Some(erasure) = erasure else { return Ok(false) };
            let erasure = erasure.force(db).perform_spine(db, spine);
            unify(db, false, level, lhs, erasure)?
        }
        _ => false
    };
    Ok(result)
}


