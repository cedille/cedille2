
use std::rc::Rc;
use std::cell::{Cell, RefCell};

use once_cell::unsync::OnceCell;

use crate::common::*;
use crate::lang::elaborator::References;
use crate::kernel::factory::Handle;
use crate::kernel::core::Term;

// Assuming GC is still needed:
/*
    Have a Slotmap of Rc<Value>'s
    Give out special handles that when dropped will attempt to drop the associated Rc<Value> if it is unique
    When an Value is successfully dropped, it will try to drop any children that are also uniquely referenced

    or..

    Don't use Rc but have a custom key that updates the number of times it was cloned
    and decrements when it is dropped

    or..

    Give out reference counted keys!
*/

#[derive(Debug, Clone)]
pub struct EnvEntry {
    mode: Mode,
    name: Symbol,
    value: LazyValue,
}

impl EnvEntry {
    pub fn new(mode: Mode, name: Symbol, value: LazyValue) -> EnvEntry {
        EnvEntry { mode, name, value }
    }
}

#[derive(Debug, Clone)]
pub struct Closure {
    env: ConsVec<EnvEntry>,
    code: Rc<Term>
}

impl Closure {
    pub fn apply(&self, refs: References, arg: EnvEntry) -> Handle {
        let Closure { env, code } = self;
        let mut env = env.clone();
        env.push_back(arg);
        Value::eval(refs, env, code.clone())
    }
}

#[derive(Debug, Clone)]
struct LazyValueCode {
    env: ConsVec<EnvEntry>,
    spine: ConsVec<EnvEntry>,
    code: Rc<Term>
}

#[derive(Debug, Clone)]
pub struct LazyValue {
    value: OnceCell<Handle>,
    code: RefCell<Option<LazyValueCode>>
}

impl LazyValue {
    pub fn new(env: ConsVec<EnvEntry>, code: Rc<Term>) -> LazyValue {
        let spine = ConsVec::new();
        LazyValue { 
            value: OnceCell::new(),
            code: RefCell::new(Some(LazyValueCode { env, spine, code }))
        }
    }

    pub fn computed(value: Handle) -> LazyValue {
        LazyValue {
            value: OnceCell::from(value),
            code: RefCell::new(None)
        }
    }

    pub fn force(&self, refs: References) -> Handle {
        if let Some(value) = self.value.get() { value.clone() }
        else {
            let mut code = self.code.borrow_mut();
            match code.as_ref() {
                Some(LazyValueCode { env, spine, code:term }) => {
                    let result = Value::eval(refs, env.clone(), term.clone());
                    let result = Value::apply_spine(result, refs, spine.clone());
                    self.value.set(result.clone());
                    *code = None;
                    result
                },
                None => unreachable!()
            }
        }
    }

    fn apply(&self, refs: References, arg: EnvEntry) -> LazyValue {
        if let Some(value) = self.value.get() { 
            LazyValue::computed(value.apply(refs, arg))
        } else {
            let mut code = self.code.borrow_mut();
            match code.as_mut() {
                Some(LazyValueCode { spine, .. }) => {
                    spine.push_back(arg);
                    self.clone()
                },
                None => unreachable!()
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Variable {
        level: Level,
        spine: ConsVec<EnvEntry>
    },
    Reference {
        id: Id,
        spine: ConsVec<EnvEntry>,
        unfolded: Option<LazyValue>
    },
    Lambda {
        mode: Mode,
        name: Symbol,
        closure: Closure
    },
    Pi {
        mode: Mode,
        name: Symbol,
        domain: Handle,
        closure: Closure
    },
    IntersectType {
        name: Symbol,
        first: Handle,
        second: Closure
    },
    Equality {
        left: Handle,
        right: Handle
    },
    Star,
    SuperStar,
}

impl Value {
    pub fn apply(&self, refs: References, arg: EnvEntry) -> Handle {
        match self {
            Value::Variable { level, spine } => {
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::variable_with_spine(*level, spine)
            },
            Value::Reference { id, spine, unfolded } => {
                let unfolded = unfolded.as_ref().map(|v| v.apply(refs, arg.clone()));
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::reference(id.clone(), spine, unfolded)
            },
            Value::Lambda { closure, .. } => closure.apply(refs, arg),
            _ => unreachable!()
        }
    }

    fn apply_spine(value: Handle, refs: References, spine: ConsVec<EnvEntry>) -> Handle {
        spine.iter().fold(value, |acc, entry| acc.apply(refs, entry.clone()))
    }

    pub fn classifier(sort: Sort) -> Handle {
        match sort {
            Sort::Term => unreachable!(),
            Sort::Type => Value::star(),
            Sort::Kind => Value::super_star(),
        }
    }

    pub fn eval(refs: References, mut env: ConsVec<EnvEntry>, term: Rc<Term>) -> Handle {
        match term.as_ref() {
            Term::Lambda { mode, name, body } => {
                let (mode, name) = (*mode, *name);
                let closure = Closure { env, code:body.clone() };
                Value::lambda(mode, name, closure)
            },
            Term::Let { mode, name, let_body, body } => {
                let def_value = LazyValue::new(env.clone(), let_body.clone());
                env.push_back(EnvEntry::new(*mode, *name, def_value));
                Value::eval(refs, env, body.clone())
            },
            Term::Pi { mode, name, domain, body } => {
                let (mode, name) = (*mode, *name);
                let domain = LazyValue::new(env.clone(), domain.clone());
                let closure = Closure { env, code:body.clone() };
                Value::pi(mode, name, domain.force(refs), closure)
            },
            Term::IntersectType { name, first, second } => {
                let first = LazyValue::new(env.clone(), first.clone());
                let second = Closure { env, code:second.clone() };
                Value::intersect_type(*name, first.force(refs), second)
            },
            Term::Equality { left, right } => {
                let left = Value::eval(refs, env.clone(), left.clone());
                let right = Value::eval(refs, env, right.clone());
                Value::equality(left, right)
            },
            Term::Rewrite { body, .. }
            | Term::Annotate { body, .. }
            | Term::Project { body, .. } => Value::eval(refs, env, body.clone()),
            Term::Intersect { first, .. } => Value::eval(refs, env, first.clone()),
            Term::Separate { .. } => Value::eval(refs, env, Rc::new(Term::id())),
            Term::Refl { erasure }
            | Term::Cast { erasure, .. } => Value::eval(refs, env, erasure.clone()),
            Term::Apply { mode, fun, arg } => {
                let (mode, name) = (*mode, Symbol::default());
                let arg = LazyValue::new(env.clone(), arg.clone());
                let entry = EnvEntry::new(mode, name, arg);
                let fun = Value::eval(refs, env.clone(), fun.clone());
                match &*Handle::upgrade(&fun) {
                    Value::Variable { level, spine } => {
                        let mut spine = spine.clone();
                        spine.push_back(entry);
                        Value::variable_with_spine(*level, spine)
                    }
                    Value::Reference { id, spine, unfolded } => {
                        let unfolded = unfolded.as_ref().map(|v| v.apply(refs, entry.clone()));
                        let mut spine = spine.clone();
                        spine.push_back(entry);
                        Value::reference(id.clone(), spine, unfolded)
                    } 
                    Value::Lambda { closure, .. } => closure.apply(refs, entry),
                    _ => unreachable!()
                }
            },
            Term::Bound { index, .. } => {
                env[env.len() - **index - 1].value.force(refs)
            }
            Term::Free { id, .. } => {
                let unfolded = refs.lookup_def(id).ok()
                    .map(LazyValue::computed);
                Value::reference(id.clone(), ConsVec::new(), unfolded)
            }
            Term::Star => Value::star(),
            Term::SuperStar => Value::super_star()
        }
    }

    pub fn unfold_to_head(refs: References, value: Handle) -> Handle {
        match &*Handle::upgrade(&value) {
            Value::Reference { unfolded, .. } => {
                if let Some(unfolded) = unfolded {
                    Value::unfold_to_head(refs, unfolded.force(refs))
                } else { value }
            },
            _ => value
        }
    }

    fn convertible_spine(refs: References, env: Level, mut left: ConsVec<EnvEntry>, mut right: ConsVec<EnvEntry>) -> bool {
        left.iter_mut()
        .zip(right.iter_mut())
        .fold(true, |acc, (l, r)| {
            if l.mode == r.mode && l.mode == Mode::Free {
                let left = l.value.force(refs);
                let right = r.value.force(refs);
                acc && Value::convertible(refs, env, &left, &right)
            } else { acc && l.mode == r.mode }
        })
    }

    pub fn convertible(refs: References, env: Level, left: &Handle, right: &Handle) -> bool {
        match dbg!(&*Handle::upgrade(left), &*Handle::upgrade(right)) {
            // Type head conversion
            (Value::Star, Value::Star) => true,
            (Value::SuperStar, Value::SuperStar) => true,
            (Value::Pi { mode:m1, name:n1, domain:d1, closure:c1 },
                Value::Pi { mode:m2, name:n2, domain:d2, closure:c2 }) =>
            {
                let (mode, input) = (Mode::Free, LazyValue::computed(Value::variable(env)));
                let c1 = c1.apply(refs, EnvEntry::new(mode, *n1, input.clone()));
                let c2 = c2.apply(refs, EnvEntry::new(mode, *n2, input));
                m1 == m2
                && Value::convertible(refs, env, &d1, &d2)
                && Value::convertible(refs, env + 1, &c1, &c2)
            }
            (Value::IntersectType { name:n1, first:f1, second:s1 },
                Value::IntersectType { name:n2, first:f2, second:s2 }) =>
            {
                let (mode, input) = (Mode::Free, LazyValue::computed(Value::variable(env)));
                let s1 = s1.apply(refs, EnvEntry::new(mode, *n1, input.clone()));
                let s2 = s2.apply(refs, EnvEntry::new(mode, *n2, input));
                Value::convertible(refs, env, &f1, &f2)
                && Value::convertible(refs, env + 1, &s1, &s2)
            }
            (Value::Equality { left:l1, right:r1 },
                Value::Equality { left:l2, right:r2 }) =>
            {
                Value::convertible(refs, env, &l1, &l2)
                && Value::convertible(refs, env, &r1, &r2)
            }
            // Lambda conversion + eta conversion
            (Value::Lambda { mode:m1, name:n1, closure:c1 },
                Value::Lambda { mode:m2, name:n2, closure:c2 }) => {
                let input= LazyValue::computed(Value::variable(env));
                let c1 = c1.apply(refs, EnvEntry::new(*m1, *n1, input.clone()));
                let c2 = c2.apply(refs, EnvEntry::new(*m2, *n2, input));
                Value::convertible(refs, env + 1, &c1, &c2)
            }
            (Value::Lambda { mode, name, closure }, v) => {
                let input= LazyValue::computed(Value::variable(env));
                let closure = closure.apply(refs, EnvEntry::new(*mode, *name, input.clone()));
                let v = v.apply(refs, EnvEntry::new(*mode, *name, input));
                Value::convertible(refs, env + 1, &closure, &v)
            }
            (v, Value::Lambda { mode, name, closure }) => {
                let input = LazyValue::computed(Value::variable(env));
                let closure = closure.apply(refs, EnvEntry::new(*mode, *name, input.clone()));
                let v = v.apply(refs, EnvEntry::new(*mode, *name, input));
                Value::convertible(refs, env + 1, &v, &closure)
            }
            // Spines
            (Value::Variable { level:l1, spine:s1},
                Value::Variable { level:l2, spine:s2 }) =>
            {
                l1 == l2 && Value::convertible_spine(refs, env, s1.clone(), s2.clone())
            }
            (Value::Reference { id:id1, spine:s1, unfolded:u1 },
                Value::Reference { id:id2, spine:s2, unfolded:u2 }) =>
            {
                let check_unfolded = || {
                    let mut result = false;
                    if let Some(u1) = u1 {
                        if let Some(u2) = u2 {
                            let (u1, u2) = (u1.force(refs), u2.force(refs));
                            result = Value::convertible(refs, env, &u1, &u2);
                        }
                    }
                    result
                };
                (id1 == id2 && Value::convertible_spine(refs, env, s1.clone(), s2.clone()))
                    || check_unfolded()
            },
            (Value::Reference { unfolded, .. }, _) => {
                unfolded.as_ref()
                    .map_or(false, |u| Value::convertible(refs, env, &u.force(refs), right))
            }
            (_, Value::Reference { unfolded, .. }) => {
                unfolded.as_ref()
                    .map_or(false, |u| Value::convertible(refs, env, left, &u.force(refs)))
            }

            _ => false
        }
    }

    fn quote_spine(refs: References, level: Level, head: Term, mut spine: ConsVec<EnvEntry>) -> Term {
        if spine.is_empty() { head }
        else {
            spine.iter_mut().fold(head, |acc, arg| {
                let (mode, fun) = (arg.mode, Rc::new(acc));
                let arg = Rc::new(Handle::upgrade(&arg.value.force(refs)).quote(refs, level));
                Term::Apply { mode, fun, arg }
            })
        }
    }

    pub fn quote(&self, refs: References, level: Level) -> Term {
        match self {
            Value::Variable { level:vlvl, spine } => {
                let var = Term::Bound { index: vlvl.to_index(level) };
                Value::quote_spine(refs, level, var, spine.clone())
            }
            Value::Reference { id, spine, .. } => {
                let var = Term::Free { id:id.clone() };
                Value::quote_spine(refs, level, var, spine.clone())
            }
            Value::Lambda { mode, name, closure } => {
                let (mode, name) = (*mode, *name);
                let input = EnvEntry::new(mode, name, LazyValue::computed(Value::variable(level)));
                let body = Rc::new(Handle::upgrade(&closure.apply(refs, input)).quote(refs, level + 1));
                Term::Lambda { mode, name, body }
            }
            Value::Pi { mode, name, domain, closure } => {
                let (mode, name) = (*mode, *name);
                let input = EnvEntry::new(mode, name, LazyValue::computed(Value::variable(level)));
                let domain = Rc::new(Handle::upgrade(&domain).quote(refs, level));
                let body = Rc::new(Handle::upgrade(&closure.apply(refs, input)).quote(refs, level + 1));
                Term::Pi { mode, name, domain, body }
            },
            Value::IntersectType { name, first, second } => {
                let input = EnvEntry::new(Mode::Free, *name, LazyValue::computed(Value::variable(level)));
                let first = Rc::new(Handle::upgrade(&first).quote(refs, level));
                let second = Rc::new(Handle::upgrade(&second.apply(refs, input)).quote(refs, level + 1));
                Term::IntersectType { name:*name, first, second }
            },
            Value::Equality { left, right } => {
                let left = Rc::new(Handle::upgrade(&left).quote(refs, level));
                let right = Rc::new(Handle::upgrade(&right).quote(refs, level));
                Term::Equality { left, right }
            }
            Value::Star => Term::Star,
            Value::SuperStar => Term::SuperStar,
        }
    }
}