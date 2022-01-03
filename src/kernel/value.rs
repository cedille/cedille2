
use std::rc::Rc;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use threadstack::*;

use crate::common::*;
use crate::lang::elaborator::References;
use crate::kernel::core::Term;

declare_thread_stacks!(
    VALUE_MEMORY: RefCell<Vec<Rc<Value>>> = RefCell::new(Vec::with_capacity(1024));
    STAR_HANDLE: Cell<Option<Handle>> = Cell::new(None);
    SUPERSTAR_HANDLE: Cell<Option<Handle>> = Cell::new(None);
    VAR_HANDLES: RefCell<HashMap<Level, Handle>> = RefCell::new(HashMap::with_capacity(16));
);

#[derive(Debug, Clone, Copy)]
pub struct Handle(usize);

impl Handle {
    pub fn deref(&self) -> Rc<Value> {
        let_ref_thread_stack_value!(slab, VALUE_MEMORY);
        let slab = slab.borrow();
        let ptr = slab.get(self.0).unwrap();
        ptr.clone()
    }
}

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
pub struct LazyValue {
    value: Cell<Option<Handle>>,
    closure: RefCell<Option<Closure>>
}

impl LazyValue {
    pub fn new(env: ConsVec<EnvEntry>, code: Rc<Term>) -> LazyValue {
        LazyValue { 
            value: Cell::new(None),
            closure: RefCell::new(Some(Closure { env, code }))
        }
    }

    pub fn computed(value: Handle) -> LazyValue {
        LazyValue {
            value: Cell::new(Some(value)),
            closure: RefCell::new(None)
        }
    }

    pub fn force(&self, refs: References) -> Handle {
        if let Some(value) = self.value.get() { value }
        else {
            let mut closure = self.closure.borrow_mut();
            match closure.as_ref() {
                Some(Closure { env, code }) => {
                    let result = Value::eval(refs, env.clone(), code.clone());
                    self.value.replace(Some(result));
                    *closure = None;
                    result
                },
                None => unreachable!()
            }
        }
    }

    fn is_forced(&self) -> bool {
        self.value.get().is_some()
    }

    fn apply(&self, refs: References, arg: EnvEntry) -> LazyValue {
        match self.value.get() {
            Some(value) => {
                LazyValue::computed(value.deref().apply(refs, arg))
            }
            None => self.clone()
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
    fn alloc(self) -> Handle {
        let_ref_thread_stack_value!(slab, VALUE_MEMORY);
        let mut slab = slab.borrow_mut();
        slab.push(Rc::new(self));
        Handle(slab.len() - 1)
    }

    pub fn collect() {
        let_ref_thread_stack_value!(slab, VALUE_MEMORY);
        let_ref_thread_stack_value!(superstar_handle, SUPERSTAR_HANDLE);
        let_ref_thread_stack_value!(star_handle, STAR_HANDLE);
        let_ref_thread_stack_value!(var_handles, VAR_HANDLES);
        slab.borrow_mut().clear();
        superstar_handle.take();
        star_handle.take();
        var_handles.borrow_mut().clear();
    }

    fn apply(&self, refs: References, arg: EnvEntry) -> Handle {
        match self {
            Value::Variable { level, spine } => {
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::Variable { level:*level, spine }.alloc()
            },
            Value::Reference { id, spine, unfolded } => {
                let unfolded = unfolded.as_ref().map(|v| v.apply(refs, arg.clone()));
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::Reference { id:id.clone(), spine, unfolded }.alloc()
            },
            Value::Lambda { closure, .. } => closure.apply(refs, arg),
            _ => unreachable!()
        }
    }

    fn apply_spine(value: Handle, refs: References, spine: ConsVec<EnvEntry>) -> Handle {
        spine.iter().fold(value, |acc, entry| acc.deref().apply(refs, entry.clone()))
    }

    pub fn equality(left: Handle, right: Handle) -> Handle {
        Value::Equality { left, right }.alloc()
    }

    pub fn superstar() -> Handle {
        let_ref_thread_stack_value!(handle, SUPERSTAR_HANDLE);
        match handle.get() {
            Some(h) => h,
            None => {
                let result = Value::SuperStar.alloc();
                handle.replace(Some(result));
                result
            }
        }
    }

    pub fn star() -> Handle {
        let_ref_thread_stack_value!(handle, STAR_HANDLE);
        match handle.get() {
            Some(h) => h,
            None => {
                let result = Value::Star.alloc();
                handle.replace(Some(result));
                result
            }
        }
    }

    pub fn var(level: Level) -> Handle {
        let_ref_thread_stack_value!(handle, VAR_HANDLES);
        let mut handle = handle.borrow_mut();
        *handle.entry(level).or_insert_with(|| Value::Variable { level, spine: ConsVec::new() }.alloc())
    }

    pub fn classifier(sort: Sort) -> Handle {
        match sort {
            Sort::Term => unreachable!(),
            Sort::Type => Value::star(),
            Sort::Kind => Value::superstar(),
        }
    }

    pub fn eval(refs: References, mut env: ConsVec<EnvEntry>, term: Rc<Term>) -> Handle {
        match term.as_ref() {
            Term::Lambda { mode, name, body } => {
                let (mode, name) = (*mode, *name);
                let closure = Closure { env, code:body.clone() };
                Value::Lambda { mode, name, closure }.alloc()
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
                Value::Pi { mode, name, domain:domain.force(refs), closure }.alloc()
            },
            Term::IntersectType { name, first, second } => {
                let first = LazyValue::new(env.clone(), first.clone());
                let second = Closure { env, code:second.clone() };
                Value::IntersectType { name:*name, first:first.force(refs), second }.alloc()
            },
            Term::Equality { left, right } => {
                let left = Value::eval(refs, env.clone(), left.clone());
                let right = Value::eval(refs, env, right.clone());
                Value::Equality { left, right }.alloc()
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
                match Value::eval(refs, env.clone(), fun.clone()).deref().as_ref() {
                    Value::Variable { level, spine } => {
                        let mut spine = spine.clone();
                        spine.push_back(entry);
                        Value::Variable { level:*level, spine }.alloc()
                    }
                    Value::Reference { id, spine, unfolded } => {
                        let unfolded = unfolded.as_ref().map(|v| v.apply(refs, entry.clone()));
                        let mut spine = spine.clone();
                        spine.push_back(entry);
                        Value::Reference { id:id.clone(), spine, unfolded }.alloc()
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
                Value::Reference { id:id.clone(), spine:ConsVec::new(), unfolded }.alloc()
            }
            Term::Star => Value::star(),
            Term::SuperStar => Value::superstar()
        }
    }

    pub fn unfold_to_head(refs: References, value: Handle) -> Handle {
        match value.deref().as_ref() {
            Value::Reference { spine, unfolded, .. } => {
                if let Some(unfolded) = unfolded {
                    let result = if unfolded.is_forced() { unfolded.force(refs) }
                        else { Value::apply_spine(unfolded.force(refs), refs, spine.clone()) };
                    Value::unfold_to_head(refs, result)
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
                acc && Value::convertible(refs, env, left, right)
            } else { acc && l.mode == r.mode }
        })
    }

    pub fn convertible(refs: References, env: Level, left: Handle, right: Handle) -> bool {
        match (left.deref().as_ref(), right.deref().as_ref()) {
            // Type head conversion
            (Value::Star, Value::Star) => true,
            (Value::SuperStar, Value::SuperStar) => true,
            (Value::Pi { mode:m1, name:n1, domain:d1, closure:c1 },
                Value::Pi { mode:m2, name:n2, domain:d2, closure:c2 }) =>
            {
                let (mode, input) = (Mode::Free, LazyValue::computed(Value::var(env)));
                let c1 = c1.apply(refs, EnvEntry::new(mode, *n1, input.clone()));
                let c2 = c2.apply(refs, EnvEntry::new(mode, *n2, input));
                *m1 == *m2
                && Value::convertible(refs, env, *d1, *d2)
                && Value::convertible(refs, env + 1, c1, c2)
            }
            (Value::IntersectType { name:n1, first:f1, second:s1 },
                Value::IntersectType { name:n2, first:f2, second:s2 }) =>
            {
                let (mode, input) = (Mode::Free, LazyValue::computed(Value::var(env)));
                let s1 = s1.apply(refs, EnvEntry::new(mode, *n1, input.clone()));
                let s2 = s2.apply(refs, EnvEntry::new(mode, *n2, input));
                Value::convertible(refs, env, *f1, *f2)
                && Value::convertible(refs, env + 1, s1, s2)
            }
            (Value::Equality { left:l1, right:r1 },
                Value::Equality { left:l2, right:r2 }) =>
            {
                Value::convertible(refs, env, *l1, *l2)
                && Value::convertible(refs, env, *r1, *r2)
            }
            // Lambda conversion + eta conversion
            (Value::Lambda { mode:m1, name:n1, closure:c1 },
                Value::Lambda { mode:m2, name:n2, closure:c2 }) => {
                let input= LazyValue::computed(Value::var(env));
                let c1 = c1.apply(refs, EnvEntry::new(*m1, *n1, input.clone()));
                let c2 = c2.apply(refs, EnvEntry::new(*m2, *n2, input));
                Value::convertible(refs, env + 1, c1, c2)
            }
            (Value::Lambda { mode, name, closure }, v) => {
                let input= LazyValue::computed(Value::var(env));
                let closure = closure.apply(refs, EnvEntry::new(*mode, *name, input.clone()));
                let v = v.apply(refs, EnvEntry::new(*mode, *name, input));
                Value::convertible(refs, env + 1, closure, v)
            }
            (v, Value::Lambda { mode, name, closure }) => {
                let input = LazyValue::computed(Value::var(env));
                let closure = closure.apply(refs, EnvEntry::new(*mode, *name, input.clone()));
                let v = v.apply(refs, EnvEntry::new(*mode, *name, input));
                Value::convertible(refs, env + 1, v, closure)
            }
            // Spines
            (Value::Variable { level:l1, spine:s1},
                Value::Variable { level:l2, spine:s2 }) =>
            {
                l1 == l2 && Value::convertible_spine(refs, env, s1.clone(), s2.clone())
            }
            (Value::Reference { id:id1, spine:s1, .. },
                Value::Reference { id:id2, spine:s2, .. }) =>
            {
                id1 == id2 && Value::convertible_spine(refs, env, s1.clone(), s2.clone())
            }

            _ => false
        }
    }

    fn quote_spine(refs: References, level: Level, head: Term, mut spine: ConsVec<EnvEntry>) -> Term {
        if spine.is_empty() { head }
        else {
            spine.iter_mut().fold(head, |acc, arg| {
                let (mode, fun) = (arg.mode, Rc::new(acc));
                let arg = Rc::new(arg.value.force(refs).deref().quote(refs, level));
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
                let input = EnvEntry::new(mode, name, LazyValue::computed(Value::var(level)));
                let body = Rc::new(closure.apply(refs, input).deref().quote(refs, level + 1));
                Term::Lambda { mode, name, body }
            }
            Value::Pi { mode, name, domain, closure } => {
                let (mode, name) = (*mode, *name);
                let input = EnvEntry::new(mode, name, LazyValue::computed(Value::var(level)));
                let domain = Rc::new(domain.deref().quote(refs, level));
                let body = Rc::new(closure.apply(refs, input).deref().quote(refs, level + 1));
                Term::Pi { mode, name, domain, body }
            },
            Value::IntersectType { name, first, second } => {
                let input = EnvEntry::new(Mode::Free, *name, LazyValue::computed(Value::var(level)));
                let first = Rc::new(first.deref().quote(refs, level));
                let second = Rc::new(second.apply(refs, input).deref().quote(refs, level + 1));
                Term::IntersectType { name:*name, first, second }
            },
            Value::Equality { left, right } => {
                let left = Rc::new(left.deref().quote(refs, level));
                let right = Rc::new(right.deref().quote(refs, level));
                Term::Equality { left, right }
            }
            Value::Star => Term::Star,
            Value::SuperStar => Term::SuperStar,
        }
    }
}