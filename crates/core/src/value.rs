
use std::rc::Rc;
use std::borrow::Borrow;
use std::cell::OnceCell;

use imbl::Vector;

use crate::hc::*;
use crate::utility::*;
use crate::term::*;
use crate::database::Database;

pub type Spine = Vector<Action>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EqInductData {
    pub domain: LazyValue,
    pub predicate: LazyValue,
    pub lhs: LazyValue,
    pub rhs: LazyValue,
    pub case: LazyValue
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Action {
    Apply(Mode, LazyValue),
    Project(usize),
    EqInduct(Rc<EqInductData>),
    Promote,
    Separate
}

pub type Env = Vector<EnvEntry>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EnvEntry {
    pub name: Symbol,
    pub mode: Mode,
    pub value: LazyValue,
}

impl EnvEntry {
    pub fn new(name: Symbol, mode: Mode, value: LazyValue) -> EnvEntry {
        EnvEntry { name, mode, value }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EnvBound {
    Defined,
    Bound
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Closure {
    pub env: Env,
    pub code: Term,
    pub pending_erase: bool
}

impl Closure {
    pub fn new(env: Env, code: Term) -> Closure {
        Closure { env, code, pending_erase: false }
    }

    pub fn erase(self) -> Closure {
        let Closure { env, code, .. } = self;
        let pending_erase = true;
        Closure { env, code, pending_erase }
    }
}

pub type LazyValue = Hc<LazyValueData>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LazyValueData {
    pub(crate) value: OnceCell<Value>,
    pub(crate) object: OnceCell<Value>,
    pub env: Env,
    pub code: Term
}

impl LazyValueData {
    pub fn lazy(db: &mut Database, env: Env, code: Term) -> LazyValue {
        db.make_value(LazyValueData {
            value: OnceCell::new(),
            object: OnceCell::new(),
            env,
            code
        })
    }

    pub fn var(db: &mut Database, sort: Sort, level: Level) -> LazyValue {
        let spine = Vector::new();
        let var = ValueData::Variable { sort, level, spine }.rced();
        let value = OnceCell::from(var.clone());
        let object = OnceCell::from(var);
        let module = Symbol::from("gen/lazy_value");
        let env = Vector::new();
        let name = format!("gen/{}/{}", sort, *level);
        let id = Id::new(module, Symbol::from(name.as_str()));
        let code = db.make_term(TermData::Free { sort, id });
        db.make_value(LazyValueData { value, object, env, code })
    }

    pub fn sort(&self) -> Sort {
        self.code.sort()
    }

    // pub fn get(&self) -> Option<Value> {
    //     self.value.get().cloned()
    // }

    pub(crate) fn set(&self, value: Value) -> Result<(), Value> {
        self.value.set(value)
    }
}

impl std::hash::Hash for LazyValueData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.env.hash(state);
        self.code.hash(state);
    }
}

pub type Value = Rc<ValueData>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueData {
    Variable {
        sort: Sort,
        level: Level,
        spine: Spine
    },
    MetaVariable {
        sort: Sort,
        name: Symbol,
        module: Symbol,
        spine: Spine
    },
    Reference {
        sort: Sort,
        id: Id,
        spine: Spine,
        unfolded: Option<LazyValue>
    },
    Pair {
        first: Value,
        second: Value,
        anno: Value
    },
    Refl {
        input: LazyValue
    },
    Cast {
        input: Value,
        witness: Value,
        evidence: Value,
        spine: Spine
    },
    Lambda {
        sort: Sort,
        mode: Mode,
        name: Symbol,
        domain: Value,
        closure: Closure
    },
    Pi {
        sort: Sort,
        mode: Mode,
        name: Symbol,
        domain: Value,
        closure: Closure
    },
    Intersect {
        name: Symbol,
        first: Value,
        second: Closure
    },
    Equality {
        left: LazyValue,
        right: LazyValue,
        anno: Value
    },
    Star,
    SuperStar,
}

pub trait ValueOps {
    fn var(sort: Sort, level: impl Into<Level>) -> Self;
    fn id(db: &mut Database, sort: Sort, mode: Mode) -> Self;
    fn sort(&self) -> Sort;
    fn push_action(&self, action: Action) -> Self;
    fn get_spine(&self) -> Spine;
    fn set_spine(&self, spine: Spine) -> Value;
    fn peel_proj(&self) -> Option<Self>
        where Self : Sized;
}

impl ValueOps for Value {
    fn var(sort: Sort, level: impl Into<Level>) -> Value {
        ValueData::Variable { sort, level: level.into(), spine: Vector::new() }.rced()
    }

    fn id(db: &mut Database, sort: Sort, mode: Mode) -> Value {
        let name = Symbol::from("x");
        let domain = ValueData::SuperStar.rced();
        let env = Vector::new();
        let code = db.make_term(TermData::Bound { sort, index: 0.into() });
        let pending_erase = false;
        let closure = Closure { env, code, pending_erase };
        ValueData::Lambda { sort, mode, name, domain, closure }.rced()
    }

    fn sort(&self) -> Sort {
        match self.as_ref() {
            ValueData::Variable { sort, .. }
            | ValueData::MetaVariable { sort, .. }
            | ValueData::Reference { sort, .. }
            | ValueData::Lambda { sort, .. }
            | ValueData::Pi { sort, .. } => *sort,
            ValueData::Refl { .. }
            | ValueData::Pair { .. }
            | ValueData::Cast { .. } => Sort::Term,
            ValueData::Intersect { .. }
            | ValueData::Equality { .. } => Sort::Type,
            ValueData::Star => Sort::Kind,
            ValueData::SuperStar => Sort::Unknown,
        }
    }

    fn push_action(&self, action: Action) -> Value {
        let mut spine = self.get_spine();
        spine.push_back(action);
        self.set_spine(spine)
    }

    fn get_spine(&self) -> Spine {
        match self.as_ref() {
            ValueData::Variable { spine, .. } => spine.clone(),
            ValueData::MetaVariable { spine, .. } => spine.clone(),
            ValueData::Reference { spine, .. } => spine.clone(),
            ValueData::Cast { spine, .. } => spine.clone(),
            _ => Vector::new()
        }
    }

    fn set_spine(&self, spine: Spine) -> Value {
        let borrow: &ValueData = self.borrow();
        match borrow.clone() {
            ValueData::Variable { sort, level, .. } => {
                ValueData::Variable { sort, level, spine }.rced()
            }
            ValueData::MetaVariable { sort, name, module, .. } => {
                ValueData::MetaVariable { sort, name, module, spine }.rced()
            }
            ValueData::Reference { sort, id, unfolded, .. } => {
                ValueData::Reference { sort, id, spine, unfolded }.rced()
            }
            ValueData::Cast { input, witness, evidence, .. } => {
                ValueData::Cast { input, witness, evidence, spine }.rced()
            }
            v => v.rced()
        }
    }

    fn peel_proj(&self) -> Option<Value> {
        let spine = self.get_spine();
        if let Some(first) = spine.last() {
            match first {
                Action::Project(_) => {
                    let mut spine = spine.clone();
                    spine.pop_back();
                    Some(self.set_spine(spine))
                }
                _ => None
            }
        } else { None }
    }
}

pub fn classifier(sort: Sort) -> Result<Value, ()> {
    match sort {
        Sort::Unknown => Err(()),
        Sort::Term => Err(()),
        Sort::Type => Ok(ValueData::Star.rced()),
        Sort::Kind => Ok(ValueData::SuperStar.rced()),
    }
}
