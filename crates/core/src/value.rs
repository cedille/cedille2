
use std::fmt;
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
pub enum Action {
    Apply(Mode, LazyValue),
    Project(usize),
    Subst(Value),
    Promote(usize, LazyValue, LazyValue),
    Separate
}

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Action::Apply(m, v) => write!(f, "@{} {}", m, v),
            Action::Project(p) => write!(f, ".{}", p),
            Action::Subst(t) => write!(f, "𝜓{{{}}}", t),
            Action::Promote(p, a, b) => write!(f, "ϑ{{{},{},{}}}", p, a, b),
            Action::Separate => write!(f, "δ"),
        }
    }
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
    pub erased: bool
}

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.code.fmt(f)
    }
}

impl Closure {
    pub fn new(env: Env, code: Term) -> Closure {
        Closure { env, code, erased: false }
    }

    pub fn erase(self) -> Closure {
        let Closure { env, code, .. } = self;
        let erased = true;
        Closure { env, code, erased }
    }
}

pub type LazyValue = Hc<LazyValueData>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LazyValueData {
    pub(crate) value: OnceCell<Value>,
    pub(crate) object: OnceCell<Value>,
    pub erased: bool,
    pub env: Env,
    pub code: Term
}

impl fmt::Display for LazyValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.code.fmt(f)
    }
}

impl LazyValueData {
    pub fn lazy(db: &Database, env: Env, code: Term) -> LazyValue {
        db.make_value(LazyValueData {
            value: OnceCell::new(),
            object: OnceCell::new(),
            erased: false,
            env,
            code
        })
    }

    pub fn var(db: &Database, sort: Sort, level: Level) -> LazyValue {
        let erased = false;
        let spine = Vector::new();
        let var = ValueData::Variable { sort, level, spine }.rced();
        let value = OnceCell::from(var.clone());
        let object = OnceCell::from(var);
        let module = Symbol::from("gen/lazy_value");
        let env = Vector::new();
        let name = format!("gen/{}/{}", sort, *level);
        let id = Id::new(module, Symbol::from(name.as_str()));
        let code = db.make_term(TermData::Free { sort, id });
        db.make_value(LazyValueData { value, object, erased, env, code })
    }

    pub fn sort(&self) -> Sort {
        self.code.sort()
    }

    // pub fn get(&self) -> Option<Value> {
    //     self.value.get().cloned()
    // }

    // pub(crate) fn set(&self, value: Value) -> Result<(), Value> {
    //     self.value.set(value)
    // }
}

impl std::hash::Hash for LazyValueData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.erased.hash(state);
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
        unfolded: Option<Value>
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

impl fmt::Display for ValueData {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValueData::Variable { sort, level, spine } => {
                level.fmt(f)?;
                for action in spine.iter() { action.fmt(f)?; }
                Ok(())
            }
            ValueData::MetaVariable { sort, name, module, spine } => todo!(),
            ValueData::Reference { sort, id, spine, unfolded } => {
                id.fmt(f)?;
                for action in spine.iter() { action.fmt(f)?; }
                Ok(())
            }
            ValueData::Pair { first, second, anno } => {
                write!(f, "[{}, {}; {}]", first, second, anno)
            }
            ValueData::Refl { input } => write!(f, "β({})", input),
            ValueData::Cast { input, witness, evidence, spine } => {
                write!(f, "φ({}, {}, {})", input, witness, evidence)?;
                for action in spine.iter() { action.fmt(f)?; }
                Ok(())
            }
            ValueData::Lambda { sort, mode, name, domain, closure } => {
                write!(f, "λ{} {}:{}. {}", mode, name, domain, closure)
            }
            ValueData::Pi { sort, mode, name, domain, closure } => {
                write!(f, "({} : {}) -{}> {}", name, domain, mode, closure)
            }
            ValueData::Intersect { name, first, second } => {
                write!(f, "({} : {}) ∩ {}", name, first, second)
            }
            ValueData::Equality { left, right, anno } => {
                write!(f, "({} =[{}] {})", left, anno, right)
            }
            ValueData::Star => write!(f, "Set"),
            ValueData::SuperStar => write!(f, "□"),
        }
    }
}

pub trait ValueOps {
    fn var(sort: Sort, level: impl Into<Level>) -> Self;
    fn id(db: &Database, sort: Sort, mode: Mode, domain: Value) -> Self;
    fn sort(&self) -> Sort;
    fn push_action(&self, action: Action) -> Self;
    fn get_spine(&self) -> Spine;
    fn set_spine(&self, spine: Spine) -> Value;
}

impl ValueOps for Value {
    fn var(sort: Sort, level: impl Into<Level>) -> Value {
        ValueData::Variable { sort, level: level.into(), spine: Vector::new() }.rced()
    }

    fn id(db: &Database, sort: Sort, mode: Mode, domain: Value) -> Value {
        let name = Symbol::from("x");
        let env = Vector::new();
        let code = db.make_term(TermData::Bound { sort, index: 0.into() });
        let erased = false;
        let closure = Closure { env, code, erased };
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
}

pub fn classifier(sort: Sort) -> Result<Value, ()> {
    match sort {
        Sort::Unknown => Err(()),
        Sort::Term => Err(()),
        Sort::Type => Ok(ValueData::Star.rced()),
        Sort::Kind => Ok(ValueData::SuperStar.rced()),
    }
}
