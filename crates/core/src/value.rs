
use std::fmt;
use std::rc::Rc;
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
            Action::Subst(t) => write!(f, "𝜓{{{}}}", t.head()),
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
}

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.code.fmt(f)
    }
}

impl Closure {
    pub fn new(env: Env, code: Term) -> Closure {
        Closure { env, code }
    }

    pub fn erase(self) -> Closure {
        let Closure { env, code, .. } = self;
        Closure { env, code }
    }
}

pub type LazyValue = Hc<LazyValueData>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LazyValueData {
    pub(crate) value: OnceCell<Value>,
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
            env,
            code
        })
    }

    pub fn var(db: &Database, sort: Sort, level: Level) -> LazyValue {
        LazyValueData::var_with_erasure(db, sort, level, None)
    }

    pub fn var_with_erasure(db: &Database, sort: Sort, level: Level, erasure: Option<LazyValue>) -> LazyValue {
        let spine = Vector::new();
        let var = Head::Variable { sort, level, erasure };
        let value = OnceCell::from((var, spine).rced());
        let module = Symbol::from("gen/lazy_value");
        let env = Vector::new();
        let name = format!("gen/{}/{}", sort, *level);
        let id = Id::new(module, Symbol::from(name.as_str()));
        let code = db.make_term(TermData::Free { sort, id });
        db.make_value(LazyValueData { value, env, code })
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
        self.env.hash(state);
        self.code.hash(state);
    }
}

pub type Value = Rc<(Head, Spine)>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Head {
    Variable {
        sort: Sort,
        level: Level,
        erasure: Option<LazyValue>
    },
    MetaVariable {
        sort: Sort,
        name: Symbol,
        module: Symbol,
    },
    Reference {
        sort: Sort,
        id: Id,
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

impl fmt::Display for Head {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Head::Variable { sort, level, .. } => {
                level.fmt(f)?;
                Ok(())
            }
            Head::MetaVariable { sort, name, module } => todo!(),
            Head::Reference { sort, id, unfolded } => {
                id.fmt(f)?;
                Ok(())
            }
            Head::Pair { first, second, anno } => {
                write!(f, "[{}, {}; {}]", first.head(), second.head(), anno.head())
            }
            Head::Refl { input } => write!(f, "β({})", input),
            Head::Cast { input, witness, evidence } => {
                write!(f, "φ({}, {}, {})", input.head(), witness.head(), evidence.head())?;
                Ok(())
            }
            Head::Lambda { sort, mode, name, domain, closure } => {
                write!(f, "λ{} {}:{}. {}", mode, name, domain.head(), closure)
            }
            Head::Pi { sort, mode, name, domain, closure } => {
                write!(f, "({} : {}) -{}> {}", name, domain.head(), mode, closure)
            }
            Head::Intersect { name, first, second } => {
                write!(f, "({} : {}) ∩ {}", name, first.head(), second)
            }
            Head::Equality { left, right, anno } => {
                write!(f, "({} =[{}] {})", left, anno.head(), right)
            }
            Head::Star => write!(f, "Set"),
            Head::SuperStar => write!(f, "□"),
        }
    }
}

pub trait ValueOps {
    fn var(sort: Sort, level: impl Into<Level>) -> Self;
    fn id(db: &Database, sort: Sort, mode: Mode, domain: Value) -> Self;
    fn sort(&self) -> Sort;
    fn push_action(&self, action: Action) -> Self;
    fn head(&self) -> Head;
    fn spine(&self) -> Spine;
    fn set_spine(&self, spine: Spine) -> Value;
}

impl ValueOps for Value {
    fn head(&self) -> Head { self.0.clone() }
    fn spine(&self) -> Spine { self.1.clone() }

    fn var(sort: Sort, level: impl Into<Level>) -> Value {
        let head = Head::Variable { sort, level: level.into(), erasure: None };
        let spine = Spine::new();
        (head, spine).rced()
    }

    fn id(db: &Database, sort: Sort, mode: Mode, domain: Value) -> Value {
        let name = Symbol::from("x");
        let env = Vector::new();
        let code = db.make_term(TermData::Bound { sort, index: 0.into() });
        let closure = Closure { env, code };
        let head = Head::Lambda { sort, mode, name, domain, closure };
        let spine = Spine::new();
        (head, spine).rced()
    }

    fn sort(&self) -> Sort {
        match self.head() {
            Head::Variable { sort, .. }
            | Head::MetaVariable { sort, .. }
            | Head::Reference { sort, .. }
            | Head::Lambda { sort, .. }
            | Head::Pi { sort, .. } => sort,
            Head::Refl { .. }
            | Head::Pair { .. }
            | Head::Cast { .. } => Sort::Term,
            Head::Intersect { .. }
            | Head::Equality { .. } => Sort::Type,
            Head::Star => Sort::Kind,
            Head::SuperStar => Sort::Unknown,
        }
    }

    fn push_action(&self, action: Action) -> Value {
        let mut spine = self.spine();
        spine.push_back(action);
        self.set_spine(spine)
    }

    fn set_spine(&self, spine: Spine) -> Value {
        (self.head(), spine).rced()
    }
}

impl From<Head> for Value {
    fn from(head: Head) -> Self {
        let spine = Spine::new();
        (head, spine).rced()
    }
}

pub fn classifier(sort: Sort) -> Result<Value, ()> {
    let spine = Spine::new();
    match sort {
        Sort::Unknown => Err(()),
        Sort::Term => Err(()),
        Sort::Type => Ok((Head::Star, spine).rced()),
        Sort::Kind => Ok((Head::SuperStar, spine).rced()),
    }
}
