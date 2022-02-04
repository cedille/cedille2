
use std::ops;
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;

use colored::Colorize;
use once_cell::unsync::OnceCell;

use crate::common::*;
use crate::kernel::core::Term;
use crate::database::Database;

#[derive(Debug, Clone)]
pub struct EnvEntry {
    name: Symbol,
    value: LazyValue,
}

impl fmt::Display for EnvEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}; {})", self.name, self.value)
    }
}

impl From<SpineEntry> for EnvEntry {
    fn from(entry: SpineEntry) -> Self {
        EnvEntry {
            name: Symbol::default(),
            value: entry.value
        }
    }
}

impl EnvEntry {
    pub fn new(name: Symbol, value: impl Into<LazyValue>) -> EnvEntry {
        EnvEntry { name, value: value.into() }
    }
}

#[derive(Debug, Clone)]
pub struct Environment(im_rc::Vector<EnvEntry>);

impl Environment {
    pub fn new() -> Environment {
        Environment(im_rc::Vector::new())
    }
}

impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = Ok(());
        result = result.and_then(|_| write!(f, "["));
        for i in 0..self.len() {
            result = result.and_then(|_| write!(f, "{}", self[i.into()]));
            if i + 1 != self.len() {
                result = result.and_then(|_| write!(f, ","));
            }
        }
        result.and_then(|_| write!(f, "]"))
    }
}

impl ops::Deref for Environment {
    type Target = im_rc::Vector<EnvEntry>;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl ops::DerefMut for Environment {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl ops::Index<Level> for Environment {
    type Output = EnvEntry;

    fn index(&self, index: Level) -> &Self::Output {
        &self.0[*index]
    }
}

#[derive(Debug, Clone)]
pub struct SpineEntry {
    pub apply_type: ApplyType,
    pub value: LazyValue,
}

impl fmt::Display for SpineEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let operator = match self.apply_type {
            ApplyType::Free => "∞",
            ApplyType::TermErased => "-",
            ApplyType::TypeErased => "·",
        };
        write!(f, "({}; {})", operator, self.value)
    }
}

impl SpineEntry {
    pub fn new(apply_type: ApplyType, value: LazyValue) -> SpineEntry {
        SpineEntry { apply_type, value }
    }
}

#[derive(Debug, Clone)]
pub struct Spine(im_rc::Vector<SpineEntry>);

impl Spine {
    pub fn new() -> Spine {
        Spine(im_rc::Vector::new())
    }
}

impl fmt::Display for Spine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = Ok(());
        result = result.and_then(|_| write!(f, "["));
        for i in 0..self.len() {
            result = result.and_then(|_| write!(f, "{}", self[i]));
            if i + 1 != self.len() {
                result = result.and_then(|_| write!(f, ","));
            }
        }
        result.and_then(|_| write!(f, "]"))
    }
}

impl ops::Deref for Spine {
    type Target = im_rc::Vector<SpineEntry>;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl ops::DerefMut for Spine {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl FromIterator<SpineEntry> for Spine {
    fn from_iter<T: IntoIterator<Item = SpineEntry>>(iter: T) -> Self {
        let inner = im_rc::Vector::from_iter(iter);
        Spine(inner)
    }
}

#[derive(Debug, Clone)]
pub struct Closure {
    module: Symbol,
    env: Environment,
    code: Rc<Term>
}

impl Closure {
    pub fn new(module: Symbol, env: Environment, code: Rc<Term>) -> Closure {
        Closure { module, env, code }
    }

    pub fn eval(&self, db: &Database, arg: impl Into<EnvEntry>) -> Rc<Value> {
        let Closure { module, env, code } = self;
        let mut env = env.clone();
        env.push_back(arg.into());
        Value::eval(db, *module, env, code.clone())
    }
}

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{};{}>", self.env, self.code)
    }
}

#[derive(Debug, Clone)]
struct LazyValueCode {
    module: Symbol,
    env: Environment,
    term: Rc<Term>
}

#[derive(Debug, Clone)]
pub struct LazyValue {
    value: OnceCell<Rc<Value>>,
    code: RefCell<Option<LazyValueCode>>
}

impl fmt::Display for LazyValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(value) = self.value.get() {
            write!(f, "{}", value)
        } else {
            let code = self.code.borrow();
            let code = code.as_ref().unwrap();
            write!(f, "<{};{}>", code.env, code.term)
        }
    }
}

impl From<&Rc<Value>> for LazyValue {
    fn from(value: &Rc<Value>) -> Self {
        Self::computed(value.clone())
    }
}

impl From<Rc<Value>> for LazyValue {
    fn from(value: Rc<Value>) -> Self {
        Self::computed(value)
    }
}

impl LazyValue {
    pub fn new(module: Symbol, env: Environment, term: Rc<Term>) -> LazyValue {
        LazyValue { 
            value: OnceCell::new(),
            code: RefCell::new(Some(LazyValueCode { module, env, term }))
        }
    }

    pub fn computed(value: Rc<Value>) -> LazyValue {
        LazyValue {
            value: OnceCell::from(value),
            code: RefCell::new(None)
        }
    }

    pub fn force(&self, db: &Database) -> Rc<Value> {
        match self.value.get() {
            Some(value) => value.clone(),
            None => {
                match self.code.take() {
                    Some(code) => {
                        let result = Value::eval(db, code.module, code.env, code.term);
                        self.value.set(result.clone()).ok();
                        result
                    },
                    None => unreachable!()
                }
            }
        }
    }

    pub fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<LazyValue> {
        let value = self.force(db).apply(db, arg);
        Rc::new(LazyValue::computed(value))
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Variable {
        level: Level,
        spine: Spine
    },
    Reference {
        id: Id,
        spine: Spine,
        unfolded: Option<Rc<LazyValue>>
    },
    Lambda {
        mode: Mode,
        name: Symbol,
        closure: Closure
    },
    Pi {
        mode: Mode,
        name: Symbol,
        domain: Rc<Value>,
        closure: Closure
    },
    IntersectType {
        name: Symbol,
        first: Rc<Value>,
        second: Closure
    },
    Equality {
        left: Rc<Value>,
        right: Rc<Value>
    },
    Star,
    SuperStar,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Variable { level, spine } => {
                if spine.len() == 0 { write!(f, "{}", level) }
                else { write!(f, "{} {}", level, spine) }
            },
            Value::Reference { id, spine, unfolded } => {
                if let Some(unfolded) = unfolded { write!(f, "{}", unfolded) }
                else if spine.len() == 0 { write!(f, "{}", id) }
                else { write!(f, "{} {}", id, spine) }
            },
            Value::Lambda { mode, name, closure } => {
                let mode = match mode {
                    Mode::Erased => "Λ",
                    Mode::Free => "λ",
                };
                write!(f, "{} {}. {}", mode, name, closure)
            },
            Value::Pi { mode, name, domain, closure } => {
                let mode = match mode {
                    Mode::Erased => "∀",
                    Mode::Free => "Π",
                };
                write!(f, "{} {}:({}). {}", mode, name, domain, closure)
            },
            Value::IntersectType { name, first, second } => {
                write!(f, "ι {}:({}). {}", name, first, second)
            },
            Value::Equality { left, right } => {
                write!(f, "{{{} ≃ {}}}", left, right)
            },
            Value::Star => write!(f, "★"),
            Value::SuperStar => write!(f, "□"),
        }
    }
}

pub trait ValueEx {
    fn apply_spine(&self, db: &Database, spine: Spine) -> Rc<Value>;
    fn quote(&self, db: &Database, level: Level) -> Term;
}

impl ValueEx for Rc<Value> {
    fn apply_spine(&self, db: &Database, spine: Spine) -> Rc<Value> {
        spine.iter()
            .fold(self.clone(), |ref acc, entry| acc.apply(db, entry.clone()))
    }

    fn quote(&self, db: &Database, level: Level) -> Term {
        Value::reify(self.clone(), db, level, false)
    }
}

impl Value {
    pub fn variable(level: impl Into<Level>) -> Rc<Value> {
        Value::variable_with_spine(level, Spine::new())
    }

    pub fn variable_with_spine(level: impl Into<Level>, spine: Spine) -> Rc<Value> {
        Rc::new(Value::Variable { level:level.into(), spine })
    }

    pub fn reference(id: Id, spine: Spine, unfolded: Option<Rc<LazyValue>>) -> Rc<Value> {
        Rc::new(Value::Reference { id, spine, unfolded })
    }

    pub fn lambda(mode: Mode, name: Symbol, closure: Closure) -> Rc<Value> {
        Rc::new(Value::Lambda { mode, name, closure })
    }

    pub fn pi(mode: Mode, name: Symbol, domain: Rc<Value>, closure: Closure) -> Rc<Value> {
        Rc::new(Value::Pi { mode, name, domain, closure })
    }

    pub fn intersect_type(name: Symbol, first: Rc<Value>, second: Closure) -> Rc<Value> {
        Rc::new(Value::IntersectType { name, first, second })
    }

    pub fn equality(left: Rc<Value>, right: Rc<Value>) -> Rc<Value> {
        Rc::new(Value::Equality { left, right })
    }

    pub fn star() -> Rc<Value> {
        Rc::new(Value::Star)
    }

    pub fn super_star() -> Rc<Value> {
        Rc::new(Value::SuperStar)
    }

    pub fn id() -> Rc<Value> {
        let body_term = Rc::new(Term::Bound { index:0.into() });
        let body = Closure::new(Symbol::default(), Environment::new(), body_term);
        Value::lambda(Mode::Free, Symbol::from("x"), body)
    }

    pub fn top_type() -> Rc<Value> {
        Value::equality(Value::id(), Value::id())
    }

    pub fn classifier(sort: Sort) -> Rc<Value> {
        match sort {
            Sort::Term => unreachable!(),
            Sort::Type => Value::star(),
            Sort::Kind => Value::super_star(),
        }
    }

    fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<Value> {
        match self {
            Value::Variable { level, spine } => {
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::variable_with_spine(*level, spine)
            },
            Value::Reference { id, spine, unfolded } => {
                let unfolded = unfolded.as_ref()
                    .map(|v| v.apply(db, arg.clone()));
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::reference(id.clone(), spine, unfolded)
            },
            Value::Lambda { mode, closure, .. } => {
                match (*mode, arg.apply_type.to_mode()) {
                    (Mode::Erased, Mode::Free) => {
                        let input = LazyValue::computed(Value::variable(closure.env.len()));
                        let body = closure.eval(db, SpineEntry::new(arg.apply_type, input));
                        body.apply(db, arg)
                    }
                    _ => closure.eval(db, arg)
                }
            }
            _ => unreachable!()
        }
    }

    fn reify_spine(db: &Database, level: Level, head: Term, mut spine: Spine, unfold: bool) -> Term {
        if spine.is_empty() { head }
        else {
            spine.iter_mut().fold(head, |acc, arg| {
                let (apply_type, fun) = (arg.apply_type, Rc::new(acc));
                let arg = Rc::new(Value::reify(arg.value.force(db), db, level, unfold));
                Term::Apply { apply_type, fun, arg }
            })
        }
    }

    pub fn reify(value: Rc<Value>, db: &Database, level: Level, unfold: bool) -> Term {
        let value =
            if unfold { Value::unfold_to_head(db, value) }
            else { value };
        match value.as_ref() {
            Value::Variable { level:vlvl, spine } => {
                let var = Term::Bound { index: vlvl.to_index(*level) };
                Value::reify_spine(db, level, var, spine.clone(), unfold)
            }
            Value::Reference { id, spine, .. } => {
                let var = Term::Free { id:id.clone() };
                Value::reify_spine(db, level, var, spine.clone(), unfold)
            }
            Value::Lambda { mode, name, closure } => {
                let (mode, name) = (*mode, *name);
                let input = EnvEntry::new(name, LazyValue::computed(Value::variable(level)));
                let body = Rc::new(Value::reify(closure.eval(db, input), db, level + 1, unfold));
                Term::Lambda { mode, name, body }
            }
            Value::Pi { mode, name, domain, closure } => {
                let (mode, name) = (*mode, *name);
                let input = EnvEntry::new(name, LazyValue::computed(Value::variable(level)));
                let domain = Rc::new(Value::reify(domain.clone(), db, level, unfold));
                let body = Rc::new(Value::reify(closure.eval(db, input), db, level + 1, unfold));
                Term::Pi { mode, name, domain, body }
            },
            Value::IntersectType { name, first, second } => {
                let input = EnvEntry::new(*name, LazyValue::computed(Value::variable(level)));
                let first = Rc::new(Value::reify(first.clone(), db, level, unfold));
                let second = Rc::new(Value::reify(second.eval(db, input), db, level + 1, unfold));
                Term::IntersectType { name:*name, first, second }
            },
            Value::Equality { left, right } => {
                let left = Rc::new(Value::reify(left.clone(), db, level, unfold));
                let right = Rc::new(Value::reify(right.clone(), db, level, unfold));
                Term::Equality { left, right }
            }
            Value::Star => Term::Star,
            Value::SuperStar => Term::SuperStar,
        }
    }

    pub fn eval(db: &Database, module: Symbol, env: Environment, term: Rc<Term>) -> Rc<Value> {
        Value::eval_naive(db, module, env, term)
    }

    fn eval_naive(db: &Database, module: Symbol, mut env: Environment, term: Rc<Term>) -> Rc<Value> {
        let result = match term.as_ref() {
            Term::Lambda { mode, name, body } => {
                let (mode, name) = (*mode, *name);
                let closure = Closure::new(module, env.clone(), body.clone());
                Value::lambda(mode, name, closure)
            },
            Term::Let { name, let_body, body, .. } => {
                let def_value = LazyValue::new(module, env.clone(), let_body.clone());
                env.push_back(EnvEntry::new(*name, def_value));
                Value::eval_naive(db, module, env.clone(), body.clone())
            },
            Term::Pi { mode, name, domain, body } => {
                let (mode, name) = (*mode, *name);
                let domain = Value::eval_naive(db, module, env.clone(), domain.clone());
                let closure = Closure::new(module, env.clone(), body.clone());
                Value::pi(mode, name, domain, closure)
            },
            Term::IntersectType { name, first, second } => {
                let first = Value::eval_naive(db, module, env.clone(), first.clone());
                let second = Closure::new(module, env.clone(), second.clone());
                Value::intersect_type(*name, first, second)
            },
            Term::Equality { left, right } => {
                let left = Value::eval_naive(db, module, env.clone(), left.clone());
                let right = Value::eval_naive(db, module, env.clone(), right.clone());
                Value::equality(left, right)
            },
            Term::Rewrite { body, .. }
            | Term::Annotate { body, .. }
            | Term::Project { body, .. } => Value::eval_naive(db, module, env.clone(), body.clone()),
            Term::Intersect { first, .. } => Value::eval_naive(db, module, env.clone(), first.clone()),
            Term::Separate { .. } => Value::eval_naive(db, module, env.clone(), Rc::new(Term::id())),
            Term::Refl { erasure }
            | Term::Cast { erasure, .. } => Value::eval_naive(db, module, env.clone(), erasure.clone()),
            Term::Apply { apply_type, fun, arg } => {
                let arg = LazyValue::new(module, env.clone(), arg.clone());
                let fun = Value::eval_naive(db, module, env.clone(), fun.clone());
                fun.apply(db, SpineEntry::new(*apply_type, arg))
            },
            Term::Bound { index, .. } => env[index.to_level(env.len())].value.force(db),
            Term::Free { id } => {
                let unfolded = db.lookup_def(module, id);
                Value::reference(id.clone(), Spine::new(), unfolded)
            }
            Term::Star => Value::star(),
            Term::SuperStar => Value::super_star()
        };
        log::trace!("\n{}\n        {}\n{} {}", env, term, "eval to".bright_blue(), result);
        result
    }

    pub fn unfold_to_head(db: &Database, value: Rc<Value>) -> Rc<Value> {
        match &*value {
            Value::Reference { unfolded, .. } => {
                if let Some(unfolded) = unfolded {
                    Value::unfold_to_head(db, unfolded.force(db))
                } else { value }
            },
            _ => value
        }
    }

    fn convertible_spine(db: &Database, sort: Sort, env: Level, mut left: Spine, mut right: Spine) -> bool {
        let mut result = true;
        let (mut i, mut j) = (0, 0);

        while i < left.len() && j < right.len() {
            let (l, r) = (&mut left[i], &mut right[j]);
            match sort {
                Sort::Term => {
                    let l_is_erased = l.apply_type.to_mode() == Mode::Erased;
                    let r_is_erased = r.apply_type.to_mode() == Mode::Erased;
                    i += if l_is_erased { 1 } else { 0 };
                    j += if r_is_erased { 1 } else { 0 };
                    if !l_is_erased && !r_is_erased {
                        let left = l.value.force(db);
                        let right = r.value.force(db);
                        result &= Value::convertible(db, sort, env, &left, &right);
                        i += 1;
                        j += 1;
                    }
                }
                Sort::Type | Sort::Kind => {
                    let left = l.value.force(db);
                    let right = r.value.force(db);
                    result &= l.apply_type == r.apply_type;
                    result &= Value::convertible(db, sort, env, &left, &right);
                    i += 1;
                    j += 1;
                }
            }
        }
        result && i == left.len() && j == right.len()
    }

    pub fn convertible(db: &Database, sort: Sort, env: Level, left: &Rc<Value>, right: &Rc<Value>) -> bool {
        log::trace!("\n   {}\n{} {}", left, "=?".bright_blue(), right);
        match (left.as_ref(), right.as_ref()) {
            // Type head conversion
            (Value::Star, Value::Star) => true,
            (Value::SuperStar, Value::SuperStar) => true,
            (Value::Pi { mode:m1, name:n1, domain:d1, closure:c1 },
                Value::Pi { mode:m2, name:n2, domain:d2, closure:c2 }) =>
            {
                let input = LazyValue::computed(Value::variable(env));
                let c1 = c1.eval(db, EnvEntry::new(*n1, input.clone()));
                let c2 = c2.eval(db, EnvEntry::new(*n2, input));
                m1 == m2
                && Value::convertible(db, sort, env, d1, d2)
                && Value::convertible(db, sort, env + 1, &c1, &c2)
            }
            (Value::IntersectType { name:n1, first:f1, second:s1 },
                Value::IntersectType { name:n2, first:f2, second:s2 }) =>
            {
                let input = LazyValue::computed(Value::variable(env));
                let s1 = s1.eval(db, EnvEntry::new(*n1, input.clone()));
                let s2 = s2.eval(db, EnvEntry::new(*n2, input));
                Value::convertible(db, sort, env, f1, f2)
                && Value::convertible(db, sort, env + 1, &s1, &s2)
            }
            (Value::Equality { left:l1, right:r1 },
                Value::Equality { left:l2, right:r2 }) =>
            {
                Value::convertible(db, Sort::Term, env, l1, l2)
                && Value::convertible(db, Sort::Term, env, r1, r2)
            }
            // Lambda conversion + eta conversion
            (Value::Lambda { mode, name, closure }, _) => {
                let apply_type = mode.to_apply_type(&sort);
                let input= LazyValue::computed(Value::variable(env));
                let closure = closure.eval(db, EnvEntry::new(*name, input.clone()));
                let v = right.apply(db, SpineEntry::new(apply_type, input));
                Value::convertible(db, sort, env + 1, &closure, &v)
            }
            (_, Value::Lambda { mode, name, closure }) => {
                let apply_type = mode.to_apply_type(&sort);
                let input = LazyValue::computed(Value::variable(env));
                let closure = closure.eval(db, EnvEntry::new(*name, input.clone()));
                let v = left.apply(db, SpineEntry::new(apply_type, input));
                Value::convertible(db, sort, env + 1, &v, &closure)
            }
            // Spines
            (Value::Variable { level:l1, spine:s1},
                Value::Variable { level:l2, spine:s2 }) =>
            {
                l1 == l2 && Value::convertible_spine(db, sort, env, s1.clone(), s2.clone())
            }
            (Value::Reference { id:id1, spine:s1, unfolded:u1 },
                Value::Reference { id:id2, spine:s2, unfolded:u2 }) =>
            {
                let check_unfolded = || {
                    let mut result = false;
                    if let Some(u1) = u1 {
                        if let Some(u2) = u2 {
                            let (u1, u2) = (u1.force(db), u2.force(db));
                            result = Value::convertible(db, sort, env, &u1, &u2);
                        }
                    }
                    result
                };
                (id1 == id2 && Value::convertible_spine(db, sort, env, s1.clone(), s2.clone()))
                    || check_unfolded()
            },
            (Value::Reference { unfolded, .. }, _) => {
                unfolded.as_ref()
                    .map_or(false,
                        |u| Value::convertible(db, sort, env, &u.force(db), right))
            }
            (_, Value::Reference { unfolded, .. }) => {
                unfolded.as_ref()
                    .map_or(false,
                        |u| Value::convertible(db, sort, env, left, &u.force(db)))
            }

            _ => false
        }
    }
}
