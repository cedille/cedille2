
use std::ops;
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;

use once_cell::unsync::OnceCell;

use crate::common::*;
use crate::lang::elaborator::References;
use crate::kernel::core::Term;

#[derive(Debug, Clone)]
pub struct EnvEntry {
    apply_type: ApplyType,
    name: Symbol,
    value: LazyValue,
}

impl fmt::Display for EnvEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let operator = match self.apply_type {
            ApplyType::Free => "∞",
            ApplyType::TermErased => "-",
            ApplyType::TypeErased => "·",
        };
        write!(f, "({}; {}; {})", operator, self.name, self.value)
    }
}

impl EnvEntry {
    pub fn new(apply_type: ApplyType, name: Symbol, value: LazyValue) -> EnvEntry {
        EnvEntry { apply_type, name, value }
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
pub struct Spine(im_rc::Vector<EnvEntry>);

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
    type Target = im_rc::Vector<EnvEntry>;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl ops::DerefMut for Spine {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

#[derive(Debug, Clone)]
pub struct Closure {
    env: Environment,
    code: Rc<Term>
}

impl Closure {
    pub fn apply(&self, refs: References, arg: EnvEntry) -> Rc<Value> {
        let Closure { env, code } = self;
        let mut env = env.clone();
        env.push_back(arg);
        Value::eval(refs, env, code.clone())
    }
}

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{};{}>", self.env, self.code)
    }
}

#[derive(Debug, Clone)]
struct LazyValueCode {
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
            write!(f, "..")
        }
    }
}

impl LazyValue {
    pub fn new(env: Environment, term: Rc<Term>) -> LazyValue {
        LazyValue { 
            value: OnceCell::new(),
            code: RefCell::new(Some(LazyValueCode { env, term }))
        }
    }

    pub fn computed(value: Rc<Value>) -> LazyValue {
        LazyValue {
            value: OnceCell::from(value),
            code: RefCell::new(None)
        }
    }

    pub fn force(&self, refs: References) -> Rc<Value> {
        match self.value.get() {
            Some(value) => value.clone(),
            None => {
                match self.code.take() {
                    Some(code) => {
                        let result = Value::eval(refs, code.env, code.term);
                        self.value.set(result.clone()).ok();
                        result
                    },
                    None => unreachable!()
                }
            }
        }
    }

    pub fn apply(&self, refs: References, arg: EnvEntry) -> LazyValue {
        let value = self.force(refs).apply(refs, arg);
        LazyValue::computed(value)
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
            Value::Reference { id, spine, .. } => {
                if spine.len() == 0 { write!(f, "{}", id) }
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
    fn apply(&self, refs: References, arg: EnvEntry) -> Rc<Value>;
    fn apply_spine(&self, refs: References, spine: Spine) -> Rc<Value>;
    fn quote(&self, refs: References, level: Level) -> Term;
}

impl ValueEx for Rc<Value> {
    fn apply(&self, refs: References, arg: EnvEntry) -> Rc<Value> {
        match self.as_ref() {
            Value::Variable { level, spine } => {
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::variable_with_spine(*level, spine)
            },
            Value::Reference { id, spine, unfolded } => {
                let unfolded = unfolded.as_ref()
                    .map(|v| v.apply(refs, arg.clone()));
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::reference(id.clone(), spine, unfolded)
            },
            Value::Lambda { closure, .. } => closure.apply(refs, arg),
            _ => unreachable!()
        }
    }

    fn apply_spine(&self, refs: References, spine: Spine) -> Rc<Value> {
        spine.iter()
            .fold(self.clone(), |ref acc, entry| acc.apply(refs, entry.clone()))
    }

    fn quote(&self, refs: References, level: Level) -> Term {
        match self.as_ref() {
            Value::Variable { level:vlvl, spine } => {
                let var = Term::Bound { index: vlvl.to_index(*level) };
                Value::quote_spine(refs, level, var, spine.clone())
            }
            Value::Reference { id, spine, .. } => {
                let var = Term::Free { id:id.clone() };
                Value::quote_spine(refs, level, var, spine.clone())
            }
            Value::Lambda { mode, name, closure } => {
                let (mode, name, apply_type) = (*mode, *name, mode.to_apply_type(&Sort::Term));
                let input = EnvEntry::new(apply_type, name, LazyValue::computed(Value::variable(level)));
                let body = Rc::new(closure.apply(refs, input).quote(refs, level + 1));
                Term::Lambda { mode, name, body }
            }
            Value::Pi { mode, name, domain, closure } => {
                let (mode, name, apply_type) = (*mode, *name, ApplyType::TypeErased);
                let input = EnvEntry::new(apply_type, name, LazyValue::computed(Value::variable(level)));
                let domain = Rc::new(domain.quote(refs, level));
                let body = Rc::new(closure.apply(refs, input).quote(refs, level + 1));
                Term::Pi { mode, name, domain, body }
            },
            Value::IntersectType { name, first, second } => {
                let input = EnvEntry::new(ApplyType::TypeErased, *name, LazyValue::computed(Value::variable(level)));
                let first = Rc::new(first.quote(refs, level));
                let second = Rc::new(second.apply(refs, input).quote(refs, level + 1));
                Term::IntersectType { name:*name, first, second }
            },
            Value::Equality { left, right } => {
                let left = Rc::new(left.quote(refs, level));
                let right = Rc::new(right.quote(refs, level));
                Term::Equality { left, right }
            }
            Value::Star => Term::Star,
            Value::SuperStar => Term::SuperStar,
        }
    }
}

impl Value {
    pub fn variable(level: impl Into<Level>) -> Rc<Value> {
        Value::variable_with_spine(level, Spine::new())
    }

    pub fn variable_with_spine(level: impl Into<Level>, spine: Spine) -> Rc<Value> {
        Rc::new(Value::Variable { level:level.into(), spine })
    }

    pub fn reference(id: Id, spine: Spine, unfolded: Option<LazyValue>) -> Rc<Value> {
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

    pub fn classifier(sort: Sort) -> Rc<Value> {
        match sort {
            Sort::Term => unreachable!(),
            Sort::Type => Value::star(),
            Sort::Kind => Value::super_star(),
        }
    }

    pub fn eval(refs: References, mut env: Environment, term: Rc<Term>) -> Rc<Value> {
        match term.as_ref() {
            Term::Lambda { mode, name, body } => {
                let (mode, name) = (*mode, *name);
                let closure = Closure { env, code:body.clone() };
                Value::lambda(mode, name, closure)
            },
            Term::Let { mode, name, let_body, body } => {
                let apply_type = mode.to_apply_type(&Sort::Term);
                let def_value = LazyValue::new(env.clone(), let_body.clone());
                env.push_back(EnvEntry::new(apply_type, *name, def_value));
                Value::eval(refs, env, body.clone())
            },
            Term::Pi { mode, name, domain, body } => {
                let (mode, name) = (*mode, *name);
                let domain = Value::eval(refs, env.clone(), domain.clone());
                let closure = Closure { env, code:body.clone() };
                Value::pi(mode, name, domain, closure)
            },
            Term::IntersectType { name, first, second } => {
                let first = Value::eval(refs, env.clone(), first.clone());
                let second = Closure { env, code:second.clone() };
                Value::intersect_type(*name, first, second)
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
            Term::Apply { apply_type, fun, arg } => {
                let (apply_type, name) = (*apply_type, Symbol::default());
                let arg = LazyValue::new(env.clone(), arg.clone());
                let entry = EnvEntry::new(apply_type, name, arg);
                let fun = Value::eval(refs, env.clone(), fun.clone());
                match fun.as_ref() {
                    Value::Variable { level, spine } => {
                        let mut spine = spine.clone();
                        spine.push_back(entry);
                        Value::variable_with_spine(*level, spine)
                    }
                    Value::Reference { id, spine, unfolded } => {
                        let unfolded = unfolded.as_ref()
                            .map(|v| v.apply(refs, entry.clone()));
                        let mut spine = spine.clone();
                        spine.push_back(entry);
                        Value::reference(id.clone(), spine, unfolded)
                    } 
                    Value::Lambda { closure, .. } => closure.apply(refs, entry),
                    _ => unreachable!()
                }
            },
            Term::Bound { index, .. } => env[index.to_level(env.len())].value.force(refs),
            Term::Free { id, .. } => {
                let unfolded = refs.lookup_def(id).ok()
                    .map(LazyValue::computed);
                Value::reference(id.clone(), Spine::new(), unfolded)
            }
            Term::Star => Value::star(),
            Term::SuperStar => Value::super_star()
        }
    }

    pub fn unfold_to_head(refs: References, value: Rc<Value>) -> Rc<Value> {
        match &*value {
            Value::Reference { unfolded, .. } => {
                if let Some(unfolded) = unfolded {
                    Value::unfold_to_head(refs, unfolded.force(refs))
                } else { value }
            },
            _ => value
        }
    }

    fn convertible_spine(refs: References, env: Level, mut left: Spine, mut right: Spine) -> bool {
        left.len() == right.len()
        && left.iter_mut()
        .zip(right.iter_mut())
        .fold(true, |acc, (l, r)| {
            if l.apply_type == r.apply_type && l.apply_type == ApplyType::Free {
                let left = l.value.force(refs);
                let right = r.value.force(refs);
                acc && Value::convertible(refs, env, &left, &right)
            } else { acc && l.apply_type == r.apply_type }
        })
    }

    pub fn convertible(refs: References, env: Level, left: &Rc<Value>, right: &Rc<Value>) -> bool {
        match (left.as_ref(), right.as_ref()) {
            // Type head conversion
            (Value::Star, Value::Star) => true,
            (Value::SuperStar, Value::SuperStar) => true,
            (Value::Pi { mode:m1, name:n1, domain:d1, closure:c1 },
                Value::Pi { mode:m2, name:n2, domain:d2, closure:c2 }) =>
            {
                let (mode, input) = (ApplyType::Free, LazyValue::computed(Value::variable(env)));
                let c1 = c1.apply(refs, EnvEntry::new(mode, *n1, input.clone()));
                let c2 = c2.apply(refs, EnvEntry::new(mode, *n2, input));
                m1 == m2
                && Value::convertible(refs, env, d1, d2)
                && Value::convertible(refs, env + 1, &c1, &c2)
            }
            (Value::IntersectType { name:n1, first:f1, second:s1 },
                Value::IntersectType { name:n2, first:f2, second:s2 }) =>
            {
                let (mode, input) = (ApplyType::Free, LazyValue::computed(Value::variable(env)));
                let s1 = s1.apply(refs, EnvEntry::new(mode, *n1, input.clone()));
                let s2 = s2.apply(refs, EnvEntry::new(mode, *n2, input));
                Value::convertible(refs, env, f1, f2)
                && Value::convertible(refs, env + 1, &s1, &s2)
            }
            (Value::Equality { left:l1, right:r1 },
                Value::Equality { left:l2, right:r2 }) =>
            {
                Value::convertible(refs, env, l1, l2)
                && Value::convertible(refs, env, r1, r2)
            }
            // Lambda conversion + eta conversion
            (Value::Lambda { mode:m1, name:n1, closure:c1 },
                Value::Lambda { mode:m2, name:n2, closure:c2 }) => {
                let (m1, m2) = (m1.to_apply_type(&Sort::Term), m2.to_apply_type(&Sort::Term));
                let input= LazyValue::computed(Value::variable(env));
                let c1 = c1.apply(refs, EnvEntry::new(m1, *n1, input.clone()));
                let c2 = c2.apply(refs, EnvEntry::new(m2, *n2, input));
                Value::convertible(refs, env + 1, &c1, &c2)
            }
            (Value::Lambda { mode, name, closure }, _) => {
                let mode = mode.to_apply_type(&Sort::Term);
                let input= LazyValue::computed(Value::variable(env));
                let closure = closure.apply(refs, EnvEntry::new(mode, *name, input.clone()));
                let v = right.apply(refs, EnvEntry::new(mode, *name, input));
                Value::convertible(refs, env + 1, &closure, &v)
            }
            (_, Value::Lambda { mode, name, closure }) => {
                let mode = mode.to_apply_type(&Sort::Term);
                let input = LazyValue::computed(Value::variable(env));
                let closure = closure.apply(refs, EnvEntry::new(mode, *name, input.clone()));
                let v = left.apply(refs, EnvEntry::new(mode, *name, input));
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

    fn quote_spine(refs: References, level: Level, head: Term, mut spine: Spine) -> Term {
        if spine.is_empty() { head }
        else {
            spine.iter_mut().fold(head, |acc, arg| {
                let (apply_type, fun) = (arg.apply_type, Rc::new(acc));
                let arg = Rc::new(arg.value.force(refs).quote(refs, level));
                Term::Apply { apply_type, fun, arg }
            })
        }
    }
}
