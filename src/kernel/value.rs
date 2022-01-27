
use std::ops;
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;

use colored::Colorize;
use once_cell::unsync::OnceCell;
use tinyvec::TinyVec;

use crate::common::*;
use crate::kernel::core::Term;
use crate::database::Database;

#[derive(Debug, Clone)]
pub struct EnvEntry {
    name: Symbol,
    value: Rc<LazyValue>,
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
    pub fn new(name: Symbol, value: impl Into<Rc<LazyValue>>) -> EnvEntry {
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
    pub value: Rc<LazyValue>,
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
    pub fn new(apply_type: ApplyType, value: Rc<LazyValue>) -> SpineEntry {
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

    pub fn eval(&self, db: &Database, arg: EnvEntry) -> Rc<Value> {
        let Closure { module, env, code } = self;
        let mut env = env.clone();
        env.push_back(arg);
        Value::eval(db, *module, &env, code)
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
    term: Rc<Term>,
    spine: Spine
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

impl LazyValue {
    pub fn new(module: Symbol, env: Environment, term: Rc<Term>) -> LazyValue {
        LazyValue { 
            value: OnceCell::new(),
            code: RefCell::new(Some(LazyValueCode { module, env, term, spine: Spine::new() }))
        }
    }

    fn new_with_spine(module: Symbol, env: Environment, term: Rc<Term>, spine: Spine) -> LazyValue {
        LazyValue {
            value: OnceCell::new(),
            code: RefCell::new(Some(LazyValueCode { module, env, term, spine }))
        }
    }

    pub fn computed(value: Rc<Value>) -> LazyValue {
        LazyValue {
            value: OnceCell::from(value),
            code: RefCell::new(None)
        }
    }

/*     pub fn force(&self, db: &Database) -> Rc<Value> {
        match self.value.get() {
            Some(value) => value.clone(),
            None => {
                match self.code.take() {
                    Some(code) => {
                        let result = Value::eval(db, code.module, &code.env, &code.term);
                        let result = code.spine.iter().fold(result, |acc, arg| {
                            acc.apply(db, arg.clone())
                        });
                        self.value.set(result.clone()).ok();
                        result
                    },
                    None => unreachable!()
                }
            }
        }
    } */
}

pub trait LazyValueEx {
    fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<LazyValue>;
    fn force(&self, db: &Database) -> Rc<Value>;
}

impl LazyValueEx for Rc<LazyValue> {
    fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<LazyValue> {
        let tag = machine::FnTag::LazyApply(self.clone(), arg);
        let mut result = machine::mutual(db, tag);
        result.lazy.pop().unwrap()
    }

    fn force(&self, db: &Database) -> Rc<Value> {
        let tag = machine::FnTag::Force(self.clone());
        let mut result = machine::mutual(db, tag);
        result.value.pop().unwrap()
    }
/*     fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<LazyValue> {
        match self.value.get() {
            Some(value) => Rc::new(LazyValue::computed(value.apply(db, arg))),
            None => {
                let code = self.code.borrow();
                match &*code {
                    Some(code) => {
                        let mut spine = code.spine.clone();
                        spine.push_back(arg);
                        Rc::new(LazyValue::new_with_spine(code.module, code.env.clone(), code.term.clone(), spine))
                    }
                    None => unreachable!()
                }
            }
        }
    } */
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
    fn quote(&self, db: &Database, level: Level) -> Term;
    fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<Value>;
}

impl ValueEx for Rc<Value> {
    fn quote(&self, db: &Database, level: Level) -> Term {
        Value::reify(self.clone(), db, level, false)
    }

    fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<Value> {
        let tag = machine::FnTag::ValueApply(self.clone(), arg);
        let mut result = machine::mutual(db, tag);
        result.value.pop().unwrap()
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

    pub fn get_ref_id(&self) -> Option<Id> {
        match self {
            Value::Reference { id, .. } => Some(id.clone()),
            _ => None
        }
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

/*     fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<Value> {
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
            Value::Lambda { mode, name, closure } => {
                match (*mode, arg.apply_type.to_mode()) {
                    (Mode::Erased, Mode::Free) => {
                        let input = Rc::new(LazyValue::computed(Value::variable(closure.env.len())));
                        let body = closure.eval(db, EnvEntry::new(*name, input));
                        body.apply(db, arg)
                    }
                    _ => closure.eval(db, EnvEntry::new(*name, arg.value))
                }
            }
            _ => unreachable!()
        }
    } */

/*     pub fn reify(value: Rc<Value>, db: &Database, level: Level, unfold: bool) -> Term {
        let tag = machine::FnTag::Reify(value, level, unfold);
        let mut result = machine::mutual(db, tag);
        result.term.pop().unwrap()
    } */

    fn reify_spine(db: &Database, level: Level, head: Term, spine: &Spine, unfold: bool) -> Term {
        if spine.is_empty() { head }
        else {
            spine.iter().fold(head, |acc, arg| {
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
                Value::reify_spine(db, level, var, spine, unfold)
            }
            Value::Reference { id, spine, .. } => {
                let var = Term::Free { id:id.clone() };
                Value::reify_spine(db, level, var, spine, unfold)
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
}

mod machine {
    use super::*;
    #[derive(Debug)]
    pub enum FnTag { 
        ValueEval(Symbol, Environment, Rc<Term>),
        ClosureEval(Closure, EnvEntry),
        ValueApply(Rc<Value>, SpineEntry),
        LazyApply(Rc<LazyValue>, SpineEntry),
        Force(Rc<LazyValue>),
        Reify(Rc<Value>, Level, bool),
        Equal(Sort, Level, *const Rc<Value>, *const Rc<Value>)
    }

    #[derive(Debug)]
    pub struct Return {
        pub value: Vec<Rc<Value>>,
        pub term: Vec<Term>,
        pub lazy: Vec<Rc<LazyValue>>,
        pub equal: Vec<bool>
    }

    impl Return {
        fn new() -> Return {
            Return {
                value: Vec::with_capacity(16),
                term: Vec::with_capacity(16),
                lazy: Vec::with_capacity(16),
                equal: Vec::with_capacity(16)
            }
        }
    }

    type MachineCtx = *const Database;
    type MachineFrame = Frame<MachineCtx, FnTag, Return>;

    pub fn mutual(db: &Database, tag: FnTag) -> Return {
        fn rec(ctx: MachineCtx, tag: FnTag) -> TinyVec<[MachineFrame; 4]> {
            let db = unsafe { ctx.as_ref().unwrap() };
            match tag {
                FnTag::ValueEval(module, env, term) => {
                    value_eval(db, module, env, term)
                }
                FnTag::ClosureEval(closure, entry) => {
                    closure_eval(closure, entry)
                }
                FnTag::ValueApply(value, entry) => {
                    value_apply(value, entry)
                }
                FnTag::LazyApply(value, entry) => {
                    lazy_apply(value, entry)
                }
                FnTag::Force(value) => {
                    force(value)
                }
                FnTag::Reify(value, level, unfold) => {
                    reify(db, value, level, unfold)
                }
                FnTag::Equal(sort, level, left, right) => {
                    let (left, right) = unsafe { (left.as_ref().unwrap(), right.as_ref().unwrap()) };
                    equal(db, sort, level, left, right)
                }
            }
        }
        let mut stack = TinyVec::new();
        stack.push(Frame::Recurse(tag));
        let acc = Return::new();
        let ctx: *const Database = db;
        tail_recurse(stack, acc, rec, ctx)
    }

    fn value_eval(db: &Database, module: Symbol, env: Environment, term: Rc<Term>) -> TinyVec<[MachineFrame; 4]> {
        let mut result = TinyVec::new();
        match term.as_ref() {
            Term::Lambda { mode, name, body } => {
                let (mode, name) = (*mode, *name);
                let closure = Closure::new(module, env, body.clone());
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.value.push(Value::lambda(mode, name, closure));
                    acc
                })));
            },
            Term::Let { name, let_body, body, .. } => {
                let def_value = LazyValue::new(module, env.clone(), let_body.clone());
                let mut env = env;
                env.push_back(EnvEntry::new(*name, def_value));
                result.push(Frame::Recurse(FnTag::ValueEval(module, env, body.clone())));
            },
            Term::Pi { mode, name, domain, body } => {
                result.push(Frame::Recurse(FnTag::ValueEval(module, env.clone(), domain.clone())));
                let (mode, name) = (*mode, *name);
                let closure = Closure::new(module, env, body.clone());
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let domain = acc.value.pop().unwrap();
                    acc.value.push(Value::pi(mode, name, domain, closure));
                    acc
                })));
            },
            Term::IntersectType { name, first, second } => {
                let name = *name;
                result.push(Frame::Recurse(FnTag::ValueEval(module, env.clone(), first.clone())));
                let second = Closure::new(module, env, second.clone());
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let first = acc.value.pop().unwrap();
                    acc.value.push(Value::intersect_type(name, first, second));
                    acc
                })));
            },
            Term::Equality { left, right } => {
                result.push(Frame::Recurse(FnTag::ValueEval(module, env.clone(), left.clone())));
                result.push(Frame::Recurse(FnTag::ValueEval(module, env, right.clone())));
                result.push(Frame::Finish(Box::new(|_, mut acc:Return| {
                    let right = acc.value.pop().unwrap();
                    let left = acc.value.pop().unwrap();
                    acc.value.push(Value::equality(left, right));
                    acc
                })));
            },
            Term::Rewrite { body, .. }
            | Term::Annotate { body, .. }
            | Term::Project { body, .. } => {
                result.push(Frame::Recurse(FnTag::ValueEval(module, env, body.clone())));
            }
            Term::Intersect { first, .. } => {
                result.push(Frame::Recurse(FnTag::ValueEval(module, env, first.clone())));
            }
            Term::Separate { .. } => {
                result.push(Frame::Recurse(FnTag::ValueEval(module, env, Rc::new(Term::id()))));
            }
            Term::Refl { erasure }
            | Term::Cast { erasure, .. } => {
                result.push(Frame::Recurse(FnTag::ValueEval(module, env, erasure.clone())));
            }
            Term::Apply { apply_type, fun, arg } => {
                let apply_type = *apply_type;
                let arg = Rc::new(LazyValue::new(module, env.clone(), arg.clone()));
                result.push(Frame::Recurse(FnTag::ValueEval(module, env, fun.clone())));
                result.push(Frame::RecurseWith(Box::new(move |_, mut acc:Return| {
                    let fun = acc.value.pop().unwrap();
                    let i = FnTag::ValueApply(fun, SpineEntry::new(apply_type, arg));
                    (acc, i)
                })));
            },
            Term::Bound { index, .. } => {
                let value = env[index.to_level(env.len())].value.clone();
                result.push(Frame::Recurse(FnTag::Force(value)));
            }
            Term::Free { id } => {
                let id = id.clone();
                let unfolded = db.lookup_def(module, &id);
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.value.push(Value::reference(id, Spine::new(), unfolded));
                    acc
                })))
            }
            Term::Star => {
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.value.push(Value::star());
                    acc
                })))
            },
            Term::SuperStar => {
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.value.push(Value::super_star());
                    acc
                })))
            }
        };
        result
    }

    fn closure_eval(closure: Closure, entry: EnvEntry) -> TinyVec<[MachineFrame; 4]> {
        let mut result = TinyVec::new();
        let Closure { module, mut env, code } = closure;
        env.push_back(entry);
        result.push(Frame::Recurse(FnTag::ValueEval(module, env, code)));
        result
    }

    fn value_apply(value: Rc<Value>, entry: SpineEntry) -> TinyVec<[MachineFrame; 4]> {
        let mut result = TinyVec::new();
        match value.as_ref() {
            Value::Variable { level, spine } => {
                let (level, mut spine) = (*level, spine.clone());
                spine.push_back(entry);
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.value.push(Value::variable_with_spine(level, spine));
                    acc
                })));
            }
            Value::Reference { id, spine, unfolded } => {
                let (id, mut spine, unfolded) = (id.clone(), spine.clone(), unfolded.clone());
                let unfolded_exists = if let Some(unfolded) = unfolded {
                    result.push(Frame::Recurse(FnTag::LazyApply(unfolded, entry.clone())));
                    true
                } else { false };
                spine.push_back(entry);
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let unfolded = if unfolded_exists {
                        Some(acc.lazy.pop().unwrap())
                    } else { None };
                    acc.value.push(Value::reference(id, spine, unfolded));
                    acc
                })));
            }
            Value::Lambda { mode, closure, .. } => {
                match (*mode, entry.apply_type.to_mode()) {
                    (Mode::Erased, Mode::Free) => {
                        let input = Rc::new(LazyValue::computed(Value::variable(closure.env.len())));
                        let arg = SpineEntry::new(entry.apply_type, input);
                        result.push(Frame::Recurse(FnTag::ClosureEval(closure.clone(), arg.clone().into())));
                        result.push(Frame::RecurseWith(Box::new(move |_, mut acc:Return| {
                            let body = acc.value.pop().unwrap();
                            let result = FnTag::ValueApply(body, arg);
                            (acc, result)
                        })));
                    }
                    _ => {
                        result.push(Frame::Recurse(FnTag::ClosureEval(closure.clone(), entry.into())))
                    }
                }
            }
            _ => unreachable!()
        }
        result
    }

    fn lazy_apply(value: Rc<LazyValue>, entry: SpineEntry) -> TinyVec<[MachineFrame; 4]> {
        let mut result = TinyVec::new();
        match value.value.get() {
            Some(value) => {
                result.push(Frame::Recurse(FnTag::ValueApply(value.clone(), entry)));
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let value = acc.value.pop().unwrap();
                    acc.lazy.push(Rc::new(LazyValue::computed(value)));
                    acc
                })));
            }
            None => {
                let code = value.code.borrow();
                if let Some(LazyValueCode { module, env, term, spine }) = &*code {
                    let (module, env, term, mut spine) =
                        (*module, env.clone(), term.clone(), spine.clone());
                    spine.push_back(entry);
                    let value = Rc::new(LazyValue::new_with_spine(module, env, term, spine));
                    result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                        acc.lazy.push(value);
                        acc
                    })));
                }
            }
        }
        result
    }

    fn force(value: Rc<LazyValue>) -> TinyVec<[MachineFrame; 4]> {
        let mut result = TinyVec::new();
        match value.value.get() {
            Some(value) => {
                let value_clone = value.clone();
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.value.push(value_clone);
                    acc
                })));
            }
            None => {
                if let Some(code) = value.code.take() {
                    let LazyValueCode { module, env, term, spine } = code;
                    result.push(Frame::Recurse(FnTag::ValueEval(module, env, term)));
                    for arg in spine.iter() {
                        let arg_clone = arg.clone();
                        result.push(Frame::RecurseWith(Box::new(move |_, mut acc:Return| {
                            let fun = acc.value.pop().unwrap();
                            let i = FnTag::ValueApply(fun, arg_clone);
                            (acc, i)
                        })));
                    }
                    result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                        let forced_value = acc.value.pop().unwrap();
                        value.value.set(forced_value.clone()).unwrap();
                        acc.value.push(forced_value);
                        acc
                    })));
                }
            }
        };
        result
    }

    fn reify(db: &Database, value: Rc<Value>, level: Level, unfold: bool) -> TinyVec<[MachineFrame; 4]> {
        fn reify_spine(result: &mut TinyVec<[MachineFrame; 4]>, spine: &Spine, level: Level, unfold: bool) {
            for entry in spine.iter() {
                let (apply_type, arg) = (entry.apply_type, entry.value.clone());
                result.push(Frame::Recurse(FnTag::Force(arg)));
                result.push(Frame::RecurseWith(Box::new(move |_, mut acc:Return| {
                    let arg = acc.value.pop().unwrap();
                    let i = FnTag::Reify(arg, level, unfold);
                    (acc, i)
                })));
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let arg = Rc::new(acc.term.pop().unwrap());
                    let fun = Rc::new(acc.term.pop().unwrap());
                    acc.term.push(Term::Apply { apply_type, fun, arg });
                    acc
                })));
            }
        }

        let mut result = TinyVec::new();
        let value =
            if unfold { Value::unfold_to_head(db, value) }
            else { value };
        match value.as_ref() {
            Value::Variable { level:vlvl, spine } => {
                let vlvl = *vlvl;
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.term.push(Term::Bound { index: vlvl.to_index(*level) });
                    acc
                })));
                reify_spine(&mut result, spine, level, unfold);
            }
            Value::Reference { id, spine, .. } => {
                let id = id.clone();
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.term.push(Term::Free { id });
                    acc
                })));
                reify_spine(&mut result, spine, level, unfold);
            }
            Value::Lambda { mode, name, closure } => {
                let (mode, name, closure) = (*mode, *name, closure.clone());
                let input = EnvEntry::new(name, LazyValue::computed(Value::variable(level)));
                result.push(Frame::Recurse(FnTag::ClosureEval(closure, input)));
                result.push(Frame::RecurseWith(Box::new(move |_, mut acc:Return| {
                    let body = acc.value.pop().unwrap();
                    let i = FnTag::Reify(body, level + 1, unfold);
                    (acc, i)
                })));
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let body = Rc::new(acc.term.pop().unwrap());
                    acc.term.push(Term::Lambda { mode, name, body });
                    acc
                })));
            }
            Value::Pi { mode, name, domain, closure } => {
                let (mode, name, domain, closure) =
                    (*mode, *name, domain.clone(), closure.clone());
                let input = EnvEntry::new(name, LazyValue::computed(Value::variable(level)));
                result.push(Frame::Recurse(FnTag::Reify(domain, level, unfold)));
                result.push(Frame::Recurse(FnTag::ClosureEval(closure, input)));
                result.push(Frame::RecurseWith(Box::new(move |_, mut acc:Return| {
                    let body = acc.value.pop().unwrap();
                    let i = FnTag::Reify(body, level + 1, unfold);
                    (acc, i)
                })));
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let body = Rc::new(acc.term.pop().unwrap());
                    let domain = Rc::new(acc.term.pop().unwrap());
                    acc.term.push(Term::Pi { mode, name, domain, body });
                    acc
                })));
            }
            Value::IntersectType { name, first, second } => {
                let (name, first, second) = (*name, first.clone(), second.clone());
                let input = EnvEntry::new(name, LazyValue::computed(Value::variable(level)));
                result.push(Frame::Recurse(FnTag::Reify(first, level, unfold)));
                result.push(Frame::Recurse(FnTag::ClosureEval(second, input)));
                result.push(Frame::RecurseWith(Box::new(move |_, mut acc:Return| {
                    let second = acc.value.pop().unwrap();
                    let i = FnTag::Reify(second, level + 1, unfold);
                    (acc, i)
                })));
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let second = Rc::new(acc.term.pop().unwrap());
                    let first = Rc::new(acc.term.pop().unwrap());
                    acc.term.push(Term::IntersectType { name, first, second });
                    acc
                })));
            }
            Value::Equality { left, right } => {
                let (left, right) = (left.clone(), right.clone());
                result.push(Frame::Recurse(FnTag::Reify(left, level, unfold)));
                result.push(Frame::Recurse(FnTag::Reify(right, level, unfold)));
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    let left = Rc::new(acc.term.pop().unwrap());
                    let right = Rc::new(acc.term.pop().unwrap());
                    acc.term.push(Term::Equality { left, right });
                    acc
                })));
            }
            Value::Star => {
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.term.push(Term::Star);
                    acc
                })));
            }
            Value::SuperStar => {
                result.push(Frame::Finish(Box::new(move |_, mut acc:Return| {
                    acc.term.push(Term::SuperStar);
                    acc
                })));
            }
        }
        result
    }

    fn equal(db: &Database, sort: Sort, level: Level, left: &Rc<Value>, right: &Rc<Value>) -> TinyVec<[MachineFrame; 4]> {
        todo!()
    }
}


impl Value {

    pub fn eval(db: &Database, module: Symbol, env: &Environment, term: &Rc<Term>) -> Rc<Value> {
        let tag = machine::FnTag::ValueEval(module, env.clone(), term.clone());
        let mut result = machine::mutual(db, tag);
        result.value.pop().unwrap()
    }

/*     pub fn eval(db: &Database, module: Symbol, env: &Environment, term: &Rc<Term>) -> Rc<Value> {
        Value::eval_naive(db, module, env, term)
    }

    fn eval_naive(db: &Database, module: Symbol, env: &Environment, term: &Rc<Term>) -> Rc<Value> {
        let result = match term.as_ref() {
            Term::Lambda { mode, name, body } => {
                let (mode, name) = (*mode, *name);
                let closure = Closure::new(module, env.clone(), body.clone());
                Value::lambda(mode, name, closure)
            },
            Term::Let { name, let_body, body, .. } => {
                let def_value = LazyValue::new(module, env.clone(), let_body.clone());
                let mut env = env.clone();
                env.push_back(EnvEntry::new(*name, def_value));
                Value::eval_naive(db, module, &env, body)
            },
            Term::Pi { mode, name, domain, body } => {
                let (mode, name) = (*mode, *name);
                let domain = Value::eval_naive(db, module, env, domain);
                let closure = Closure::new(module, env.clone(), body.clone());
                Value::pi(mode, name, domain, closure)
            },
            Term::IntersectType { name, first, second } => {
                let first = Value::eval_naive(db, module, env, first);
                let second = Closure::new(module, env.clone(), second.clone());
                Value::intersect_type(*name, first, second)
            },
            Term::Equality { left, right } => {
                let left = Value::eval_naive(db, module, env, left);
                let right = Value::eval_naive(db, module, env, right);
                Value::equality(left, right)
            },
            Term::Rewrite { body, .. }
            | Term::Annotate { body, .. }
            | Term::Project { body, .. } => Value::eval_naive(db, module, env, body),
            Term::Intersect { first, .. } => Value::eval_naive(db, module, env, first),
            Term::Separate { .. } => Value::eval_naive(db, module, env, &Rc::new(Term::id())),
            Term::Refl { erasure }
            | Term::Cast { erasure, .. } => Value::eval_naive(db, module, env, erasure),
            Term::Apply { apply_type, fun, arg } => {
                let arg = Rc::new(LazyValue::new(module, env.clone(), arg.clone()));
                let fun = Value::eval_naive(db, module, env, fun);
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
    } */

    pub fn unfold_to_head(db: &Database, value: Rc<Value>) -> Rc<Value> {
        let mut result = value;
        while let Value::Reference { unfolded, .. } = &*result {
            if let Some(unfolded) = unfolded {
                result = unfolded.force(db);
            } else { break }
        }
        result
    }

    fn convertible_spine(db: &Database, sort: Sort, env: Level, mut left: Spine, mut right: Spine) -> bool {
        left.len() == right.len()
        && left.iter_mut()
        .zip(right.iter_mut())
        .fold(true, |acc, (l, r)| {
            match sort {
                Sort::Term => {
                    if l.apply_type == r.apply_type && l.apply_type == ApplyType::Free {
                        let left = l.value.force(db);
                        let right = r.value.force(db);
                        acc && Value::convertible(db, sort, env, &left, &right)
                    } else { acc && l.apply_type == r.apply_type }
                }
                Sort::Type | Sort::Kind => {
                    let left = l.value.force(db);
                    let right = r.value.force(db);
                    acc && l.apply_type == r.apply_type && Value::convertible(db, sort, env, &left, &right)
                }
            }
        })
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
            (Value::Lambda { mode:m1, name:n1, closure:c1 },
                Value::Lambda { mode:m2, name:n2, closure:c2 }) => {
                let input= LazyValue::computed(Value::variable(env));
                let c1 = c1.eval(db, EnvEntry::new(*n1, input.clone()));
                let c2 = c2.eval(db, EnvEntry::new(*n2, input));
                m1 == m2 && Value::convertible(db, sort, env + 1, &c1, &c2)
            }
            (Value::Lambda { mode, name, closure }, _) => {
                let apply_type = mode.to_apply_type(&sort);
                let input= Rc::new(LazyValue::computed(Value::variable(env)));
                let closure = closure.eval(db, EnvEntry::new(*name, input.clone()));
                let v = right.apply(db, SpineEntry::new(apply_type, input));
                Value::convertible(db, sort, env + 1, &closure, &v)
            }
            (_, Value::Lambda { mode, name, closure }) => {
                let apply_type = mode.to_apply_type(&sort);
                let input = Rc::new(LazyValue::computed(Value::variable(env)));
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
