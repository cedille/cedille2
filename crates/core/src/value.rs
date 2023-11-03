
use std::ops;
use std::fmt;
use std::rc::Rc;
use std::cell::RefCell;

use colored::Colorize;
use once_cell::unsync::OnceCell;

use crate::utility::*;
use crate::term::Term;
use crate::metavar::{self, MetaState};
use crate::database::Database;

#[derive(Debug, Clone)]
pub struct EnvEntry {
    name: Symbol,
    mode: Mode,
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
            mode: entry.mode,
            value: entry.value
        }
    }
}

impl EnvEntry {
    pub fn new(name: Symbol, mode: Mode, value: impl Into<LazyValue>) -> EnvEntry {
        EnvEntry { name, mode, value: value.into() }
    }
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum EnvBound {
    Defined,
    Bound
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
    pub mode: Mode,
    pub value: LazyValue,
}

impl fmt::Display for SpineEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let operator = match self.mode {
            Mode::Free => "∞",
            Mode::Erased => "-",
            Mode::TypeLevel => "t"
        };
        write!(f, "({}; {})", operator, self.value)
    }
}

impl SpineEntry {
    pub fn new(mode: Mode, value: LazyValue) -> SpineEntry {
        SpineEntry { mode, value }
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
        Closure {
            module,
            env,
            code
        }
    }

    pub fn eval(&self, db: &Database, arg: impl Into<EnvEntry>) -> Rc<Value> {
        let Closure { module, env, code, .. } = self;
        let mut env = env.clone();
        env.push_back(arg.into());
        Value::eval(db, *module, env, code.clone())
    }
}

impl fmt::Display for Closure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // let ctx = self.env.iter()
        //     .map(|EnvEntry { name, .. }| *name)
        //     .collect::<im_rc::Vector<_>>();
        // write!(f, "{}", self.code.to_string_with_context(ctx))
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
    sort: Option<Sort>,
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
            sort: Some(term.sort()),
            value: OnceCell::new(),
            code: RefCell::new(Some(LazyValueCode { module, env, term }))
        }
    }

    pub fn sort(&self, db: &Database) -> Sort {
        match self.value.get() {
            Some(value) => value.sort(db),
            None => self.sort.unwrap()
        }
    }

    pub fn computed(value: Rc<Value>) -> LazyValue {
        LazyValue {
            sort: None,
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
        unfolded: Option<Rc<LazyValue>>
    },
    Lambda {
        sort: Sort,
        domain_sort: Sort,
        mode: Mode,
        name: Symbol,
        closure: Closure
    },
    Pi {
        sort: Sort,
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
            Value::Variable { level, spine, .. } => {
                if spine.len() == 0 { write!(f, "{}", level) }
                else { write!(f, "{} {}", level, spine) }
            },
            Value::MetaVariable { name, spine, .. } => {
                if spine.len() == 0 { write!(f, "{}", name) }
                else { write!(f, "{} {}", name, spine) }
            },
            Value::Reference { id, spine, unfolded, .. } => {
                if let Some(unfolded) = unfolded { write!(f, "{}", unfolded) }
                else if spine.len() == 0 { write!(f, "{}", id) }
                else { write!(f, "{} {}", id, spine) }
            },
            Value::Lambda { mode, name, closure, .. } => {
                let mode = match mode {
                    Mode::Erased => "Λ",
                    Mode::Free => "λ",
                    Mode::TypeLevel => "λ"
                };
                write!(f, "{} {}. {}", mode, name, closure)
            },
            Value::Pi { mode, name, domain, closure, .. } => {
                let mode = match mode {
                    Mode::Erased => "∀",
                    Mode::Free => "Π",
                    Mode::TypeLevel => "Π",
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
    fn is_closed(&self, db: &Database) -> bool;
}

impl ValueEx for Rc<Value> {
    fn apply_spine(&self, db: &Database, spine: Spine) -> Rc<Value> {
        spine.iter()
            .fold(self.clone(), |ref acc, entry| acc.apply(db, entry.clone()))
    }

    fn quote(&self, db: &Database, level: Level) -> Term {
        Value::reify(self.clone(), db, level, false)
    }

    fn is_closed(&self, db: &Database) -> bool {
        Value::is_closed(db, self, Environment::new())
    }
}

impl Value {
    pub fn variable(sort: Sort, level: impl Into<Level>) -> Rc<Value> {
        Value::variable_with_spine(sort, level, Spine::new())
    }

    pub fn variable_with_spine(sort: Sort, level: impl Into<Level>, spine: Spine) -> Rc<Value> {
        Rc::new(Value::Variable { sort, level:level.into(), spine })
    }

    pub fn meta(sort: Sort, name: Symbol, module: Symbol, spine: Spine) -> Rc<Value> {
        Rc::new(Value::MetaVariable { sort, name, module, spine })
    }

    pub fn reference(sort: Sort, id: Id, spine: Spine, unfolded: Option<Rc<LazyValue>>) -> Rc<Value> {
        Rc::new(Value::Reference { sort, id, spine, unfolded })
    }

    pub fn lambda(sort: Sort, domain_sort: Sort, mode: Mode, name: Symbol, closure: Closure) -> Rc<Value> {
        Rc::new(Value::Lambda { sort, domain_sort, mode, name, closure })
    }

    pub fn pi(sort: Sort, mode: Mode, name: Symbol, domain: Rc<Value>, closure: Closure) -> Rc<Value> {
        Rc::new(Value::Pi { sort, mode, name, domain, closure })
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

    pub fn sort(&self, db: &Database) -> Sort {
        match self {
            Value::Variable { sort, .. } => *sort,
            Value::MetaVariable { sort, name, module, .. } => {
                match db.lookup_meta(*module, *name) {
                    MetaState::Unsolved | MetaState::Frozen => *sort,
                    MetaState::Solved(val) => val.sort(db),
                }
            }
            Value::Reference { sort, .. }
            | Value::Lambda { sort, .. }
            | Value::Pi { sort, .. } => *sort,
            Value::IntersectType { .. }
            | Value::Equality { .. } => Sort::Type,
            Value::Star => Sort::Kind,
            Value::SuperStar => Sort::Unknown,
        }
    }

    pub fn id() -> Rc<Value> {
        let body_term = Rc::new(Term::Bound { sort:Sort::Term, index:0.into() });
        let body = Closure::new(Symbol::default(), Environment::new(), body_term);
        Value::lambda(Sort::Term, Sort::Term, Mode::Free, Symbol::from("x"), body)
    }

    pub fn top_type() -> Rc<Value> {
        Value::equality(Value::id(), Value::id())
    }

    pub fn classifier(sort: Sort) -> Result<Rc<Value>, ()> {
        match sort {
            Sort::Unknown => Err(()),
            Sort::Term => Err(()),
            Sort::Type => Ok(Value::star()),
            Sort::Kind => Ok(Value::super_star()),
        }
    }

    fn apply(&self, db: &Database, arg: SpineEntry) -> Rc<Value> {
        match self {
            Value::Variable { sort, level, spine } => {
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::variable_with_spine(*sort, *level, spine)
            },
            Value::MetaVariable { sort, name, module, spine } => {
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::meta(*sort, *name, *module, spine)
            }
            Value::Reference { sort, id, spine, unfolded } => {
                let unfolded = unfolded.as_ref()
                    .map(|v| v.apply(db, arg.clone()));
                let mut spine = spine.clone();
                spine.push_back(arg);
                Value::reference(*sort, id.clone(), spine, unfolded)
            },
            Value::Lambda { domain_sort, mode, closure, .. } => {
                match (*mode, arg.mode) {
                    (Mode::Erased, Mode::Free) => {
                        let input = LazyValue::computed(Value::variable(*domain_sort, closure.env.len()));
                        let body = closure.eval(db, SpineEntry::new(arg.mode, input));
                        body.apply(db, arg)
                    }
                    (Mode::Free, Mode::Erased) => Rc::new(self.clone()),
                    _ => closure.eval(db, arg)
                }
            }
            Value::Pi { closure, .. } => closure.eval(db, arg),
            _ => {
                eprintln!("{}", self);
                eprintln!("{}", arg);
                unreachable!()
            }
        }
    }

    fn reify_spine(db: &Database, level: Level, head: Term, mut spine: Spine, unfold: bool) -> Term {
        if spine.is_empty() { head }
        else {
            spine.iter_mut().fold(head, |acc, arg| {
                let sort = acc.sort();
                let (mode, fun) = (arg.mode, Rc::new(acc));
                let arg = Rc::new(Value::reify(arg.value.force(db), db, level, unfold));
                Term::Apply { sort, mode, fun, arg }
            })
        }
    }

    pub fn reify(value: Rc<Value>, db: &Database, level: Level, unfold: bool) -> Term {
        let value =
            if unfold { Value::unfold_to_head(db, value) }
            else { value };
        match value.as_ref() {
            Value::Variable { sort, level:vlvl, spine } => {
                let var = Term::Bound { sort: *sort, index: vlvl.to_index(*level) };
                Value::reify_spine(db, level, var, spine.clone(), unfold)
            }
            Value::MetaVariable { name, spine, .. } => {
                let sort = value.sort(db);
                let var = Term::Meta { sort, name: *name };
                Value::reify_spine(db, level, var, spine.clone(), unfold)
            }
            Value::Reference { sort, id, spine, .. } => {
                let var = Term::Free { sort: *sort, id: id.clone() };
                Value::reify_spine(db, level, var, spine.clone(), unfold)
            }
            Value::Lambda { sort, domain_sort, mode, name, closure } => {
                let (sort, domain_sort, mode, name) = (*sort, *domain_sort, *mode, *name);
                let input = EnvEntry::new(name, mode, LazyValue::computed(Value::variable(domain_sort, level)));
                let body = Rc::new(Value::reify(closure.eval(db, input), db, level + 1, unfold));
                Term::Lambda { sort, domain_sort, mode, name, body }
            }
            Value::Pi { sort, mode, name, domain, closure } => {
                let (sort, mode, name) = (*sort, *mode, *name);
                let input = EnvEntry::new(name, mode, LazyValue::computed(Value::variable(domain.sort(db), level)));
                let domain = Rc::new(Value::reify(domain.clone(), db, level, unfold));
                let body = Rc::new(Value::reify(closure.eval(db, input), db, level + 1, unfold));
                Term::Pi { sort, mode, name, domain, body }
            },
            Value::IntersectType { name, first, second } => {
                let input = EnvEntry::new(*name, Mode::Free, LazyValue::computed(Value::variable(first.sort(db), level)));
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

    pub fn eval(db: &Database, module: Symbol, mut env: Environment, term: Rc<Term>) -> Rc<Value> {
        fn eval_meta(db: &Database, sort: Sort, module: Symbol, name: Symbol) -> Rc<Value> {
            match db.lookup_meta(module, name) {
                MetaState::Unsolved | MetaState::Frozen => Value::meta(sort, name, module, Spine::new()),
                MetaState::Solved(v) => v
            }
        }

        let result = match term.as_ref() {
            Term::Lambda { sort, domain_sort, mode, name, body } => {
                let closure = Closure::new(module, env.clone(), body.clone());
                Value::lambda(*sort, *domain_sort, *mode, *name, closure)
            },
            Term::Let { name, let_body, body, .. } => {
                let def_value = LazyValue::new(module, env.clone(), let_body.clone());
                env.push_back(EnvEntry::new(*name, Mode::Free, def_value));
                Value::eval(db, module, env.clone(), body.clone())
            },
            Term::Pi { sort, mode, name, domain, body } => {
                let domain = Value::eval(db, module, env.clone(), domain.clone());
                let closure = Closure::new(module, env.clone(), body.clone());
                Value::pi(*sort, *mode, *name, domain, closure)
            },
            Term::IntersectType { name, first, second } => {
                let first = Value::eval(db, module, env.clone(), first.clone());
                let second = Closure::new(module, env.clone(), second.clone());
                Value::intersect_type(*name, first, second)
            },
            Term::Equality { left, right } => {
                let left = Value::eval(db, module, env.clone(), left.clone());
                let right = Value::eval(db, module, env.clone(), right.clone());
                Value::equality(left, right)
            },
            Term::Project { body, .. } => Value::eval(db, module, env.clone(), body.clone()),
            Term::Intersect { first, .. } => Value::eval(db, module, env.clone(), first.clone()),
            Term::Separate { .. } => Value::eval(db, module, env.clone(), Rc::new(Term::id())),
            Term::Refl { .. } => Value::id(),
            Term::Promote { input } => Value::eval(db, module, env.clone(), input.clone()),
            Term::Induct => Value::id(),
            Term::Cast { input, .. } => Value::eval(db, module, env.clone(), input.clone()),
            Term::Apply { mode, fun, arg, .. } => {
                let arg = LazyValue::new(module, env.clone(), arg.clone());
                let fun = Value::eval(db, module, env.clone(), fun.clone());
                fun.apply(db, SpineEntry::new(*mode, arg))
            },
            Term::Bound { index, .. } => env[index.to_level(env.len())].value.force(db),
            Term::Free { sort, id } => {
                let unfolded = db.lookup_def(module, id);
                Value::reference(*sort, id.clone(), Spine::new(), unfolded)
            }
            Term::Meta { sort, name } => eval_meta(db, *sort, module, *name),
            Term::InsertedMeta { sort, name, mask } => {
                let mut result = eval_meta(db,*sort,  module, *name);
                for (level, bound) in mask.iter().enumerate() {
                    let level = Level::from(level);
                    match bound {
                        EnvBound::Bound => {
                            let arg = &env[level];
                            let arg = SpineEntry::new(arg.mode, arg.value.clone());
                            result = result.apply(db, arg);
                        }
                        EnvBound::Defined => { }
                    }
                }
                result
            }
            Term::Star => Value::star(),
            Term::SuperStar => Value::super_star()
        };
        log::trace!("\n{}\n        {}\n{} {}", env, term, "eval to".bright_blue(), result);
        result
    }

    pub fn unfold_to_head(db: &Database, value: Rc<Value>) -> Rc<Value> {
        let mut result = value;
        loop {
            match result.as_ref() {
                Value::Reference { unfolded, .. } => {
                    if let Some(unfolded) = unfolded {
                        result = Value::unfold_to_head(db, unfolded.force(db));
                    } else { break }
                },
                Value::MetaVariable { name, module, spine, .. } => {
                    match db.lookup_meta(*module, *name) {
                        MetaState::Solved(v) => result = v.apply_spine(db, spine.clone()),
                        MetaState::Unsolved | MetaState::Frozen => break
                    }
                },
                _ => break
            }
        }
        result
    }

    pub fn unfold_meta_to_head(db: &Database, value: Rc<Value>) -> Rc<Value> {
        let mut result = value;
        while let Value::MetaVariable { name, module, spine, .. } = result.as_ref() {
            match db.lookup_meta(*module, *name) {
                MetaState::Solved(v) => result = v.apply_spine(db, spine.clone()),
                MetaState::Unsolved | MetaState::Frozen => break
            }
        }
        // loop {
        //     match result.as_ref() {
        //         Value::MetaVariable { name, module, spine, .. } => {
        //             match db.lookup_meta(*module, *name) {
        //                 MetaState::Solved(v) => result = v.apply_spine(db, spine.clone()),
        //                 MetaState::Unsolved | MetaState::Frozen => break
        //             }
        //         },
        //         _ => break
        //     }
        // }
        result
    }

    fn unify_spine(db: &mut Database, sort: Sort, env: Level, mut left: Spine, mut right: Spine) -> Result<bool, ()> {
        let mut result = true;
        let (mut i, mut j) = (0, 0);

        while i < left.len() && j < right.len() {
            let (l, r) = (&mut left[i], &mut right[j]);
            match sort {
                Sort::Term => {
                    let l_is_erased = l.mode == Mode::Erased;
                    let r_is_erased = r.mode == Mode::Erased;
                    i += if l_is_erased { 1 } else { 0 };
                    j += if r_is_erased { 1 } else { 0 };
                    if !l_is_erased && !r_is_erased {
                        let left = l.value.force(db);
                        let right = r.value.force(db);
                        result &= Value::unify(db, env, &left, &right)?;
                        i += 1;
                        j += 1;
                    }
                }
                Sort::Type | Sort::Kind | Sort::Unknown => {
                    let left = l.value.force(db);
                    let right = r.value.force(db);
                    result &= l.mode == r.mode;
                    result &= Value::unify(db, env, &left, &right)?;
                    i += 1;
                    j += 1;
                }
            }
        }

        let left_remainder_is_erased = {
            let mut result = sort == Sort::Term;
            for _ in i..left.len() {
                if left[i].mode != Mode::Erased { result = false; }
            }
            result
        };
        if left_remainder_is_erased { i = left.len() }
        let right_remainder_is_erased = {
            let mut result = sort == Sort::Term;
            for _ in j..right.len() {
                if right[i].mode != Mode::Erased { result = false; }
            }
            result
        };
        if right_remainder_is_erased { j = right.len() }

        Ok(result && i == left.len() && j == right.len())
    }

    pub fn unify(db: &mut Database, env: Level, left: &Rc<Value>, right: &Rc<Value>) -> Result<bool, ()> {
        let left = Value::unfold_meta_to_head(db, left.clone());
        let right = Value::unfold_meta_to_head(db, right.clone());
        log::trace!("\n   {}\n{} {}", left, "=?".bright_blue(), right);
        match (left.as_ref(), right.as_ref()) {
            // Type head conversion
            (Value::Star, Value::Star) => Ok(true),
            (Value::SuperStar, Value::SuperStar) => Ok(true),
            (Value::Pi { mode:m1, name:n1, domain:d1, closure:c1, .. },
                Value::Pi { mode:m2, name:n2, domain:d2, closure:c2, .. }) =>
            {
                let input = LazyValue::computed(Value::variable(d1.sort(db), env));
                let c1 = c1.eval(db, EnvEntry::new(*n1, *m1, input.clone()));
                let c2 = c2.eval(db, EnvEntry::new(*n2, *m2, input));
                Ok(m1 == m2
                && Value::unify(db, env, d1, d2)?
                && Value::unify(db, env + 1, &c1, &c2)?)
            }
            (Value::IntersectType { name:n1, first:f1, second:s1 },
                Value::IntersectType { name:n2, first:f2, second:s2 }) =>
            {
                let input = LazyValue::computed(Value::variable(f1.sort(db), env));
                let s1 = s1.eval(db, EnvEntry::new(*n1, Mode::Free, input.clone()));
                let s2 = s2.eval(db, EnvEntry::new(*n2, Mode::Free, input));
                Ok(Value::unify(db, env, f1, f2)?
                && Value::unify(db, env + 1, &s1, &s2)?)
            }
            (Value::Equality { left:l1, right:r1 },
                Value::Equality { left:l2, right:r2 }) =>
            {
                Ok(Value::unify(db, env, l1, l2)?
                && Value::unify(db, env, r1, r2)?)
            }
            // Lambda conversion + eta conversion
            (Value::Lambda { domain_sort:d1, mode:m1, name:n1, closure:c1, .. },
                Value::Lambda { domain_sort:d2, mode:m2, name:n2, closure:c2, .. }) 
                if d1 == d2 && m1 == m2 =>
            {
                let input= LazyValue::computed(Value::variable(*d1, env));
                let c1 = c1.eval(db, EnvEntry::new(*n1, *m1, input.clone()));
                let c2 = c2.eval(db, EnvEntry::new(*n2, *m2, input));
                Value::unify(db, env + 1, &c1, &c2)
            }
            // (Value::Lambda { domain_sort, mode, name, closure, .. }, _) => {
            //     let input= LazyValue::computed(Value::variable(*domain_sort, env));
            //     let closure = closure.eval(db, EnvEntry::new(*name, *mode, input.clone()));
            //     let v = right.apply(db, SpineEntry::new(*mode, input));
            //     Value::unify(db, env + 1, &closure, &v)
            // }
            // (_, Value::Lambda { domain_sort, mode, name, closure, .. }) => {
            //     let input = LazyValue::computed(Value::variable(*domain_sort, env));
            //     let closure = closure.eval(db, EnvEntry::new(*name, *mode, input.clone()));
            //     let v = left.apply(db, SpineEntry::new(*mode, input));
            //     Value::unify(db, env + 1, &v, &closure)
            // }
            // Spines
            (Value::Variable { sort, level:l1, spine:s1 },
                Value::Variable { level:l2, spine:s2, .. }) =>
            {
                Ok(l1 == l2 && Value::unify_spine(db, *sort, env, s1.clone(), s2.clone())?)
            }

            (Value::MetaVariable { name:n1, spine:s1, .. },
                Value::MetaVariable { name:n2, spine:s2, .. }) =>
            {
                let sort = left.sort(db);
                Ok(n1 == n2 && Value::unify_spine(db, sort, env, s1.clone(), s2.clone())?)
            }
            (Value::MetaVariable { name, module, spine, .. }, _) => {
                metavar::solve(db, *module, env, *name, spine.clone(), right.clone())?;
                Ok(true)
            }
            (_, Value::MetaVariable { name, module, spine, .. }) => {
                metavar::solve(db, *module, env, *name, spine.clone(), left.clone())?;
                Ok(true)
            }

            (Value::Reference { sort, id:id1, spine:s1, unfolded:u1, .. },
                Value::Reference { id:id2, spine:s2, unfolded:u2, .. }) =>
            {
                let folded_check = id1 == id2 && Value::unify_spine(db, *sort, env, s1.clone(), s2.clone())?;
                let mut check_unfolded = || {
                    let mut result = Ok(false);
                    if let Some(u1) = u1 {
                        if let Some(u2) = u2 {
                            let (u1, u2) = (u1.force(db), u2.force(db));
                            result = Value::unify(db, env, &u1, &u2);
                        }
                    }
                    result
                };
                Ok(folded_check || check_unfolded()?)
            },
            (Value::Reference { unfolded, .. }, _) => {
                unfolded.as_ref()
                    .map_or(Ok(false),
                        |u| Value::unify(db, env, &u.force(db), &right))
            }
            (_, Value::Reference { unfolded, .. }) => {
                unfolded.as_ref()
                    .map_or(Ok(false),
                        |u| Value::unify(db, env, &left, &u.force(db)))
            }
    
            _ => Ok(false)
        }
    }

    fn spine_is_closed(db: &Database, spine: &Spine, env: Environment) -> bool {
        let mut result = true;
        for arg in spine.iter() {
            let value = arg.value.force(db);
            result &= Value::is_closed(db, &value, env.clone());
        }
        result
    }

    fn is_closed(db: &Database, term: &Rc<Value>, mut env: Environment) -> bool {
        match term.as_ref() {
            Value::Variable { level, spine, .. } => {
                match env.get(**level) {
                    Some(_) => Value::spine_is_closed(db, spine, env),
                    None => false
                }
            }
            Value::MetaVariable { spine, name, module, .. } => {
                match db.lookup_meta(*module, *name) {
                    MetaState::Unsolved | MetaState::Frozen => false,
                    MetaState::Solved(v) => v.is_closed(db) && Value::spine_is_closed(db, spine, env),
                }
            }
            Value::Reference { spine, unfolded, .. } => {
                // If there is no unfolded definition, then the reference is free
                if unfolded.is_some() { Value::spine_is_closed(db, spine, env) }
                else { false }
            }
            Value::Lambda { domain_sort, name, closure, .. } => {
                let input = LazyValue::computed(Value::variable(*domain_sort, env.len()));
                let entry = EnvEntry::new(*name, Mode::Free, input);
                let closure = closure.eval(db, entry.clone());
                env.push_back(entry);
                Value::is_closed(db, &closure, env)
            }
            Value::Pi { name, domain, closure, .. } => {
                let domain_is_closed = Value::is_closed(db, domain, env.clone());
                let input = LazyValue::computed(Value::variable(domain.sort(db), env.len()));
                let entry = EnvEntry::new(*name, Mode::Free, input);
                let closure = closure.eval(db, entry.clone());
                env.push_back(entry);
                domain_is_closed && Value::is_closed(db, &closure, env)
            }
            Value::IntersectType { name, first, second } => {
                let first_is_closed = Value::is_closed(db, first, env.clone());
                let input = LazyValue::computed(Value::variable(first.sort(db), env.len()));
                let entry = EnvEntry::new(*name, Mode::Free, input);
                let second = second.eval(db, entry.clone());
                env.push_back(entry);
                first_is_closed && Value::is_closed(db, &second, env)
            }
            Value::Equality { left, right } => {
                Value::is_closed(db, left, env.clone()) && Value::is_closed(db, right, env)
            }
            Value::Star => true,
            Value::SuperStar => true,
        }
    }
}
