
use std::borrow::Borrow;

use imbl::Vector;

use crate::utility::*;
use crate::database::*;
use crate::term::*;
use crate::value::*;
use crate::metavar::*;

pub trait PerformAction {
    fn perform(self, db: &Database, action: Action) -> Self;
    fn perform_spine(self, db: &Database, actions: Spine) -> Self;
}

impl PerformAction for Value {
    fn perform(self, db: &Database, action: Action) -> Self {
        if !self.spine().is_empty() {
            self.push_action(action)
        } else {
            match action.clone() {
                Action::Apply(arg_mode, arg) => {
                    let Head::Lambda { mode, name, closure, .. } = self.head()
                        else { return self.push_action(action) };
                    let entry = EnvEntry::new(name, mode, arg);
                    closure.eval(db, entry)
                }
                Action::Project(variant) => {
                    let Head::Pair { first, second, .. } = self.head()
                        else { return self.push_action(action) };
                    if variant == 1 { first.clone() } else { second.clone() }
                }
                Action::Subst(predicate) => {
                    let Head::Refl { input } = self.head()
                        else { return self.push_action(action) };
                    let predicate = predicate.perform(db, Action::Apply(Mode::TypeLevel, input.clone()));
                    Value::id(db, Sort::Term, Mode::Free, predicate)
                }
                Action::Promote(variant, lhs, rhs) => {
                    let Head::Refl { input } = self.head()
                        else { return self.push_action(action) };
                    Head::Refl { input: lhs }.into()
                }
                Action::Separate => self.push_action(action),
            }
        }
    }

    fn perform_spine(self, db: &Database, actions: Spine) -> Self {
        let mut result = self;
        for action in actions.iter().cloned() {
            result = result.perform(db, action);
        }
        result
    }
}

pub trait ForceValue {
    fn force(&self, db: &Database) -> Value;
}

impl ForceValue for LazyValue {
    fn force(&self, db: &Database) -> Value {
        let v = self.value.get().cloned();
        match v {
            Some(v) => v,
            None => {
                let (env, code) = (self.env.clone(), self.code.clone());
                let new_value = eval(db, env, code);
                self.value.set(new_value.clone()).ok();
                new_value
            }
        }
    }
}

impl Closure {
    pub fn eval(&self, db: &Database, arg: EnvEntry) -> Value {
        let Closure { env, code } = self;
        let mut env = env.clone();
        env.push_back(arg);
        eval(db, env.clone(), code.clone())
    }
}

pub fn eval(db: &Database, env: Env, term: Term) -> Value {
    fn eval_meta(db: &Database, sort: Sort, module: Symbol, name: Symbol) -> Value {
        match db.lookup_meta(module, name) {
            MetaState::Unsolved | MetaState::Frozen => Head::MetaVariable {
                sort,
                name,
                module,
            }.into(),
            MetaState::Solved(v) => v
        }
    }

    //println!("env_len: {}, term: {}", env.len(), term.clone());
    let result = match term.cloned() {
        TermData::Lambda { sort, mode, name, domain, body } => {
            let domain = eval(db, env.clone(), domain);
            let closure = Closure::new(env, body);
            Head::Lambda { sort, mode, name, domain, closure }.into()
        }
        TermData::Let { name, let_body, body, .. } => {
            let def = LazyValueData::lazy(db, env.clone(), let_body);
            let mut env = env.clone();
            env.push_back(EnvEntry::new(name, Mode::Free, def));
            eval(db, env, body)
        }
        TermData::Pi { sort, mode, name, domain, body } => {
            let domain = eval(db, env.clone(), domain);
            let closure = Closure::new(env, body);
            Head::Pi { sort, mode, name, domain, closure }.into()
        }
        TermData::Intersect { name, first, second } => {
            let first = eval(db, env.clone(), first);
            let second = Closure::new(env, second);
            Head::Intersect { name, first, second }.into()
        }
        TermData::Equality { left, right, anno } => {
            let left = LazyValueData::lazy(db, env.clone(), left);
            let right = LazyValueData::lazy(db, env.clone(), right);
            let anno = eval(db, env, anno);
            Head::Equality { left, right, anno }.into()
        }
        TermData::Project { variant, body } => {
            let body = eval(db, env, body);
            body.perform(db, Action::Project(variant))
        }
        TermData::Pair { first, second, anno } => {
            let first = eval(db, env.clone(), first);
            let second = eval(db, env.clone(), second);
            let anno = eval(db, env, anno);
            Head::Pair { first, second, anno }.into()
        }
        TermData::Separate { equation } => {
            let equation = eval(db, env, equation);
            equation.perform(db, Action::Separate)
        }
        TermData::Refl { input } => {
            let input = LazyValueData::lazy(db, env.clone(), input);
            Head::Refl { input }.into()
        }
        TermData::Cast { input, witness, evidence } => {
            let input = eval(db, env.clone(), input);
            let witness = eval(db, env.clone(), witness);
            let evidence = eval(db, env, evidence);
            Head::Cast { input, witness, evidence }.into()
        }
        TermData::Promote { variant, equation, lhs, rhs } => {
            let lhs = LazyValueData::lazy(db, env.clone(), lhs);
            let rhs = LazyValueData::lazy(db, env.clone(), rhs);
            let equation = eval(db, env, equation);
            equation.perform(db, Action::Promote(variant, lhs, rhs))
        }
        TermData::Subst { predicate, equation } => {
            let predicate = eval(db, env.clone(), predicate);
            let equation = eval(db, env.clone(), equation);
            equation.perform(db, Action::Subst(predicate))
        }
        TermData::Apply { mode, fun, arg, .. } => {
            let fun = eval(db, env.clone(), fun);
            let arg = LazyValueData::lazy(db, env, arg);
            fun.perform(db, Action::Apply(mode, arg))
        }
        TermData::Bound { index, .. } => {
            let position = index.to_level(env.len());
            // eprintln!("===================");
            // for entry in env.iter() { eprintln!("{}", entry.value) }
            // eprintln!("FETCHING: {}", *position);
            // eprintln!("FROM INDEX: {} with LEVEL: {}", *index, env.len());
            let entry = env.get(*position).unwrap().clone();
            entry.value.force(db)
        }
        TermData::Free { sort, id } => {
            let unfolded = db.lookup_def(&id);
            Head::Reference { sort, id, unfolded }.into()
        }
        TermData::Meta { sort, module, name } => eval_meta(db, sort, module, name),
        TermData::InsertedMeta { sort, module, name, mask } => {
            let mut result = eval_meta(db, sort, module, name);
            for (level, bound) in mask.iter().enumerate() {
                let level = Level::from(level);
                match bound {
                    EnvBound::Bound => {
                        let arg = env.get(*level).unwrap();
                        result = result.perform(db, Action::Apply(arg.mode, arg.value.clone()));
                    }
                    EnvBound::Defined => { }
                }
            }
            result
        }
        TermData::Star => Head::Star.into(),
        TermData::SuperStar => Head::SuperStar.into()
    };

    result
}

fn quote_spine(db: &Database, head: Term, spine: Spine, level: Level) -> Term {
    spine.iter().cloned().fold(head, |acc, action| {
        let sort = acc.sort();
        match action {
            Action::Apply(mode, arg) => {
                let arg = arg.force(db);
                let arg = quote(db, arg, level);
                db.make_term(TermData::Apply { sort, mode, fun: acc, arg })
            }
            Action::Project(variant) => {
                db.make_term(TermData::Project { variant, body: acc })
            }
            Action::Subst(predicate) => {
                let predicate = quote(db, predicate, level);
                db.make_term(TermData::Subst { predicate, equation: acc })
            }
            Action::Promote(variant, lhs, rhs) => {
                let lhs = quote(db, lhs.force(db), level);
                let rhs = quote(db, rhs.force(db), level);
                db.make_term(TermData::Promote { variant, lhs, rhs, equation: acc })
            }
            Action::Separate => db.make_term(TermData::Separate { equation: acc })
        }
    })
}

pub fn quote(db: &Database, value: Value, level: Level) -> Term {
    let head = match value.head() {
        Head::Variable { sort, level:vlvl, .. } => {
            let index = vlvl.to_index(*level);
            db.make_term(TermData::Bound { sort, index })
        }
        Head::MetaVariable { sort, name, module } => {
            db.make_term(TermData::Meta { sort, module, name })
        }
        Head::Reference { sort, id, .. } => {
            db.make_term(TermData::Free { sort, id })
        }
        Head::Pair { first, second, anno } => {
            let first = quote(db, first, level);
            let second = quote(db, second, level);
            let anno = quote(db, anno, level);
            db.make_term(TermData::Pair { first, second, anno })
        }
        Head::Refl { input } => {
            let input = input.force(db);
            let input = quote(db, input, level);
            db.make_term(TermData::Refl { input })
        }
        Head::Cast { input, witness, evidence } => {
            let input = quote(db, input, level);
            let witness = quote(db, witness, level);
            let evidence = quote(db, evidence, level);
            db.make_term(TermData::Cast { input, witness, evidence })
        }
        Head::Lambda { sort, mode, name, domain, closure } => {
            let domain = quote(db, domain, level);
            let input = EnvEntry::new(name, mode, LazyValueData::var(db, domain.sort(), level));
            let body = closure.eval(db, input);
            let body = quote(db, body, level + 1);
            db.make_term(TermData::Lambda { sort, mode, name, domain, body })
        }
        Head::Pi { sort, mode, name, domain, closure } => {
            let domain = quote(db, domain, level);
            let input = EnvEntry::new(name, mode, LazyValueData::var(db, domain.sort(), level));
            let body = closure.eval(db, input);
            let body = quote(db, body, level + 1);
            db.make_term(TermData::Pi { sort, mode, name, domain, body })
        }
        Head::Intersect { name, first, second } => {
            let first = quote(db, first, level);
            let input = EnvEntry::new(name, Mode::TypeLevel, LazyValueData::var(db, first.sort(), level));
            let second = second.eval(db, input);
            let second = quote(db, second, level + 1);
            db.make_term(TermData::Intersect { name, first, second })
        }
        Head::Equality { left, right, anno } => {
            let (left, right) = (left.force(db), right.force(db));
            let left = quote(db, left, level);
            let right = quote(db, right, level);
            let anno = quote(db, anno, level);
            db.make_term(TermData::Equality { left, right, anno })
        }
        Head::Star => db.make_term(TermData::Star),
        Head::SuperStar => db.make_term(TermData::SuperStar),
    };
    quote_spine(db, head, value.spine(), level)
}
