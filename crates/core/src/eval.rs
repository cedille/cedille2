
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
        match action.clone() {
            Action::Apply(arg_mode, arg) => {
                let ValueData::Lambda { mode, name, closure, .. } = self.as_ref()
                    else { return self.push_action(action) };
                let entry = EnvEntry::new(*name, *mode, arg);
                closure.eval(db, entry)
            }
            Action::Project(variant) => {
                let ValueData::Pair { first, second, .. } = self.as_ref()
                    else { return self.push_action(action) };
                if variant == 1 { first.clone() } else { second.clone() }
            }
            Action::Subst(predicate) => {
                let ValueData::Refl { input } = self.as_ref()
                    else { return self.push_action(action) };
                let predicate = predicate.perform(db, Action::Apply(Mode::TypeLevel, input.clone()));
                Value::id(db, Sort::Term, Mode::Free, predicate)
            }
            Action::Promote(variant, lhs, rhs) => {
                let ValueData::Refl { input } = self.as_ref()
                    else { return self.push_action(action) };
                ValueData::Refl { input: lhs }.rced()
            }
            Action::Separate => self.push_action(action),
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
    fn erase(&self, db: &Database) -> LazyValue;
}

impl ForceValue for LazyValue {
    fn force(&self, db: &Database) -> Value {
        let v =
            if self.erased { self.object.get().cloned() }
            else { self.value.get().cloned() };
        match v {
            Some(v) => v,
            None => {
                let (env, code) = (self.env.clone(), self.code.clone());
                if self.erased {
                    let new_object = code.erase(db, env);
                    self.object.set(new_object.clone()).ok();
                    new_object
                } else {
                    let new_value = eval(db, env, code);
                    self.value.set(new_value.clone()).ok();
                    new_value
                }
            }
        }
    }

    fn erase(&self, db: &Database) -> LazyValue {
        let erased = true;
        let result = LazyValueData {
            value: self.value.clone(),
            object: self.object.clone(),
            erased,
            env: self.env.clone(),
            code: self.code.clone(),
        };
        db.make_value(result)
    }
}

impl Closure {
    pub fn eval(&self, db: &Database, arg: EnvEntry) -> Value {
        let Closure { env, code, erased } = self;
        let mut env = env.clone();
        env.push_back(arg);
        if *erased { code.erase(db, env) }
        else { eval(db, env.clone(), code.clone()) }
    }
}

pub fn eval(db: &Database, env: Env, term: Term) -> Value {
    fn eval_meta(db: &Database, sort: Sort, module: Symbol, name: Symbol) -> Value {
        match db.lookup_meta(module, name) {
            MetaState::Unsolved | MetaState::Frozen => ValueData::MetaVariable {
                sort,
                name,
                module,
                spine: Spine::new(),
            }.rced(),
            MetaState::Solved(v) => v
        }
    }

    //println!("env_len: {}, term: {}", env.len(), term.clone());
    let result = match term.cloned() {
        TermData::Lambda { sort, mode, name, domain, body } => {
            let domain = eval(db, env.clone(), domain);
            let closure = Closure::new(env, body);
            ValueData::Lambda { sort, mode, name, domain, closure }.rced()
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
            ValueData::Pi { sort, mode, name, domain, closure }.rced()
        }
        TermData::Intersect { name, first, second } => {
            let first = eval(db, env.clone(), first);
            let second = Closure::new(env, second);
            ValueData::Intersect { name, first, second }.rced()
        }
        TermData::Equality { left, right, anno } => {
            let left = LazyValueData::lazy(db, env.clone(), left);
            let right = LazyValueData::lazy(db, env.clone(), right);
            let anno = eval(db, env, anno);
            ValueData::Equality { left, right, anno }.rced()
        }
        TermData::Project { variant, body } => {
            let body = eval(db, env, body);
            body.perform(db, Action::Project(variant))
        }
        TermData::Pair { first, second, anno } => {
            let first = eval(db, env.clone(), first);
            let second = eval(db, env.clone(), second);
            let anno = eval(db, env, anno);
            ValueData::Pair { first, second, anno }.rced()
        }
        TermData::Separate { equation } => {
            let equation = eval(db, env, equation);
            equation.perform(db, Action::Separate)
        }
        TermData::Refl { input } => {
            let input = LazyValueData::lazy(db, env.clone(), input);
            ValueData::Refl { input }.rced()
        }
        TermData::Cast { input, witness, evidence } => {
            let input = eval(db, env.clone(), input);
            let witness = eval(db, env.clone(), witness);
            let evidence = eval(db, env, evidence);
            let spine = Vector::new();
            ValueData::Cast { input, witness, evidence, spine }.rced()
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
            // TODO: think about this more
            env.get(*position).unwrap().value.force(db)
        }
        TermData::Free { sort, id } => {
            let spine = Vector::new();
            let unfolded = db.lookup_def(&id);
            ValueData::Reference { sort, id, spine, unfolded }.rced()
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
        TermData::Star => ValueData::Star.rced(),
        TermData::SuperStar => ValueData::SuperStar.rced()
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
    let borrow: &ValueData = value.borrow();
    match borrow.clone() {
        ValueData::Variable { sort, level:vlvl, spine } => {
            let index = vlvl.to_index(*level);
            let head = db.make_term(TermData::Bound { sort, index });
            quote_spine(db, head, spine, level)
        }
        ValueData::MetaVariable { sort, name, module, spine } => {
            let head = db.make_term(TermData::Meta { sort, module, name });
            quote_spine(db, head, spine, level)
        }
        ValueData::Reference { sort, id, spine, .. } => {
            let head = db.make_term(TermData::Free { sort, id });
            quote_spine(db, head, spine, level)
        }
        ValueData::Pair { first, second, anno } => {
            let first = quote(db, first, level);
            let second = quote(db, second, level);
            let anno = quote(db, anno, level);
            db.make_term(TermData::Pair { first, second, anno })
        }
        ValueData::Refl { input } => {
            let input = input.force(db);
            let input = quote(db, input, level);
            db.make_term(TermData::Refl { input })
        }
        ValueData::Cast { input, witness, evidence, spine } => {
            let input = quote(db, input, level);
            let witness = quote(db, witness, level);
            let evidence = quote(db, evidence, level);
            let head = db.make_term(TermData::Cast { input, witness, evidence });
            quote_spine(db, head, spine, level)
        }
        ValueData::Lambda { sort, mode, name, domain, closure } => {
            let domain = quote(db, domain, level);
            let input = EnvEntry::new(name, mode, LazyValueData::var(db, domain.sort(), level));
            let body = closure.eval(db, input);
            let body = quote(db, body, level + 1);
            db.make_term(TermData::Lambda { sort, mode, name, domain, body })
        }
        ValueData::Pi { sort, mode, name, domain, closure } => {
            let domain = quote(db, domain, level);
            let input = EnvEntry::new(name, mode, LazyValueData::var(db, domain.sort(), level));
            let body = closure.eval(db, input);
            let body = quote(db, body, level + 1);
            db.make_term(TermData::Pi { sort, mode, name, domain, body })
        }
        ValueData::Intersect { name, first, second } => {
            let first = quote(db, first, level);
            let input = EnvEntry::new(name, Mode::TypeLevel, LazyValueData::var(db, first.sort(), level));
            let second = second.eval(db, input);
            let second = quote(db, second, level + 1);
            db.make_term(TermData::Intersect { name, first, second })
        }
        ValueData::Equality { left, right, anno } => {
            let (left, right) = (left.force(db), right.force(db));
            let left = quote(db, left, level);
            let right = quote(db, right, level);
            let anno = quote(db, anno, level);
            db.make_term(TermData::Equality { left, right, anno })
        }
        ValueData::Star => db.make_term(TermData::Star),
        ValueData::SuperStar => db.make_term(TermData::SuperStar),
    }
}

pub(crate) fn erase_spine(db: &Database, spine: Spine) -> Spine {
    let mut result = Spine::new();
    for action in spine.iter().cloned() {
        match action {
            Action::Apply(Mode::Erased, _) => { },
            Action::Apply(m, v) => {
                let v = v.erase(db);
                result.push_back(Action::Apply(m, v));
            }
            Action::Project(_) => { },
            Action::Subst(_) => { },
            Action::Promote(_, _, _) => { },
            Action::Separate => { },
        }
    }
    result
}

impl ValueData {
    pub fn erase(&self, db: &Database) -> Value {
        match self.clone() {
            ValueData::Variable { sort, level, spine } => {
                let spine = erase_spine(db, spine);
                ValueData::Variable { sort, level, spine }.rced()
            }
            ValueData::MetaVariable { sort, name, module, spine } => {
                let spine = erase_spine(db, spine);
                ValueData::MetaVariable { sort, name, module, spine }.rced()
            }
            ValueData::Reference { sort, id, spine, unfolded } => {
                let spine = erase_spine(db, spine);
                let unfolded = unfolded.map(|v| v.erase(db));
                ValueData::Reference { sort, id, spine, unfolded }.rced()
            }
            ValueData::Pair { first, .. } => first.erase(db),
            ValueData::Refl { .. } => Value::id(db, Sort::Term, Mode::Free, ValueData::SuperStar.rced()),
            ValueData::Cast { input, spine, .. } => {
                let input = input.erase(db);
                let spine = erase_spine(db, spine);
                input.perform_spine(db, spine)
            }
            ValueData::Lambda { sort, mode, name, domain, closure } => {
                match mode {
                    Mode::Erased => {
                        let name = Symbol::from("gen/erase");
                        let value = LazyValueData::var(db, sort, usize::MAX.into());
                        closure.erase().eval(db, EnvEntry::new(name, Mode::Erased, value))
                    }
                    Mode::Free => {
                        let domain = ValueData::SuperStar.rced();
                        let closure = closure.erase();
                        ValueData::Lambda { sort, mode, name, domain, closure }.rced()
                    }
                    Mode::TypeLevel => {
                        let domain = domain.erase(db);
                        let closure = closure.erase();
                        ValueData::Lambda { sort, mode, name, domain, closure }.rced()
                    }
                }
            }
            ValueData::Pi { sort, mode, name, domain, closure } => {
                let domain = domain.erase(db);
                let closure = closure.erase();
                ValueData::Pi { sort, mode, name, domain, closure }.rced()
            }
            ValueData::Intersect { name, first, second } => {
                let first = first.erase(db);
                let second = second.erase();
                ValueData::Intersect { name, first, second }.rced()
            }
            ValueData::Equality { left, right, anno } => {
                let left = left.erase(db);
                let right = right.erase(db);
                let anno = anno.erase(db);
                ValueData::Equality { left, right, anno }.rced()
            }
            ValueData::Star => ValueData::Star.rced(),
            ValueData::SuperStar => ValueData::SuperStar.rced(),
        }
    }
}

impl TermData {
    pub fn erase(&self, db: &Database, mut env: Env) -> Value {
        fn erase_meta(db: &Database, sort: Sort, module: Symbol, name: Symbol) -> Value {
            match db.lookup_meta(module, name) {
                MetaState::Unsolved | MetaState::Frozen => ValueData::MetaVariable {
                    sort,
                    name,
                    module,
                    spine: Spine::new(),
                }.rced(),
                MetaState::Solved(v) => v
            }
        }

        match self.clone() {
            TermData::Lambda { sort, mode, name, domain, body } => {
                let closure = Closure::new(env.clone(), body).erase();
                if mode == Mode::Erased {
                    let name = Symbol::from("gen/erase");
                    let value = LazyValueData::var(db, sort, usize::MAX.into());
                    let arg = EnvEntry::new(name, Mode::Erased, value);
                    closure.eval(db, arg)
                } else {
                    let domain = if mode == Mode::Free {
                        ValueData::SuperStar.rced()
                    } else {
                        domain.erase(db, env.clone())
                    };
                    ValueData::Lambda { sort, mode, name, domain, closure }.rced()
                }
            }
            TermData::Let { name, let_body, body, .. } => {
                let def = LazyValueData::lazy(db, env.clone(), let_body).erase(db);
                env.push_back(EnvEntry::new(name, Mode::Free, def));
                body.erase(db, env)
            }
            TermData::Pi { sort, mode, name, domain, body } => {
                let domain = domain.erase(db, env.clone());
                let closure = Closure::new(env, body).erase();
                ValueData::Pi { sort, mode, name, domain, closure }.rced()
            }
            TermData::Intersect { name, first, second } => {
                let first = first.erase(db, env.clone());
                let second = Closure::new(env, second).erase();
                ValueData::Intersect { name, first, second }.rced()
            }
            TermData::Equality { left, right, anno } => {
                let left = LazyValueData::lazy(db, env.clone(), left).erase(db);
                let right = LazyValueData::lazy(db, env.clone(), right).erase(db);
                let anno = anno.erase(db, env);
                ValueData::Equality { left, right, anno }.rced()
            }
            TermData::Project { body, .. } => body.erase(db, env),
            TermData::Pair { first, .. } => first.erase(db, env),
            TermData::Separate { equation } => equation.erase(db, env),
            TermData::Refl { .. } => Value::id(db, Sort::Term, Mode::Free, ValueData::SuperStar.rced()),
            TermData::Cast { input, .. } => input.erase(db, env),
            TermData::Promote { equation, .. } => equation.erase(db, env),
            TermData::Subst { equation, ..} => equation.erase(db, env),
            TermData::Apply { mode, fun, arg, .. } => {
                let fun = fun.erase(db, env.clone());
                if mode == Mode::Erased { fun } else {
                    let arg = LazyValueData::lazy(db, env, arg).erase(db);
                    fun.perform(db, Action::Apply(mode, arg))
                }
            }
            TermData::Bound { index, .. } => {
                let position = index.to_level(env.len());
                // TODO: think about this more
                env.get(*position).unwrap().value.erase(db).force(db)
            }
            TermData::Free { sort, id } => {
                let spine = Vector::new();
                let unfolded = db.lookup_def(&id).map(|v| v.erase(db));
                ValueData::Reference { sort, id, spine, unfolded }.rced()
            }
            TermData::Meta { sort, module, name } => erase_meta(db, sort, module, name),
            TermData::InsertedMeta { sort, module, name, mask } => {
                let mut result = erase_meta(db, sort, module, name);
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
            TermData::Star => ValueData::Star.rced(),
            TermData::SuperStar => ValueData::SuperStar.rced()
        }
    }
}


// pub fn reify(value: Rc<Value>, db: &Database, level: Level, unfold: bool) -> Term {
//     let value =
//         if unfold { Value::unfold_to_head(db, value) }
//         else { value };
//     match value.as_ref() {

//         Value::MetaVariable { name, spine, .. } => {

//         }
//     }
// }
