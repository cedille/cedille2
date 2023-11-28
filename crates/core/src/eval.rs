
use std::borrow::Borrow;

use imbl::Vector;

use crate::utility::*;
use crate::database::*;
use crate::term::*;
use crate::value::*;

pub trait PerformAction {
    fn perform(self, db: &mut Database, action: Action) -> Self;
    fn perform_spine(self, db: &mut Database, actions: Spine) -> Self;
}

impl PerformAction for Value {
    fn perform(self, db: &mut Database, action: Action) -> Self {
        match action.clone() {
            Action::Apply(arg_mode, arg) => {
                match self.as_ref() {
                    ValueData::Lambda { mode, name, closure, .. } => {
                        let entry = EnvEntry::new(*name, *mode, arg);
                        closure.eval(db, entry)
                    }
                    _ => self.push_action(action)
                }
            }
            Action::Project(variant) => {
                match self.as_ref() {
                    ValueData::Pair { first, second, .. } => {
                        if variant == 1 { first.clone() }
                        else { second.clone() }
                    },
                    ValueData::Cast { input, spine, .. } => {
                        let len = spine.len();
                        if variant == 1 && len == 0 { input.clone() }
                        else { self.push_action(action) }
                    }
                    _ => self.push_action(action)
                }
            }
            Action::EqInduct(data) => {
                match self.as_ref() {
                    ValueData::Refl { input } => {
                        let case = data.case.force(db);
                        let action = Action::Apply(Mode::Erased, input.clone());
                        case.perform(db, action)
                    }
                    _ => self.push_action(action)
                }
            }
            Action::Promote => {
                match self.as_ref() {
                    ValueData::Refl { input } => {
                        let value = input.force(db);
                        if let Some(inner) = value.peel_first_projection() {
                            let env = input.env.clone();
                            let code = quote(db, inner.clone(), env.len().into());
                            let lazy = LazyValueData::lazy(db, input.module, env, code);
                            lazy.set(inner).ok(); // It is possible we've already forced this lazy value
                            return ValueData::Refl { input: lazy }.rced();
                        }
                        self.push_action(action)
                    }
                    _ => self.push_action(action)
                }
            }
            Action::Separate => self.push_action(action),
        }
    }

    fn perform_spine(self, db: &mut Database, actions: Spine) -> Self {
        let mut result = self;
        for action in actions.iter().cloned() {
            result = result.perform(db, action);
        }
        result
    }
}

pub trait ForceValue {
    fn force(&self, db: &mut Database) -> Value;
    fn erase(&self, db: &mut Database) -> Value;
}

impl ForceValue for LazyValue {
    fn force(&self, db: &mut Database) -> Value {
        let v = self.value.get().cloned();
        match v {
            Some(v) => v,
            None => {
                let (env, code) = (self.env.clone(), self.code.clone());
                let new_value = eval(db, self.module, env, code);
                self.value.set(new_value.clone()).ok();
                new_value
            }
        }
    }

    fn erase(&self, db: &mut Database) -> Value {
        let o = self.object.get().cloned();
        match o {
            Some(o) => o,
            None => {
                let (env, code) = (self.env.clone(), self.code.clone());
                let new_object = eval(db, self.module, env.clone(), code);
                let new_object = erase(db, env.len().into(), new_object);
                self.object.set(new_object.clone()).ok();
                new_object
            }
        }
    }
}

impl Closure {
    pub fn eval(&self, db: &mut Database, arg: EnvEntry) -> Value {
        let Closure { module, env, code, pending_erase } = self;
        let mut env = env.clone();
        env.push_back(arg);
        let value = eval(db, *module, env.clone(), code.clone());
        if *pending_erase { erase(db, env.len().into(), value) }
        else { value }
    }
}

pub fn eval(db: &mut Database, module: Symbol, env: Env, term: Term) -> Value {
    let result = match term.cloned() {
        TermData::Lambda { sort, mode, name, domain, body } => {
            let domain = eval(db, module, env.clone(), domain);
            let closure = Closure::new(module, env, body);
            ValueData::Lambda { sort, mode, name, domain, closure }.rced()
        }
        TermData::Let { name, let_body, body, .. } => {
            let def = LazyValueData::lazy(db, module, env.clone(), let_body);
            let mut env = env.clone();
            env.push_back(EnvEntry::new(name, Mode::Free, def));
            eval(db, module, env, body)
        }
        TermData::Pi { sort, mode, name, domain, body } => {
            let domain = eval(db, module, env.clone(), domain);
            let closure = Closure::new(module, env, body);
            ValueData::Pi { sort, mode, name, domain, closure }.rced()
        }
        TermData::Intersect { name, first, second } => {
            let first = eval(db, module, env.clone(), first);
            let second = Closure::new(module, env, second);
            ValueData::Intersect { name, first, second }.rced()
        }
        TermData::Equality { left, right, anno } => {
            let left = LazyValueData::lazy(db, module, env.clone(), left);
            let right = LazyValueData::lazy(db, module, env.clone(), right);
            let anno = eval(db, module, env, anno);
            ValueData::Equality { left, right, anno }.rced()
        }
        TermData::Project { variant, body } => {
            let body = eval(db, module, env, body);
            body.perform(db, Action::Project(variant))
        }
        TermData::Pair { first, second, anno } => {
            let first = eval(db, module, env.clone(), first);
            let second = eval(db, module, env.clone(), second);
            let anno = eval(db, module, env, anno);
            ValueData::Pair { first, second, anno }.rced()
        }
        TermData::Separate { equation } => {
            let equation = eval(db, module, env, equation);
            equation.perform(db, Action::Separate)
        }
        TermData::Refl { input } => {
            let input = LazyValueData::lazy(db, module, env.clone(), input);
            ValueData::Refl { input }.rced()
        }
        TermData::Cast { input, witness, evidence } => {
            let input = eval(db, module, env.clone(), input);
            let witness = eval(db, module, env.clone(), witness);
            let evidence = eval(db, module, env, evidence);
            let spine = Vector::new();
            ValueData::Cast { input, witness, evidence, spine }.rced()
        }
        TermData::Promote { equation } => {
            let equation = eval(db, module, env, equation);
            equation.perform(db, Action::Promote)
        }
        TermData::EqInduct { domain, predicate, lhs, rhs, equation, case } => {
            let domain = LazyValueData::lazy(db, module, env.clone(), domain);
            let predicate = LazyValueData::lazy(db, module, env.clone(), predicate);
            let lhs = LazyValueData::lazy(db, module, env.clone(), lhs);
            let rhs = LazyValueData::lazy(db, module, env.clone(), rhs);
            let equation = eval(db, module, env.clone(), equation);
            let case = LazyValueData::lazy(db, module, env.clone(), case);
            let data = EqInductData { domain, predicate, lhs, rhs, case }.rced();
            equation.perform(db, Action::EqInduct(data))
        }
        TermData::Apply { mode, fun, arg, .. } => {
            let fun = eval(db, module, env.clone(), fun);
            let arg = LazyValueData::lazy(db, module, env, arg);
            fun.perform(db, Action::Apply(mode, arg))
        }
        TermData::Bound { index, .. } => {
            let position = index.to_level(env.len());
            // TODO: think about this more
            env.get(*position).unwrap().value.force(db)
        }
        TermData::Free { sort, id } => {
            let spine = Vector::new();
            let unfolded = db.lookup_def(module, &id);
            ValueData::Reference { sort, id, spine, unfolded }.rced()
        }
        TermData::Meta { sort, name } => unimplemented!(),
        TermData::InsertedMeta { sort, name, mask } => unimplemented!(),
        TermData::Star => ValueData::Star.rced(),
        TermData::SuperStar => ValueData::SuperStar.rced()
    };

    result
    // fn eval_meta(db: &Database, sort: Sort, module: Symbol, name: Symbol) -> Value {
    //     match db.lookup_meta(module, name) {
    //         MetaState::Unsolved | MetaState::Frozen => Value::meta(sort, name, module, Spine::new()),
    //         MetaState::Solved(v) => v
    //     }
    // }
    //     TermData::Meta { sort, name } => eval_meta(db, *sort, module, *name),
    //     TermData::InsertedMeta { sort, name, mask } => {
    //         let mut result = eval_meta(db,*sort,  module, *name);
    //         for (level, bound) in mask.iter().enumerate() {
    //             let level = Level::from(level);
    //             match bound {
    //                 EnvBound::Bound => {
    //                     let arg = &env[level];
    //                     let arg = SpineEntry::new(arg.mode, arg.value.clone());
    //                     result = result.apply(db, arg);
    //                 }
    //                 EnvBound::Defined => { }
    //             }
    //         }
    //         result
    //     }
}

fn quote_spine(db: &mut Database, head: Term, spine: Spine, level: Level) -> Term {
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
            Action::EqInduct(_) => todo!(),
            Action::Promote => db.make_term(TermData::Promote { equation: acc }),
            Action::Separate => db.make_term(TermData::Separate { equation: acc })
        }
    })
}

pub fn quote(db: &mut Database, value: Value, level: Level) -> Term {
    let borrow: &ValueData = value.borrow();
    match borrow.clone() {
        ValueData::Variable { sort, level:vlvl, spine } => {
            let index = vlvl.to_index(*level);
            let head = db.make_term(TermData::Bound { sort, index });
            quote_spine(db, head, spine, level)
        }
        ValueData::MetaVariable { sort, name, module, spine } => unimplemented!(),
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

pub(crate) fn erase_spine(spine: Spine) -> Spine {
    let mut result = Spine::new();
    for action in spine.iter().cloned() {
        match action {
            Action::Apply(Mode::Erased, _) => { },
            a @ Action::Apply(_, _) => { result.push_back(a); }
            Action::Project(_) => { },
            Action::EqInduct(_) => { },
            Action::Promote => { },
            Action::Separate => { },
        }
    }
    result
}

pub fn erase(db: &mut Database, level: Level, value: Value) -> Value {
    let borrow: &ValueData = value.borrow();
    match borrow.clone() {
        ValueData::Variable { sort, level, spine } => {
            let spine = erase_spine(spine);
            ValueData::Variable { sort, level, spine }.rced()
        }
        ValueData::MetaVariable { sort, name, module, spine } => todo!(),
        ValueData::Reference { sort, id, spine, unfolded } => {
            let spine = erase_spine(spine);
            ValueData::Reference { sort, id, spine, unfolded }.rced()
        }
        ValueData::Pair { first, .. } => first,
        ValueData::Refl { .. } => Value::id(db, Sort::Term, Mode::Free),
        ValueData::Cast { input, spine, .. } => {
            let input = erase(db, level, input);
            let spine = erase_spine(spine);
            input.perform_spine(db, spine)
        }
        ValueData::Lambda { sort, mode, name, domain, closure } => {
            match mode {
                Mode::Erased => {
                    let name = Symbol::from("gen/erase");
                    let value = LazyValueData::var(db, sort, level);
                    closure.erase().eval(db, EnvEntry::new(name, Mode::Erased, value))
                }
                Mode::Free => {
                    let domain = ValueData::SuperStar.rced();
                    let closure = closure.erase();
                    ValueData::Lambda { sort, mode, name, domain, closure }.rced()
                }
                Mode::TypeLevel => {
                    let domain = erase(db, level, domain);
                    let closure = closure.erase();
                    ValueData::Lambda { sort, mode, name, domain, closure }.rced()
                }
            }
        }
        ValueData::Pi { sort, mode, name, domain, closure } => {
            let domain = erase(db, level, domain);
            let closure = closure.erase();
            ValueData::Pi { sort, mode, name, domain, closure }.rced()
        }
        ValueData::Intersect { name, first, second } => {
            let first = erase(db, level, first);
            let second = second.erase();
            ValueData::Intersect { name, first, second }.rced()
        }
        ValueData::Equality { left, right, anno } => {
            left.erase(db);
            right.erase(db);
            let anno = erase(db, level, anno);
            ValueData::Equality { left, right, anno }.rced()
        }
        ValueData::Star => ValueData::Star.rced(),
        ValueData::SuperStar => ValueData::SuperStar.rced(),
    }
}

// pub fn reify(value: Rc<Value>, db: &Database, level: Level, unfold: bool) -> Term {
//     let value =
//         if unfold { Value::unfold_to_head(db, value) }
//         else { value };
//     match value.as_ref() {

//         Value::MetaVariable { name, spine, .. } => {
//             let sort = value.sort(db);
//             let var = Term::Meta { sort, name: *name };
//             Value::reify_spine(db, level, var, spine.clone(), unfold)
//         }
//     }
// }
