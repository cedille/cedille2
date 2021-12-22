
use crate::kernel::term::{Mode, Term};
use crate::common::debruijn::{Level, Index};
use crate::common::Id;

#[derive(Debug, Clone)]
pub struct Closure<'a> {
    env: Vec<Value<'a>>,
    code: &'a Term
}

impl<'a> Closure<'a> {
    fn apply(self, arg: Value<'a>) -> Value<'a> {
        let Closure { mut env, code } = self;
        env.push(arg);
        eval(env, code)
    }
}

#[derive(Debug, Clone)]
pub enum Value<'a> {
    Variable {
        level: Level,
        spine: Vec<Value<'a>>
    },
    Reference {
        id: &'a Id,
        spine: Vec<Value<'a>>
    },
    Hole { spine: Vec<Value<'a>> },
    Lambda {
        closure: Closure<'a>
    },
    Pi {
        domain: Box<Value<'a>>,
        closure: Closure<'a>
    },
    IntersectType {
        first: Box<Value<'a>>,
        second: Box<Value<'a>>
    },
    Equality {
        left: Box<Value<'a>>,
        right: Box<Value<'a>>
    },
    Star
}

impl<'a> Value<'a> {
    fn apply(self, arg:Value<'a>) -> Value<'a> {
        match self {
            Value::Variable { level, mut spine } => {
                spine.push(arg);
                Value::Variable { level, spine }
            },
            Value::Reference { id, mut spine } => {
                spine.push(arg);
                Value::Reference { id, spine }
            },
            Value::Hole { mut spine } => {
                spine.push(arg);
                Value::Hole { spine }
            },
            Value::Lambda { closure } => closure.apply(arg),
            _ => unreachable!()
        }
    }
}

pub fn eval<'a>(mut env: Vec<Value<'a>>, term: &'a Term) -> Value<'a> {
    match term {
        Term::Lambda { mode, body, .. } => match mode {
            Mode::Erased => eval(env, body.as_ref()),
            Mode::Free => {
                let closure = Closure { env, code:body.as_ref() };
                Value::Lambda { closure }
            },
        },
        Term::Let { mode, def, body, .. } => match mode {
            Mode::Erased => eval(env, body.as_ref()),
            Mode::Free => {
                let def_value = eval(env.clone(), def.body.as_ref());
                env.push(def_value);
                eval(env, body.as_ref())
            }
        },
        Term::Pi { domain, body, .. } => {
            let domain = Box::new(eval(env.clone(), domain.as_ref()));
            let closure = Closure { env, code:body.as_ref() };
            Value::Pi { domain, closure }
        },
        Term::IntersectType { first, second } => {
            let first = Box::new(eval(env.clone(), first.as_ref()));
            env.push(*first.clone());
            let second = Box::new(eval(env, second.as_ref()));
            Value::IntersectType { first, second }
        },
        Term::Equality { left, right } => {
            let left = Box::new(eval(env.clone(), left.as_ref()));
            let right = Box::new(eval(env, right.as_ref()));
            Value::Equality { left, right }
        },
        Term::Rewrite { body, .. }
        | Term::Annotate { body, .. }
        | Term::Project { body, .. } => eval(env, body.as_ref()),
        Term::Intersect { first, .. } => eval(env, first.as_ref()),
        Term::Separate { .. } => unreachable!(),
        Term::Refl { erasure }
        | Term::Cast { erasure, .. } => eval(env, erasure.as_ref()),
        Term::Apply { mode, fun, arg, .. } => match mode {
            Mode::Erased => eval(env, fun.as_ref()),
            Mode::Free => {
                let arg = eval(env.clone(), arg);
                match eval(env.clone(), fun) {
                    Value::Variable { level, mut spine } => {
                        spine.push(arg);
                        Value::Variable { level, spine }
                    },
                    Value::Hole { mut spine } => {
                        spine.push(arg);
                        Value::Hole { spine }
                    },
                    Value::Lambda { closure } => closure.apply(arg),
                    _ => unreachable!()
                }
            },
        },
        Term::Bound { index, .. } => env[**index].clone(),
        Term::Free { id, .. } => {
            Value::Reference { id, spine:vec![] }
        }
        Term::Star => Value::Star,
        Term::Hole { .. } => Value::Hole { spine:vec![] },
    }
}

pub fn convertible(env: Level, left: Value, right: Value) -> bool {
    match (left, right) {
        // Type head conversion
        (Value::Star, Value::Star) => true,
        (Value::Pi { domain:d1, closure:c1 },
            Value::Pi { domain:d2, closure:c2 }) =>
        {
            let input = Value::Variable { level:1.into(), spine:vec![] };
            let c1 = c1.apply(input.clone());
            let c2 = c2.apply(input);
            convertible(env, *d1, *d2)
            && convertible(env + 1, c1, c2)
        }
        (Value::IntersectType { first:f1, second:s1 },
            Value::IntersectType { first:f2, second:s2 }) =>
        {
            todo!()
        }
        (Value::Equality { left:l1, right:r1 },
            Value::Equality { left:l2, right:r2 }) =>
        {
            convertible(env, *l1, *l2)
            && convertible(env, *r1, *r2)
        }
        // Lambda conversion + eta conversion
        (Value::Lambda { closure:c1 }, Value::Lambda { closure:c2 }) => {
            let input = Value::Variable { level:1.into(), spine:vec![] };
            let c1 = c1.apply(input.clone());
            let c2 = c2.apply(input);
            convertible(env + 1, c1, c2)
        }
        (Value::Lambda { closure }, v) => {
            let input = Value::Variable { level:1.into(), spine:vec![] };
            let closure = closure.apply(input.clone());
            let v = v.apply(input);
            convertible(env + 1, closure, v)
        }
        (v, Value::Lambda { closure }) => {
            let input = Value::Variable { level:1.into(), spine:vec![] };
            let closure = closure.apply(input.clone());
            let v = v.apply(input);
            convertible(env + 1, v, closure)
        }
        // Spines
        (Value::Variable { level:l1, spine:mut s1},
            Value::Variable { level:l2, spine:mut s2 }) =>
        {
            l1 == l2
            && s1.drain(..)
                .zip(s2.drain(..))
                .fold(true, |acc, (l, r)| {
                    acc && convertible(env, l, r)
                })
        }

        _ => false
    }
}
