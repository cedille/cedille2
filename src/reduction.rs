/*
    TODO: There are definitely better ways of handling reduction
        I speculate that Cedille would benefit the most from using an egraph to track equivalence classes of terms.
        Especially because of the annotate and rewrite constructs, we are frequently checking terms for conversion that are only slightly modified.
        There is a high quality crate for this already as well: `egg`.
        References changing would potentially invalidate the egraph though (if we are including references inside the equivalence classes).

        Andras Kovacs has though a lot about this, so looking into his research before making a decision would be a good idea.
*/

use std::time::{Instant, Duration};

use crate::kernel::*;
use crate::database::*;

impl Term {
    fn shift(term: Term, cutoff: isize, amount: isize) -> Term {
        match term {
            Term::Apply { fun, arg, .. } => {
                let fun = Box::new(Term::shift(*fun, cutoff, amount));
                let arg = Box::new(Term::shift(*arg, cutoff, amount));
                Term::Apply { mode:Mode::Free, fun, arg }
            },
            Term::Lambda { body, .. } => {
                let body = Box::new(Term::shift(*body, cutoff + 1, amount));
                Term::Lambda { mode:Mode::Free, body }
            },
            Term::Var { index } => {
                let shifted = if index < cutoff { index } else { index + amount };
                Term::Var { index:shifted }
            },
            t @ Term::Ref { .. } => t,
            t @ Term::Hole => t,
            _ => panic!("Precondition violated! Term::shift must be called with an erased term.")
        }
    }

    fn substitute(term: Term, value: Term, var: isize) -> Term {
        match term {
            Term::Apply { fun, arg, .. } => {
                let fun = Box::new(Term::substitute(*fun, value.clone(), var));
                let arg = Box::new(Term::substitute(*arg, value, var));
                Term::Apply { mode:Mode::Free, fun, arg }
            },
            Term::Lambda { body, .. } => {
                let body = Term::shift(*body, 0, 1);
                let body = Box::new(Term::substitute(body, value, var + 1));
                Term::Lambda { mode:Mode::Free, body }
            },
            Term::Var { index } => {
                if index == var { value } else { Term::Var { index } }
            },
            t @ Term::Ref { .. } => t,
            t @ Term::Hole => t,
            _ => panic!("Precondition violated! Term::substitute must be called with an erased term.")
            
        }
    }

    fn reduce(body: Term, arg: Term) -> Term {
        let arg = Term::shift(arg, 1, 0);
        let result = Term::substitute(body, arg, 0);
        Term::shift(result, 0, -1)
    }

    fn normalize_step(term: Term) -> (Term, bool) {
        match term {
            Term::Apply { fun, arg, .. } => {
                let (fun, fun_is_normal) = Term::normalize_step(*fun);
                let (arg, arg_is_normal) = Term::normalize_step(*arg);
                if let Term::Lambda { body, .. } = fun {
                    let result = Term::reduce(*body, arg);
                    (result, false)
                } else {
                    let is_normal = fun_is_normal && arg_is_normal;
                    let (fun, arg) = (Box::new(fun), Box::new(arg));
                    (Term::Apply { mode:Mode::Free, fun, arg }, is_normal)
                }
            },
            Term::Lambda { body, .. } => {
                let (body, is_normal) = Term::normalize_step(*body);
                let body = Box::new(body);
                (Term::Lambda { mode:Mode::Free, body }, is_normal)
            },
            t @ Term::Var { .. } => (t, true),
            t @ Term::Ref { .. } => (t, true),
            t @ Term::Hole => (t, true),
            _ => panic!("Precondition violated! Term::normalize_step must be called with an erased term.")
            
        }
    }

    fn contract(term: Term) -> Term {
        match term {
            Term::Apply { fun, arg, .. } => {
                let fun = Box::new(Term::contract(*fun));
                let arg = Box::new(Term::contract(*arg));
                Term::Apply { mode:Mode::Free, fun, arg }
            },
            Term::Lambda { body, .. } => {
                if let Term::Apply { fun, arg, .. } = *body {
                    if let Term::Var { index:0 } = *arg {
                        *fun
                    } else {
                        let body = Term::Apply { mode:Mode::Free, fun, arg };
                        let body = Box::new(Term::contract(body));
                        Term::Lambda { mode:Mode::Free, body }
                    }
                } else {
                    let body = Box::new(Term::contract(*body));
                    Term::Lambda { mode:Mode::Free, body }
                }
            },
            t @ Term::Var { .. } => t,
            t @ Term::Ref { .. } => t,
            t @ Term::Hole => t,
            _ => panic!("Precondition violated! Term::contract must be called with an erased term.")
        }
    }

    pub fn normalize_without_unfolding(term: Term, timeout: Option<Duration>) -> Term {
        let timer = Instant::now();
        let mut result = term;
        let mut finished = false;

        while !finished {
            let (r, is_normal) = Term::normalize_step(result);
            result = r;
            finished = is_normal || timeout.map_or(false, |d| timer.elapsed() > d);
        }
        Term::contract(result)
    }

    pub fn unfold(db: &mut Database, term: Term) -> (Term, bool) {
        match term {
            Term::Apply { fun, arg, .. } => {
                let (fun, fun_unfolded) = Term::unfold(db, *fun);
                let (arg, arg_unfolded) = Term::unfold(db, *arg);
                let (fun, arg) = (Box::new(fun), Box::new(arg));
                let unfolded = fun_unfolded || arg_unfolded;
                (Term::Apply { mode:Mode::Free, fun, arg }, unfolded)
            },
            Term::Lambda { body, .. } => {
                let (body, unfolded) = Term::unfold(db, *body);
                let body = Box::new(body);
                (Term::Lambda { mode:Mode::Free, body }, unfolded)
            },
            t @ Term::Var { .. } => (t, false),
            Term::Ref { id } => (db.normal_from(id).unwrap_term(), true),
            t @ Term::Hole => (t, false),
            _ => panic!("Precondition violated! Term::contract must be called with an erased term.")
        }
    }

    pub fn normalize(db: &mut Database, term: Term, timeout: Option<Duration>) -> Term {
        let mut finished = false;
        let mut result = term;
        while !finished {
            result = Term::normalize_without_unfolding(result, timeout);
            let (unfolded_term, unfolded) = Term::unfold(db, result);
            result = unfolded_term;
            finished = !unfolded;
        }
        result
    }
}

impl Type {
    fn shift(ty: Type, cutoff: isize, amount: isize) -> Type {
        match ty {
            Type::Fn { domain, body } => {
                let body = Box::new(Type::shift(*body, cutoff + 1, amount));
                Type::Fn { domain, body }
            },
            Type::TermFn { mode, domain, body } => {
                let body = Box::new(Type::shift(*body, cutoff + 1, amount));
                Type::TermFn { mode, domain, body }
            },
            Type::Lambda { domain, body } => {
                let body = Box::new(Type::shift(*body, cutoff + 1, amount));
                Type::Lambda { domain, body }
            },
            Type::TermLambda { domain, body } => {
                let body = Box::new(Type::shift(*body, cutoff + 1, amount));
                Type::TermLambda { domain, body }
            },
            Type::Intersection { first, second } => {
                let first = Box::new(Type::shift(*first, cutoff, amount));
                let second = Box::new(Type::shift(*second, cutoff, amount));
                Type::Intersection { first, second }
            },
            Type::Equality { left, right } => {
                let left = Box::new(Term::shift(*left, cutoff, amount));
                let right = Box::new(Term::shift(*right, cutoff, amount));
                Type::Equality { left, right }
            },
            Type::Apply { fun, arg } => {
                let fun = Box::new(Type::shift(*fun, cutoff, amount));
                let arg = Box::new(Type::shift(*arg, cutoff, amount));
                Type::Apply { fun, arg }
            },
            Type::TermApply { fun, arg } => {
                let fun = Box::new(Type::shift(*fun, cutoff, amount));
                let arg = Box::new(Term::shift(*arg, cutoff, amount));
                Type::TermApply { fun, arg }
            },
            Type::Var { index } => {
                let shifted = if index < cutoff { index } else { index + amount };
                Type::Var { index:shifted }
            },
            t @ Type::Ref { .. } => t,
            t @ Type::Hole => t,
        }
    }

    fn substitute(ty: Type, value: TermOrType, var: isize) -> Type {
        match ty {
            Type::Fn { domain, body } => {
                let body = Type::shift(*body, 0 , 1);
                let body = Box::new(Type::substitute(body, value, var + 1));
                Type::Fn { domain, body }
            },
            Type::TermFn { mode, domain, body } => {
                let body = Type::shift(*body, 0, 1);
                let body = Box::new(Type::substitute(body, value, var + 1));
                Type::TermFn { mode, domain, body }
            },
            Type::Lambda { domain, body } => {
                let body = Type::shift(*body, 0, 1);
                let body = Box::new(Type::substitute(body, value, var + 1));
                Type::Lambda { domain, body }
            },
            Type::TermLambda { domain, body } => {
                let body = Type::shift(*body, 0 , 1);
                let body = Box::new(Type::substitute(body, value, var + 1));
                Type::TermLambda { domain, body }
            },
            Type::Intersection { first, second } => {
                let first = Box::new(Type::substitute(*first, value.clone(), var));
                let second = Box::new(Type::substitute(*second, value, var));
                Type::Intersection { first, second }
            },
            Type::Equality { left, right } => {
                let value = value.unwrap_term();
                let left = Box::new(Term::substitute(*left, value.clone(), var));
                let right = Box::new(Term::substitute(*right, value, var));
                Type::Equality { left, right }
            },
            Type::Apply { fun, arg } => {
                let fun = Box::new(Type::substitute(*fun, value.clone(), var));
                let arg = Box::new(Type::substitute(*arg, value, var));
                Type::Apply { fun, arg }
            },
            Type::TermApply { fun, arg } => {
                let fun = Box::new(Type::substitute(*fun, value.clone(), var));
                let arg = Box::new(Term::substitute(*arg, value.unwrap_term(), var));
                Type::TermApply { fun, arg }
            },
            Type::Var { index } => {
                if index == var { value.unwrap_type() } else { Type::Var { index } }
            },
            t @ Type::Ref { .. } => t,
            t @ Type::Hole => t,
        }
    }

    fn reduce(body: Type, arg: TermOrType) -> Type {
        let arg = match arg {
            TermOrType::Term(term) => TermOrType::Term(Term::shift(term, 1, 0)),
            TermOrType::Type(ty) => TermOrType::Type(Type::shift(ty, 1, 0))
        };
        let result = Type::substitute(body, arg, 0);
        Type::shift(result, 0, -1)
    }

    fn normalize_step(ty: Type) -> (Type, bool) {
        match ty {
            t @ Type::Fn { .. } => (t, true),
            t @ Type::TermFn { .. } => (t, true),
            t @ Type::Lambda { .. } => (t, true),
            t @ Type::TermLambda { .. } => (t, true),
            t @ Type::Intersection { .. } => (t, true),
            t @ Type::Equality { .. } => (t, true),
            Type::Apply { fun, arg } => {
                let (fun, fun_is_normal) = Type::normalize_step(*fun);
                if let Type::Lambda { body, .. } = fun {
                    let result = Type::reduce(*body, TermOrType::Type(*arg));
                    (result, false)
                } else {
                    let fun = Box::new(fun);
                    (Type::Apply { fun, arg }, fun_is_normal)
                }
            },
            Type::TermApply { fun, arg } => {
                let (fun, fun_is_normal) = Type::normalize_step(*fun);
                if let Type::TermLambda { body, .. } = fun {
                    let result = Type::reduce(*body, TermOrType::Term(*arg));
                    (result, false)
                } else {
                    let fun = Box::new(fun);
                    (Type::TermApply { fun, arg }, fun_is_normal)
                }
            },
            t @ Type::Var { .. } => (t, true),
            t @ Type::Ref { .. } => (t, true),
            t @ Type::Hole => (t, true),
        }
    }

    pub fn normalize_without_unfolding(ty: Type, timeout: Option<Duration>) -> Type {
        let timer = Instant::now();
        let mut result = ty;
        let mut finished = false;

        while !finished {
            let (r, is_normal) = Type::normalize_step(result);
            result = r;
            finished = is_normal || timeout.map_or(false, |d| timer.elapsed() > d);
        }
        result
    }

    pub fn unfold(db: &mut Database, ty: Type) -> (Type, bool) {
        match ty {
            Type::Fn { domain, body } => {
                let (body, body_unfolded) = Type::unfold(db, *body);
                let body = Box::new(body);
                (Type::Fn { domain, body }, body_unfolded)
            },
            Type::TermFn { mode, domain, body } => {
                let (body, body_unfolded) = Type::unfold(db, *body);
                let body = Box::new(body);
                (Type::TermFn { mode, domain, body }, body_unfolded)
            },
            Type::Lambda { domain, body } => {
                let (body, body_unfolded) = Type::unfold(db, *body);
                let body = Box::new(body);
                (Type::Lambda { domain, body }, body_unfolded)
            },
            Type::TermLambda { domain, body } => {
                let (body, body_unfolded) = Type::unfold(db, *body);
                let body = Box::new(body);
                (Type::TermLambda { domain, body }, body_unfolded)
            },
            Type::Intersection { first, second } => {
                let (first, first_unfolded) = Type::unfold(db, *first);
                let (second, second_unfolded) = Type::unfold(db, *second);
                let (first, second) = (Box::new(first), Box::new(second));
                let unfolded = first_unfolded || second_unfolded;
                (Type::Intersection { first, second }, unfolded)
            },
            t @ Type::Equality { .. } => (t, false),
            Type::Apply { fun, arg } => {
                let (fun, fun_unfolded) = Type::unfold(db, *fun);
                let (arg, arg_unfolded) = Type::unfold(db, *arg);
                let (fun, arg) = (Box::new(fun), Box::new(arg));
                let unfolded = fun_unfolded || arg_unfolded;
                (Type::Apply { fun, arg }, unfolded)
                
            },
            Type::TermApply { fun, arg } => {
                let (fun, fun_unfolded) = Type::unfold(db, *fun);
                let fun = Box::new(fun);
                (Type::TermApply { fun, arg }, fun_unfolded)
            },
            t @ Type::Var { .. } => (t, false),
            Type::Ref { id } => (db.normal_from(id).unwrap_type(), true),
            t @ Type::Hole => (t, false),
        }
    }

    pub fn normalize(db: &mut Database, ty: Type, timeout: Option<Duration>) -> Type {
        let mut finished = false;
        let mut result = ty;
        while !finished {
            result = Type::normalize_without_unfolding(result, timeout);
            let (unfolded_type, unfolded) = Type::unfold(db, result);
            result = unfolded_type;
            finished = !unfolded;
        }
        result
    }

}
