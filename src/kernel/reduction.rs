/*
    TODO: There are definitely better ways of handling reduction
        I speculate that Cedille would benefit the most from using an egraph to track equivalence classes of terms.
        Especially because of the annotate and rewrite constructs, we are frequently checking terms for conversion that are only slightly modified.
        There is a high quality crate for this already as well: `egg`.
        References changing would potentially invalidate the egraph though (if we are including references inside the equivalence classes).

        Andras Kovacs has though a lot about this, so looking into his research before making a decision would be a good idea.
*/

/* use std::time::{Instant, Duration};

use crate::kernel::*;
use crate::database::*;

impl Term {
    fn shift(term: Term, cutoff: isize, amount: isize) -> Term {
        let (mode, sort) = (Mode::Free, Sort::Term);
        match term {
            Term::Apply { fun, arg, .. } => {
                let fun = Box::new(Term::shift(*fun, cutoff, amount));
                let arg = Box::new(Term::shift(*arg, cutoff, amount));
                Term::Apply { mode, sort, fun, arg }
            },
            Term::Lambda { body, .. } => {
                let body = Box::new(Term::shift(*body, cutoff + 1, amount));
                Term::Lambda { mode, sort, body }
            },
            Term::Bound { index, .. } => {
                let shifted = if index < cutoff { index } else { index + amount };
                Term::Bound { sort, index:shifted }
            },
            t @ Term::Free { .. } => t,
            t @ Term::Hole { .. } => t,
            _ => panic!("Precondition violated! Term::shift must be called with an erased term.")
        }
    }

    fn substitute(term: Term, value: Term, var: isize) -> Term {
        let (mode, sort) = (Mode::Free, Sort::Term);
        match term {
            Term::Apply { fun, arg, .. } => {
                let fun = Box::new(Term::substitute(*fun, value.clone(), var));
                let arg = Box::new(Term::substitute(*arg, value, var));
                Term::Apply { mode, sort, fun, arg }
            },
            Term::Lambda { body, .. } => {
                let body = Term::shift(*body, 0, 1);
                let body = Box::new(Term::substitute(body, value, var + 1));
                Term::Lambda { mode, sort, body }
            },
            Term::Bound { index, .. } => {
                if index == var { value } else { Term::Bound { sort, index } }
            },
            t @ Term::Free { .. } => t,
            t @ Term::Hole { .. } => t,
            _ => panic!("Precondition violated! Term::substitute must be called with an erased term.")
            
        }
    }

    fn reduce(body: Term, arg: Term) -> Term {
        let arg = Term::shift(arg, 1, 0);
        let result = Term::substitute(body, arg, 0);
        Term::shift(result, 0, -1)
    }

    fn normalize_step(term: Term) -> (Term, bool) {
        let (mode, sort) = (Mode::Free, Sort::Term);
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
                    (Term::Apply { mode, sort, fun, arg }, is_normal)
                }
            },
            Term::Lambda { body, .. } => {
                let (body, is_normal) = Term::normalize_step(*body);
                let body = Box::new(body);
                (Term::Lambda { mode, sort, body }, is_normal)
            },
            t @ Term::Bound { .. } => (t, true),
            t @ Term::Free { .. } => (t, true),
            t @ Term::Hole { .. } => (t, true),
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
 */