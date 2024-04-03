
use std::borrow::Borrow;

use imbl::Vector;

use crate::utility::*;
use crate::database::*;
use crate::term::*;
use crate::value::*;
use crate::eval::*;
use crate::unify::*;

#[derive(Debug, Clone)]
pub struct Context {
    pub module: Symbol,
    pub env: Env,
    pub types: Vector<Value>
}

pub fn infer(db: &mut Database, ctx: Context, t: Term) -> Result<Value, Term> {
    let borrow: &TermData = t.borrow();
    match borrow.clone() {
        TermData::Lambda { sort, mode, name, domain, body } => todo!(),
        TermData::Let { sort, name, let_body, body } => todo!(),
        TermData::Pi { sort, mode, name, domain, body } => todo!(),
        TermData::Intersect { name, first, second } => todo!(),
        TermData::Equality { left, right, anno } => todo!(),
        TermData::Project { variant, body } => {
            let ty = infer(db, ctx.clone(), body)?;
            let ty_unfolded = unfold_to_head(db, ty);
            match ty_unfolded.head() {
                Head::Intersect { name, first, second, .. } => {
                    if variant == 1 {
                        Ok(first.clone())
                    } else {
                        let first_quote = quote(db, first.clone(), ctx.env.len().into());
                        let lazy = LazyValueData::lazy(db, ctx.env, first_quote);
                        let arg = EnvEntry::new(name, Mode::TypeLevel, lazy);
                        Ok(second.eval(db, arg))
                    }
                }
                _ => todo!()
            }
        }
        TermData::Pair { first, second, anno } => todo!(),
        TermData::Separate { equation } => todo!(),
        TermData::Refl { input } => {
            let anno = infer(db, ctx.clone(), input.clone())?;
            let left = LazyValueData::lazy(db, ctx.env, input);
            let right = left.clone();
            Ok(Head::Equality { left, right, anno }.into())
        }
        TermData::Cast { input, witness, evidence } => todo!(),
        TermData::Promote { variant, equation, lhs, rhs } => {
            todo!()
            // let equation_ty = infer(db, ctx.clone(), equation.clone())?;
            // let equation_ty_borrow: &ValueData = equation_ty.borrow();
            // match equation_ty_borrow.clone() {
            //     ValueData::Equality { left, right, anno } => {
            //         let level: Level = ctx.clone().env.len().into();
            //         let left_value = left.force(db);
            //         let left_value = left_value.peel_proj()
            //             .ok_or_else(|| quote(db, left_value, level))?;
            //         let right_value = right.force(db);
            //         let right_value = right_value.peel_proj()
            //             .ok_or_else(|| quote(db, right_value, level))?;
            //         let left = quote(db, left_value, level);
            //         let right = quote(db, right_value, level);
            //         let left_ty = infer(db, ctx.clone(), left.clone())?;
            //         check(db, ctx.clone(), right.clone(), left_ty.clone())?;
            //         let left_ty_borrow: &ValueData = left_ty.borrow();
            //         match left_ty_borrow.clone() {
            //             ValueData::Intersect { name, first, second } => {
            //                 let anno_term = quote(db, anno.clone(), level);
            //                 try_unify(db, level, anno.clone(), first.clone(), anno_term)?;
            //                 let anno = ValueData::Intersect { name, first, second }.rced();
            //                 let left = LazyValueData::lazy(db, ctx.env.clone(), left);
            //                 let right = LazyValueData::lazy(db, ctx.env, right);
            //                 let ty = ValueData::Equality { left, right, anno }.rced();
            //                 Ok(ty)
            //             }
            //             _ => Err(left)
            //         }
            //     }
            //     _ => Err(equation)
            // }
        }
        TermData::Subst { predicate, equation } => todo!(),
        TermData::Apply { sort, mode:m1, fun, arg } => {
            let fun_ty = infer(db, ctx.clone(), fun.clone())?;
            match fun_ty.head() {
                Head::Pi { sort, mode:m2, name, domain, closure } => {
                    let mode = check_mode(m1, m2, arg.clone())?;
                    check(db, ctx.clone(), arg.clone(), domain)?;
                    let lazy_arg = LazyValueData::lazy(db, ctx.env, arg);
                    let ty = closure.eval(db, EnvEntry::new(name, mode, lazy_arg));
                    Ok(ty)
                }
                _ => Err(fun)
            }
        }
        TermData::Bound { sort, index } => {
            let level = index.to_level(ctx.env.len());
            if let Some(ty) = ctx.types.get(*level) {
                Ok(ty.clone())
            } else { Err(t) }
        }
        TermData::Free { sort, id } => {
            if let Some(result) = db.lookup_type(&id) {
                Ok(result)
            } else { Err(t) }
        },
        TermData::Meta { sort, module, name } => unimplemented!(),
        TermData::InsertedMeta { sort, module, name, mask } => unimplemented!(),
        TermData::Star => Ok(Head::SuperStar.into()),
        TermData::SuperStar => Err(t),
    }
}

pub fn check(db: &mut Database, ctx: Context, t: Term, ty: Value) -> Result<(), Term> {
    let inferred_ty = infer(db, ctx.clone(), t.clone())?;
    let level: Level = ctx.env.len().into();
    if unify(db, true, level, inferred_ty, ty.clone()).map_err(|_| t)? { Ok(()) }
    else { Err(quote(db, ty, level)) }
}

fn check_mode(lhs: Mode, rhs: Mode, err: Term) -> Result<Mode, Term> {
    if lhs == rhs { Ok(lhs) }
    else { Err(err) }
}

fn try_unify(db: &mut Database, level: Level, lhs: Value, rhs: Value, err: Term) -> Result<(), Term> {
    if unify(db, true, level, lhs, rhs).map_err(|_| err.clone())? { Ok(()) }
    else { Err(err) }
}

pub fn church_bool_type_value(db: &mut Database) -> Value {
    let module = Symbol::from("gen/church_bool_type_value");
    let env = Env::new();
    let body = db.make_term(TermData::Bound {
        sort: todo!(),
        index: 2.into(),
    });
    let domain = db.make_term(TermData::Bound {
        sort: todo!(),
        index: 1.into(),
    });
    let body = db.make_term(TermData::Pi {
        sort: todo!(),
        mode: todo!(),
        name: todo!(),
        domain,
        body,
    });
    let domain = db.make_term(TermData::Bound {
        sort: todo!(),
        index: 0.into(),
    });
    let code = db.make_term(TermData::Pi {
        sort: todo!(),
        mode: todo!(),
        name: todo!(),
        domain,
        body,
    });
    let closure = Closure::new(env, code);
    Head::Pi {
        sort: Sort::Type,
        mode: Mode::Erased,
        name: Symbol::from("X"),
        domain: Head::Star.into(),
        closure
    }.into()
}

pub fn cast_evidence_ty(db: &Database, domain: Term, witness: Term) -> Term {
    db.make_term(TermData::Pi {
        sort: Sort::Type,
        mode: Mode::Free,
        name: Symbol::from("x"),
        domain: domain.clone(),
        body: db.make_term(TermData::Equality {
            left: db.make_term(TermData::Bound {
                sort: Sort::Term,
                index: 0.into()
            }),
            right: db.make_term(TermData::Project {
                variant: 1,
                body: db.make_term(TermData::Apply {
                    sort: Sort::Term,
                    mode: Mode::Free,
                    fun: witness.shift(db, 1, 0),
                    arg: db.make_term(TermData::Bound {
                        sort: Sort::Term,
                        index: 0.into()
                    }),
                }),
            }),
            anno: domain.shift(db, 1, 0),
        }),
    })
}
