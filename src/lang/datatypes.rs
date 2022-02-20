use std::rc::Rc;

use crate::common::*;
use crate::kernel::core;
use crate::kernel::value::{Value, ValueEx, Closure, LazyValue, EnvEntry, Environment, EnvBound, SpineEntry};

use crate::database::Database;
use crate::lang::elaborator::Context;

pub fn subtype(db: &mut Database, ctx: Context, mut t1: Rc<Value>, mut t2: Rc<Value>, w: Rc<Value>,
               base1: Rc<Value>, base2: Rc<Value>) -> Result<Rc<core::Term>, ()> {
    t1 = Value::unfold_to_head(db, t1);
    t2 = Value::unfold_to_head(db, t2);

    match (t1.as_ref() , t2.as_ref()) {
        (Value::Variable{ level:l1 , spine:s1} , Value::Variable{ level:l2 , spine:s2}) => {
            if l1 == l2 {
                let spines_conv = Value::unify_spine(db, Sort::Type, ctx.env(), s1.clone(), s2.clone())?;

                if spines_conv {
                    Ok(core::Term::id())
                } else {
                    Err(())
                }
            } else {
                if s1.is_empty() && s2.is_empty() {
                    let t1prime = ctx.env()[l1].value.force(db);
                    let t2prime = ctx.env()[l2].value.force(db);

                    if Value::unify(db, Sort::Type, ctx.env(), t1prime, &base1)?
                        && Value::unify(db, Sort::Type, ctx.env(), t2prime, &base2)? {
                            Ok(w.quote(db, ctx.env_lvl()))
                        } {
                            Err(())
                        }
                } else {
                    Err(())
                }
            }

            // let is_conv =

            //     Value::unify_spine(db, Sort::Type, ctx.env(), s1.clone(), s2.clone())?;
        },
        (Value::Pi {mode: m1, domain: dom1, name: name1, closure: close1}
         , Value::Pi {mode: m2, domain: dom2, name: name2, closure: close2}) => {
            let c1_elabed = subtype(db, ctx, dom2, dom1, w, base1, base2)?;
            let c1 = Value::eval(db, ctx.module, ctx.env(), c1_elabed);

            let lv = ctx.env_lvl();
            let input1 = Value::variable(lv);
            let input2 = c1.apply(db, input1);

            let omaewa = Symbol::default();
            let sub_ctx = ctx.bind(omaewa, Mode::Free, dom2);

            let close1prime = close1.eval(db, EnvEntry::new(omaewa, Mode::Free, input2));
            let close2prime = close2.eval(db, EnvEntry::new(omaewa, Mode::Free, input1));

            let c2_elabed = subtype(db, sub_ctx, close1prime, close2prime, w, base1, base2);
            let c2 = Value::eval(db, sub_ctx.module, sub_ctx.env(), c2_elabed);

            // Value::lambda(Mode::Free, name, closure)
            let lvf = ctx.env_lvl();
            let lvx = ctx.env_lvl() + 1;
            let varfp = Value::variable(lvf);
            let varxp = Value::variable(lvx);
            let varf = LazyValue::computed(varfp);
            let varx = LazyValue::computed(varxp);

            let ctx_wip =
                ctx.bind(Symbol::default(), Mode::Free, Value::top_type())
                    .bind(Symbol::default(), *m1, Value::top_type());

            let body =
                c2.apply(db,
                         SpineEntry::new(ApplyType::Free,
                                         varf.apply(db, SpineEntry::new(m1.to_apply_type(&Sort::Term),
                                                                        c1.apply(db, SpineEntry::new(ApplyType::Free, varx))))));

            let bodyq = body.quote(db, ctx_wip.env_lvl());
            core::Term::Lambda { mode: Mode::Free, name: Symbol::default(),
                                 body: Rc::new(core::Term::Lambda { mode: m1, name: Symbol::default(), body: bodyq })};
       }
    }
}
