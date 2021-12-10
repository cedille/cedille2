
use std::collections::HashSet;

use internment::Intern;
use thiserror::Error;

use crate::lang::syntax;
use crate::database::Database;

type Span = (usize, usize);

#[derive(Debug, Error)]
pub enum ResolverError {
    #[error("Dangling reference {var:?} at {span:?}")]
    DanglingFreeReference { span:Span, var:Intern<String> },
    #[error("Reference {var:?} is defined twice")]
    Redefined { var:Intern<String> }
}

#[derive(Debug, Clone, Copy)]
struct References<'a> {
    db: &'a Database,
    decl_names: &'a HashSet<Intern<String>>
}

pub fn resolve(module: &mut syntax::Module, db: &Database) -> Result<(), ResolverError> {
    let decl_names = fetch_decl_names(module)?;
    let refs = References { db, decl_names:&decl_names };
    resolve_imports(&mut module.imports, refs)?;
    resolve_params(&mut module.params, refs)?;
    resolve_decls(&mut module.decls, refs)?;
    Ok(())
}

fn fetch_decl_names(module: &syntax::Module) -> Result<HashSet<Intern<String>>, ResolverError> {
    use syntax::*;
    let mut result = HashSet::new();
    for decl in module.decls.iter() {
        match decl {
            Decl::Type(DefineTerm { name, .. })
            | Decl::Term(DefineTerm { name, .. })
            | Decl::Kind(DefineKind { name, .. })
            | Decl::Datatype(DefineDatatype { name, .. }) => {
                if result.contains(name) {
                    return Err(ResolverError::Redefined { var:*name })
                }
                result.insert(*name);
            }
        }
    }
    Ok(result)
}

fn resolve_params(params: &mut Vec<syntax::Parameter>, refs: References) -> Result<(), ResolverError> {
    let mut ctx = vec![];
    for p in params {
        resolve_term(&mut p.body, &mut ctx, refs)?;
        ctx.push(p.name);
    }
    Ok(())
}

fn resolve_imports(imports: &mut Vec<syntax::Import>, refs: References) -> Result<(), ResolverError> {
    for import in imports.iter_mut() {
        for (_, t) in import.args.iter_mut() {
            resolve_term(t, &mut vec![], refs)?;
        }
    }
    Ok(())
}

fn resolve_decls(decls: &mut Vec<syntax::Decl>, refs: References) -> Result<(), ResolverError> {
    use syntax::Decl::*;
    for decl in decls.iter_mut() {
        match decl {
            Type(def) | Term(def) => resolve_define_term(def, refs)?,
            Kind(def) => todo!(),
            Datatype(def) => todo!()
        }
    }
    Ok(())
}

fn resolve_define_term(def: &mut syntax::DefineTerm, refs: References) -> Result<(), ResolverError> {
    if let Some(anno) = &mut def.anno {
        resolve_term(anno, &mut vec![], refs)?;
    }
    resolve_term(def.body.as_mut(), &mut vec![], refs)?;
    Ok(())
}

fn resolve_term(term: &mut syntax::Term, ctx: &mut Vec<Intern<String>>, refs: References) -> Result<(), ResolverError> {
    use syntax::Term::*;
    match term {
        Lambda { var, anno, body, .. } => {
            if let Some(anno) = anno {
                resolve_term(anno.as_mut(), ctx, refs)?;
            }
            ctx.push(*var);
            resolve_term(body, ctx, refs)?;
        },
        Let { def, body, .. } => {
            resolve_define_term(def, refs)?;
            ctx.push(def.name);
            resolve_term(body, ctx, refs)?;
        },
        Fn { var, domain, body, .. } => {
            resolve_term(domain, ctx, refs)?;
            if let Some(name) = var {
                ctx.push(*name);
            }
            resolve_term(body, ctx, refs)?;
        },
        IntersectType { var, first, second, .. } => {
            resolve_term(first, ctx, refs)?;
            ctx.push(*var);
            resolve_term(second, ctx, refs)?;
        },
        Equality { left, right, .. } => {
            resolve_term(left, ctx, refs)?;
            resolve_term(right, ctx, refs)?;
        },
        Rewrite { equation, guide, body, .. } => {
            resolve_term(equation, ctx, refs)?;
            if let Some(guide) = guide {
                resolve_rewrite_guide(guide, ctx, refs)?;
            }
            resolve_term(body, ctx, refs)?;
        },
        Annotate { anno, body, .. } => {
            resolve_term(anno, ctx, refs)?;
            resolve_term(body, ctx, refs)?;
        },
        Project { body, .. } => resolve_term(body, ctx, refs)?,
        Symmetry { equation, .. } => resolve_term(equation, ctx, refs)?,
        Intersect { first, second, .. } => {
            resolve_term(first, ctx, refs)?;
            resolve_term(second, ctx, refs)?;
        },
        Separate { anno, equation, .. } => {
            if let Some(anno) = anno {
                resolve_term(anno, ctx, refs)?;
            }
            resolve_term(equation, ctx, refs)?;
        },
        Refl { guide, erasure, .. } => {
            if let Some(guide) = guide {
                resolve_term(guide, ctx, refs)?;
            }
            if let Some(erasure) = erasure {
                resolve_term(erasure, ctx, refs)?;
            }
        },
        Cast { equation, input, erasure, .. } => {
            resolve_term(equation, ctx, refs)?;
            resolve_term(input, ctx, refs)?;
            resolve_term(erasure, ctx, refs)?;
        },
        Induct { var, inductee, motive, cases, .. }
            => todo!(),
        Match { guide, matched, motive, cases, .. }
            => todo!(),
        Apply { fun, arg, .. } => {
            resolve_term(fun, ctx, refs)?;
            resolve_term(arg, ctx, refs)?;
        },
        // The parser never constructs the Bound variant
        Bound { .. } => unreachable!(),
        t @ Free { .. } => {
            let (span, sort, id) = match t {
                Free { span, sort, id } => (*span, *sort, id.clone()),
                _ => unreachable!()
            };
            let mut is_free = true;
            // Is this a bound variable?
            if id.namespace.is_empty() {
                if let Some(index) = ctx.iter().position(|x| *x == id.name) {
                    *t = syntax::Term::Bound { span, sort, var:id.name, index };
                    is_free =false;
                }
            }
            // Check that the free reference exists and is unique
            if is_free {
                let imported = refs.db.lookup(&id);
                let internal = refs.decl_names.get(&id.name);
                match (imported, internal) {
                    (Some(_), Some(_)) => return Err(ResolverError::Redefined { var:id.name }),
                    (None, None) => return Err(ResolverError::DanglingFreeReference { span, var:id.name}),
                    _ => { }
                };
            }
        },
        Star { .. } | Hole { .. } => { },
    }
    Ok(())
}

fn resolve_rewrite_guide(
    guide: &mut syntax::RewriteGuide,
    ctx: &mut Vec<Intern<String>>,
    refs: References)
    -> Result<(), ResolverError> 
{
    if let Some(hint) = guide.hint.as_mut() {
        resolve_term(hint, ctx, refs)?;
    }
    ctx.push(guide.name);
    resolve_term(guide.equation.as_mut(), ctx, refs)?;
    Ok(())
}
