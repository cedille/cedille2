
use std::rc::Rc;

use colored::Colorize;
use thiserror::Error;

use crate::common::*;
use crate::lang::syntax;
use crate::kernel::core;
use crate::kernel::value::{Value, ValueEx, LazyValue, EnvEntry, Environment};
use crate::database::Database;

type Span = (usize, usize);

#[derive(Debug, Error)]
pub enum ElabError {
    #[error("errors:\n{errors:?}")]
    Many {
        errors: Vec<anyhow::Error>
    },
    #[error("Terms are inconvertible at {span:?}")]
    Inconvertible { 
        span: Span,
    },
    #[error("Terms are convertible at {span:?} when they should not be")]
    Convertible {
        span: Span,
    },
    #[error("Sort checking failed, expected {expected:?} but have {provided:?} at {span:?}")]
    SortMismatch { 
        span: Span,
        expected: Sort,
        provided: Sort
    },
    #[error("Expected term {span:?}")]
    ExpectedTerm { span: Span },
    #[error("ExpectedFunctionType")]
    ExpectedFunctionType,
    #[error("ExpectedEqualityType")]
    ExpectedEqualityType,
    #[error("ExpectedIntersectionType")]
    ExpectedIntersectionType,
    #[error("ModeMismatch")]
    ModeMismatch,
    #[error("Hole at {span:?}")]
    Hole { span: Span },
    #[error("DefinitionCollision")]
    DefinitionCollision,
    #[error("MissingName")]
    MissingName,
    #[error("Inference failed {span:?}")]
    InferenceFailed { span: Span },
    #[error("UnsupportedProjection")]
    UnsupportedProjection,
}

#[derive(Debug, Clone)]
struct Context {
    env: Environment,
    types: im_rc::Vector<(Symbol, Rc<Value>)>,
    mode: Mode,
    sort: Sort
}

impl Context {
    fn new(sort: Sort) -> Context {
        Context {
            env: Environment::new(),
            types: im_rc::Vector::new(),
            mode: Mode::Free,
            sort
        }
    }

    fn bind(&mut self, mode: ApplyType, name: Symbol, value_type: Rc<Value>) {
        let level = self.env_lvl();
        self.env.push_back(EnvEntry::new(mode, name, LazyValue::computed(Value::variable(level))));
        self.types.push_back((name, value_type));
    }

    fn define(&mut self, mode: ApplyType, name: Symbol, value: LazyValue, value_type: Rc<Value>) {
        self.env.push_back(EnvEntry::new(mode, name, value));
        self.types.push_back((name, value_type));
    }

    fn env(&self) -> Environment { self.env.clone() }

    fn env_lvl(&self) -> Level { self.env.len().into() }
}

pub fn elaborate(db: &mut Database, module: &syntax::Module) -> anyhow::Result<()> {
    let mut errors = vec![];
    module.header_imports.iter().map(|import| db.load_import(import))
        .collect::<Result<Vec<_>, _>>()?;

    for decl in module.decls.iter() {
        match elaborate_decl(db, &module.params, decl) {
            Ok(_) =>  { },
            Err(error) => errors.push(error)
        }
    }

    if errors.is_empty() { Ok(()) }
    else { Err(anyhow::Error::new(ElabError::Many { errors })) }
}

fn elaborate_decl(db: &mut Database, params: &[syntax::Parameter], decl: &syntax::Decl) -> anyhow::Result<()> {
    fn elaborate_decl_helper(sort: Sort, db: &mut Database, params: &[syntax::Parameter], def: &syntax::DefineTerm) -> anyhow::Result<()> {
        if db.lookup_type(&Id::from(def.name)).is_some() {
            Err(anyhow::Error::new(ElabError::DefinitionCollision))
        } else {
            let result = elaborate_define_term(sort, db, params, def);
            if let Ok(ref elabed) = result {
                log::info!("\n{}\n{}\n{}", def.as_str(db.text()), "elaborated to".green(), elabed);
            }
            match result {
                Ok(decl) => db.insert_decl(decl),
                e => e.map(|_| ()),
            }.map_err(anyhow::Error::new)
        }
    }
    match decl {
        syntax::Decl::Type(ty) => elaborate_decl_helper(Sort::Type, db, params, ty),
        syntax::Decl::Term(term) => elaborate_decl_helper(Sort::Term, db, params, term),
        syntax::Decl::Import(import) => db.load_import(import),
        syntax::Decl::Kind(_) => todo!(),
        syntax::Decl::Datatype(_) => todo!(),
    }
}

fn elaborate_define_term(sort: Sort, db: &Database, _params: &[syntax::Parameter], def: &syntax::DefineTerm) -> Result<core::Decl, ElabError> {
    if def.body.sort() != sort {
        Err(ElabError::SortMismatch { span: def.body.span(), expected: sort, provided: def.body.sort() })
    } else if let Some(anno) = &def.anno {
        let ctx = Context::new(sort);
        let anno_elaborated = check(db, ctx.clone(), anno, Value::classifier(anno.sort()))?;
        let anno_value = Value::eval(db, ctx.env(), anno_elaborated.clone());
        let body = check(db, ctx, &def.body, anno_value)?;
        Ok(core::Decl { 
            name: def.name,
            ty: anno_elaborated,
            body
        })
    } else {
        let ctx = Context::new(sort);
        let (body, inferred) = infer(db, ctx.clone(), &def.body)?;
        Ok(core::Decl {
            name: def.name,
            ty: Rc::new(inferred.quote(db, ctx.env_lvl())),
            body
        })
    }
}

fn check(db: &Database, mut ctx: Context, term: &syntax::Term, ty: Rc<Value>) -> Result<Rc<core::Term>, ElabError> {
    let ty = Value::unfold_to_head(db, ty);
    log::debug!("\n{} {} {}", term.as_str(db.text()), "<=".bright_blue(), ty);
    match (term, ty.as_ref()) {
        (syntax::Term::Lambda { mode
            , sort
            , var
            , anno
            , body
            , .. },
            Value::Pi { mode:type_mode, domain, closure, .. }) =>
        {
            if *sort == Sort::Term && mode != type_mode { return Err(ElabError::ModeMismatch) }
            let name = var.unwrap_or_default();
            if let Some(anno) = anno {
                let span = anno.span();
                let anno = check(db, ctx.clone(), anno, Value::classifier(anno.sort()))?;
                let anno = Value::eval(db, ctx.env(), anno);
                convertible(db, ctx.clone(), span, &anno, domain)?;
            }
            let value = LazyValue::computed(Value::variable(ctx.env_lvl()));
            ctx.bind(mode.to_apply_type(sort), name, domain.clone());
            let body_type = closure.apply(db, EnvEntry::new(mode.to_apply_type(sort), name, value));
            let elaborated_body = check(db, ctx, body, body_type)?;
            Ok(Rc::new(core::Term::Lambda { mode:*mode, name, body: elaborated_body }))
        }

        (syntax::Term::Let { mode, sort, def, body, .. }, _) =>
        {
            let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
                let anno_elabed = check(db, ctx.clone(), anno, Value::star())?;
                let anno_value = Value::eval(db, ctx.env(), anno_elabed.clone());
                (anno_elabed, anno_value)
            } else { infer(db, ctx.clone(), &def.body)? };
            let def_body_elabed = check(db, ctx.clone(), &def.body, anno_value.clone())?;
            let def_body_value = LazyValue::new(ctx.env(), def_body_elabed.clone());
            ctx.define(mode.to_apply_type(sort), def.name, def_body_value, anno_value);
            let body_elabed = check(db, ctx, body, ty)?;
            let result_let = Rc::new(core::Term::Let { 
                mode: *mode,
                name: def.name,
                let_body: def_body_elabed,
                body: body_elabed
            });
            let result = core::Term::Annotate { 
                anno: anno_elabed,
                body: result_let
            };
            Ok(Rc::new(result))
        }

        (syntax::Term::Intersect { span, first, second },
            Value::IntersectType { name, first:type1, second:type2 }) =>
        {
            let first_elabed = check(db, ctx.clone(), first, type1.clone())?;
            let first_value = Value::eval(db, ctx.env(), first_elabed.clone());
            let closure_arg = EnvEntry::new(ApplyType::Free, *name, LazyValue::computed(first_value.clone()));
            let type2 = type2.apply(db, closure_arg);
            let second_elabed = check(db, ctx.clone(), second, type2)?;
            let second_value = Value::eval(db, ctx.env(), second_elabed.clone());
            convertible(db, ctx, *span, &first_value, &second_value)?;
            Ok(Rc::new(core::Term::Intersect {
                first: first_elabed,
                second: second_elabed
            }))
        }

        (syntax::Term::Reflexivity { span, erasure, .. },
            Value::Equality { left, right }) =>
        {
            let erasure_elabed = if let Some(t) = erasure { erase(db, ctx.clone(), t)? }
                else { Rc::new(core::Term::id()) };
            convertible(db, ctx, *span, left, right)?;
            Ok(Rc::new(core::Term::Refl { erasure: erasure_elabed }))
        }

        (syntax::Term::Separate { span, equation, .. }, _) =>
        {
            let (equation_elabed, equality) = infer(db, ctx.clone(), equation)?;
            match equality.as_ref() {
                Value::Equality { left, right } => {
                    if convertible(db, ctx, *span, left, right).is_ok() {
                        Err(ElabError::Convertible { span:*span })
                    } else {
                        Ok(Rc::new(core::Term::Separate { equation: equation_elabed }))
                    }
                },
                _ => Err(ElabError::ExpectedEqualityType)
            }
        }

        (syntax::Term::Rewrite { .. },
            _) =>
        {
            todo!()
        }

        (syntax::Term::Cast { equation, input, erasure, ..}, _) =>
        {
            let input_elabed = check(db, ctx.clone(), input, ty)?;
            let input_value = Value::eval(db, ctx.env(), input_elabed.clone());
            let erasure_elabed = erase(db, ctx.clone(), erasure)?;
            let erasure_value = Value::eval(db, ctx.env(), erasure_elabed.clone());
            let equality_type = Value::equality(input_value, erasure_value);
            let equation_elabed = check(db, ctx, equation, equality_type)?;
            Ok(Rc::new(core::Term::Cast { 
                equation: equation_elabed,
                input: input_elabed,
                erasure: erasure_elabed
            }))
        }

        (syntax::Term::Hole { span, .. }, _) => {
            Err(ElabError::Hole { span:*span })
        }

        // change direction
        _ => {
            let (result, inferred_type) = infer(db, ctx.clone(), term)?;
            convertible(db, ctx, term.span(), &ty, &inferred_type)?;
            Ok(result)
        }
    }
}

fn infer(db: &Database, mut ctx: Context, term: &syntax::Term) -> Result<(Rc<core::Term>, Rc<Value>), ElabError> {
    let result = match term {
        syntax::Term::Pi { mode
            , sort
            , var
            , domain
            , body
            , .. } =>
        {
            let (mode, name) = (*mode, var.unwrap_or_default());
            let domain_elabed = check(db, ctx.clone(), domain, Value::classifier(domain.sort()))?;
            let domain_value = Value::eval(db, ctx.env(), domain_elabed.clone());
            ctx.bind(ApplyType::Free, name, domain_value);
            let body_elabed = check(db, ctx, body, Value::classifier(body.sort()))?;
            let result = Rc::new(core::Term::Pi { 
                mode, 
                name,
                domain: domain_elabed,
                body: body_elabed
            });
            Ok((result, Value::classifier(*sort)))
        }

        syntax::Term::IntersectType { var, first, second, .. } => {
            let first_elabed = check(db, ctx.clone(), first, Value::star())?;
            let first_value = Value::eval(db, ctx.env(), first_elabed.clone());
            let name = var.unwrap_or_default();
            ctx.bind(ApplyType::Free, name, first_value);
            let second_elabed = check(db, ctx, second, Value::star())?;
            let result = Rc::new(core::Term::IntersectType {
                name,
                first: first_elabed,
                second: second_elabed
            });
            Ok((result, Value::star()))
        }

        syntax::Term::Equality { left, right, .. } => {
            let left_elabed = erase(db, ctx.clone(), left)?;
            let right_elabed = erase(db, ctx.clone(), right)?;
            let result = Rc::new(core::Term::Equality {
                left: left_elabed,
                right: right_elabed
            });
            Ok((result, Value::star()))
        }

        syntax::Term::Let { mode, sort, def, body, .. } => {
            let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
                let anno_elabed = check(db, ctx.clone(), anno, Value::star())?;
                let anno_value = Value::eval(db, ctx.env(), anno_elabed.clone());
                (anno_elabed, anno_value)
            } else { infer(db, ctx.clone(), &def.body)? };
            let def_body_elabed = check(db, ctx.clone(), &def.body, anno_value.clone())?;
            let def_body_value = LazyValue::new(ctx.env(), def_body_elabed.clone());
            ctx.define(mode.to_apply_type(sort), def.name, def_body_value, anno_value);
            let (body_elabed, type_value) = infer(db, ctx.clone(), body)?;
            let result_let = Rc::new(core::Term::Let { 
                mode: *mode,
                name: def.name,
                let_body: def_body_elabed,
                body: body_elabed
            });
            let result = Rc::new(core::Term::Annotate { 
                anno: anno_elabed,
                body: result_let
            });
            Ok((result, Value::unfold_to_head(db, type_value)))
        }

        syntax::Term::Variable { id, .. } => {
            let (var_type, level) = lookup_type(db, &ctx, id)?;
            let var_type = Value::unfold_to_head(db, var_type);
            if let Some(level) = level {
                let index = level.to_index(ctx.env.len());
                Ok((Rc::new(core::Term::Bound { index }), var_type))
            } else {
                Ok((Rc::new(core::Term::Free { id:id.clone() }), var_type))
            }
        }

        syntax::Term::Apply { mode, fun, arg, .. } => {
            let (fun_elabed, fun_type) = infer(db, ctx.clone(), fun)?;
            match fun_type.as_ref() {
                Value::Pi { mode:type_mode, name, domain, closure } => {
                    if mode != type_mode { return Err(ElabError::ModeMismatch); }
                    let arg_elabed = check(db, ctx.clone(), arg, domain.clone())?;
                    let arg_value = LazyValue::new(ctx.env(), arg_elabed.clone());
                    let closure_arg = EnvEntry::new(mode.to_apply_type(&arg.sort()), *name, arg_value);
                    let result_type = closure.apply(db, closure_arg);
                    let result = Rc::new(core::Term::Apply {
                        apply_type: mode.to_apply_type(&arg.sort()),
                        fun: fun_elabed,
                        arg: arg_elabed
                    });
                    Ok((result, Value::unfold_to_head(db, result_type)))
                },
                _ => Err(ElabError::ExpectedFunctionType)
            }
        }

        syntax::Term::Project { variant, body, .. } => {
            let (body_elabed, body_type) = infer(db, ctx.clone(), body)?;
            match body_type.as_ref() {
                Value::IntersectType { name, first, second } => {
                    let first_proj = Rc::new(core::Term::Project { variant:1, body: body_elabed.clone() });
                    let first_value = Value::eval(db, ctx.env(), first_proj.clone());
                    match variant {
                        1 => Ok((first_proj, Value::unfold_to_head(db, first.clone()))),
                        2 => {
                            let second_proj = Rc::new(core::Term::Project { variant:2, body: body_elabed });
                            let closure_arg = EnvEntry::new(ApplyType::Free, *name, LazyValue::computed(first_value));
                            let result_type = Value::unfold_to_head(db, second.apply(db, closure_arg));
                            Ok((second_proj, result_type))
                        }
                        _ => Err(ElabError::UnsupportedProjection)
                    }
                },
                _ => Err(ElabError::ExpectedIntersectionType)
            }
        }

        syntax::Term::Cast { equation, input, erasure, .. } => {
            let (input_elabed, result_type) = infer(db, ctx.clone(), input)?;
            let input_value = Value::eval(db, ctx.env(), input_elabed.clone());
            let erasure_elabed = erase(db, ctx.clone(), erasure)?;
            let erasure_value = Value::eval(db, ctx.env(), erasure_elabed.clone());
            let equality_type = Value::equality(input_value, erasure_value);
            let equation_elabed = check(db, ctx.clone(), equation, equality_type)?;
            let result = Rc::new(core::Term::Cast { 
                equation: equation_elabed,
                input: input_elabed,
                erasure: erasure_elabed
            });
            Ok((result, Value::unfold_to_head(db, result_type)))
        }

        syntax::Term::Star { .. } => Ok((Rc::new(core::Term::Star), Value::super_star())),

        syntax::Term::Hole { span, .. } => {
            Err(ElabError::Hole { span: *span })
        }

        syntax::Term::Annotate { anno, body, .. } => {
            let anno_elabed = check(db, ctx.clone(), anno, Value::star())?;
            let anno_value = Value::eval(db, ctx.env(), anno_elabed.clone());
            let body_elabed = check(db, ctx.clone(), body, anno_value.clone())?;
            let result = Rc::new(core::Term::Annotate {
                anno: anno_elabed,
                body: body_elabed
            });
            Ok((result, Value::unfold_to_head(db, anno_value)))
        }

        _ => Err(ElabError::InferenceFailed { span:term.span() })
    };
    if let Ok((_, ref inferred_type)) = result {
        log::debug!("\n{} {} {}", term.as_str(db.text()), "=>".bright_blue(), inferred_type);
    }
    result
}

fn erase(db: &Database, mut ctx: Context, term: &syntax::Term) -> Result<Rc<core::Term>, ElabError> {
    use syntax::Term;
    match term {
        Term::Lambda { mode, sort, var, body, .. } => {
            let (mode, sort) = (*mode, *sort);
            if mode == Mode::Erased || sort != Sort::Term { erase(db, ctx, body) }
            else {
                let name = var.unwrap_or_default();
                ctx.bind(ApplyType::Free, name, Value::star());
                let body = erase(db, ctx, body)?;
                Ok(Rc::new(core::Term::Lambda { mode, name, body }))
            }
        },
        Term::Let { mode, sort, def, body, .. } => {
            let (mode, sort) = (*mode, *sort);
            if mode == Mode::Erased || sort != Sort::Term { erase(db, ctx, body) }
            else {
                let let_body = erase(db, ctx.clone(), &def.body)?;
                ctx.bind(ApplyType::Free, def.name, Value::star());
                let body = erase(db, ctx, body)?;
                Ok(Rc::new(core::Term::Let { mode, name:def.name, let_body, body }))
            }
        },
        Term::Pi { .. }
        | Term::IntersectType { .. }
        | Term::Equality { .. } => Err(ElabError::ExpectedTerm { span:term.span() }),
        Term::Rewrite { body, .. } => erase(db, ctx, body),
        Term::Annotate { body, .. } => erase(db, ctx, body),
        Term::Project { body, .. } => erase(db, ctx, body),
        Term::Symmetry { .. } => unreachable!(),
        Term::Intersect { first, .. } => erase(db, ctx, first),
        Term::Separate { .. } => Ok(Rc::new(core::Term::id())),
        Term::Reflexivity { erasure, .. } => {
            if let Some(erasure) = erasure { erase(db, ctx, erasure) }
            else { Ok(Rc::new(core::Term::id())) }
        },
        Term::Cast { erasure, .. } => erase(db, ctx, erasure),
        Term::Induct { .. } => todo!(),
        Term::Match { .. } => todo!(),
        Term::Apply { mode, sort, fun, arg, .. } => {
            let (mode, sort) = (*mode, *sort);
            if mode == Mode::Erased || sort != Sort::Term { erase(db, ctx, fun) }
            else {
                let apply_type = ApplyType::Free;
                let fun = erase(db, ctx.clone(), fun)?;
                let arg = erase(db, ctx, arg)?;
                Ok(Rc::new(core::Term::Apply { apply_type, fun, arg }))
            }
        },
        Term::Variable { id, .. } => {
            let (_, level) = lookup_type(db, &ctx, id)?;
            if let Some(level) = level {
                let index = level.to_index(ctx.env.len());
                Ok(Rc::new(core::Term::Bound { index }))
            } else {
                Ok(Rc::new(core::Term::Free { id:id.clone() }))
            }
        },
        Term::Star { .. } => Err(ElabError::ExpectedTerm { span:term.span() }),
        Term::Hole { span, .. } => Err(ElabError::Hole { span:*span }),
    }
}

fn convertible(db: &Database, ctx: Context, span: Span, left: &Rc<Value>, right: &Rc<Value>) -> Result<(), ElabError> {
    if Value::convertible(db, ctx.env_lvl(), left, right) { Ok(()) }
    else {
        log::debug!("\n{} {} {}", left, "=?".bright_blue(), right);
        Err(ElabError::Inconvertible { span })
    }
}

fn lookup_type(db: &Database, ctx: &Context, id: &Id) -> Result<(Rc<Value>, Option<Level>), ElabError> {
    let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
    let toplevel_type = db.lookup_type(id);
    let context_type = has_namespace
        .and(ctx.types.iter().enumerate().find(|(_, (x, _))| *x == id.name))
        .map(|(level, (_, ty))| (ty.clone(), Some(level.into())));
    match (toplevel_type, context_type) {
        (_, Some((v, level))) => Ok((v, level)),
        (Some(v), None) => Ok((v.force(db), None)),
        (None, None) => Err(ElabError::MissingName)
    }
}
