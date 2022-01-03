
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

use colored::Colorize;
use thiserror::Error;

use crate::common::*;
use crate::lang::syntax;
use crate::kernel::core;
use crate::kernel::value;
use crate::kernel::value::{Value, LazyValue, EnvEntry};
use crate::database::Database;

type Span = (usize, usize);

#[derive(Debug, Error)]
pub enum ElabError {
    #[error("errors:\n{errors:?}")]
    Many {
        errors: Vec<ElabError>
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
    #[error("todo")]
    ExpectedFunctionType,
    #[error("todo")]
    ExpectedEqualityType,
    #[error("todo")]
    ExpectedIntersectionType,
    #[error("todo")]
    ModeMismatch,
    #[error("Hole at {span:?}")]
    Hole { span: Span },
    #[error("todo")]
    DefinitionCollision,
    #[error("todo")]
    MissingName,
    #[error("Inference failed {span:?}")]
    InferenceFailed { span: Span },
    #[error("todo")]
    UnsupportedProjection,
}

#[derive(Debug, Clone, Copy)]
pub struct References<'a> {
    module: Symbol,
    db: &'a Database,
    decl_defs: &'a HashMap<Symbol, LazyValue>,
    decl_types: &'a HashMap<Symbol, LazyValue>,
}

impl<'a> References<'a> {
    fn new(module: Symbol
        , db: &'a Database
        , decl_defs: &'a HashMap<Symbol, LazyValue>
        , decl_types: &'a HashMap<Symbol, LazyValue>)
        -> References<'a>
    {
        References { module, db, decl_defs, decl_types }
    }

    pub fn lookup_type(&self, id: &Id) -> Result<value::Handle, ElabError> {
        let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
        let db_type = self.db.lookup_type(self.module, id);
        let decl_type = has_namespace.and(self.decl_types.get(&id.name)).cloned();
        match (db_type, decl_type) {
            (Some(_), Some(_)) => Err(ElabError::DefinitionCollision),
            | (Some(_ty), None) => todo!(),
            | (None, Some(ty)) => Ok(ty.force(*self)),
            (None, None) => Err(ElabError::MissingName)
        }
    }

    pub fn lookup_def(&self, id: &Id) -> Result<value::Handle, ElabError> {
        let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
        let db_def = self.db.lookup_def(self.module, id);
        let decl_def = has_namespace.and(self.decl_defs.get(&id.name)).cloned();
        match (db_def, decl_def) {
            (Some(_), Some(_)) => Err(ElabError::DefinitionCollision),
            | (Some(_ty), None) => todo!(),
            | (None, Some(ty)) => Ok(ty.force(*self)),
            (None, None) => Err(ElabError::MissingName)
        }
    }
}

#[derive(Debug, Clone)]
struct Context<'a> {
    pub refs: References<'a>,
    env: ConsVec<EnvEntry>,
    types: ConsVec<(Symbol, value::Handle)>,
    module: Symbol,
    mode: Mode,
    sort: Sort
}

impl<'a> Context<'a> {
    fn new(sort: Sort, refs: References)
        -> Context
    {
        Context {
            refs,
            env: ConsVec::new(),
            types: ConsVec::new(),
            module: Symbol::default(),
            mode: Mode::Free,
            sort
        }
    }

    fn bind(&mut self, mode: Mode, name: Symbol, value_type: value::Handle) {
        let level = self.env_lvl();
        self.env.push_back(EnvEntry::new(mode, name, LazyValue::computed(Value::var(level))));
        self.types.push_back((name, value_type));
    }

    fn define(&mut self, mode: Mode, name: Symbol, value: LazyValue, value_type: value::Handle) {
        self.env.push_back(EnvEntry::new(mode, name, value));
        self.types.push_back((name, value_type));
    }

    fn env(&self) -> ConsVec<EnvEntry> { self.env.clone() }

    fn env_lvl(&self) -> Level { self.env.len().into() }
}

pub fn elaborate(db: &Database, module: &syntax::Module, module_name: Symbol) -> Result<core::Module, ElabError> {
    let imports = vec![];
    let id = Id { namespace:vec![], name: Symbol::from("") };
    let mut decls = vec![];
    let mut decl_defs = HashMap::new();
    let mut decl_types = HashMap::new();
    let mut errors = vec![];
    
    for decl in module.decls.iter() {
        let refs = References::new(module_name, db, &decl_defs, &decl_types);
        match elaborate_decl(refs, &module.params, decl) {
            Ok(elaborated_decl) =>  {
                let lazy_def = LazyValue::new(ConsVec::new(), elaborated_decl.body.clone());
                let lazy_type = LazyValue::new(ConsVec::new(), elaborated_decl.ty.clone());
                decl_defs.insert(elaborated_decl.name, lazy_def);
                decl_types.insert(elaborated_decl.name, lazy_type);
                decls.push(elaborated_decl)
            }
            Err(error) => errors.push(error)
        }
    }

    let result = if errors.is_empty() { Ok(core::Module { imports, id, decls }) }
        else { Err(ElabError::Many { errors }) };
    
    Value::collect();
    result
}

fn elaborate_decl(refs: References, params: &[syntax::Parameter], decl: &syntax::Decl) -> Result<core::Decl, ElabError> {
    match decl {
        syntax::Decl::Type(ty) => {
            elaborate_define_term(Sort::Type, refs, params, ty)
        },
        syntax::Decl::Term(term) => {
            elaborate_define_term(Sort::Term, refs, params, term)
        },
        syntax::Decl::Kind(_) => todo!(),
        syntax::Decl::Datatype(_) => todo!(),
    }
}

fn elaborate_define_term(sort: Sort, refs: References, _params: &[syntax::Parameter], def: &syntax::DefineTerm) -> Result<core::Decl, ElabError> {
    if def.body.sort() != sort {
        Err(ElabError::SortMismatch { span: def.body.span(), expected: sort, provided: def.body.sort() })
    } else if let Some(anno) = &def.anno {
        let ctx = Context::new(sort, refs);
        let anno_elaborated = check(ctx.clone(), anno, Value::classifier(anno.sort()))?;
        let anno_value = Value::eval(ctx.refs, ctx.env(), anno_elaborated.clone());
        let body = check(ctx, &def.body, anno_value)?;
        Ok(core::Decl { 
            name: def.name,
            ty: anno_elaborated,
            body
        })
    } else {
        let ctx = Context::new(sort, refs);
        let (body, inferred) = infer(ctx.clone(), &def.body)?;
        Ok(core::Decl {
            name: def.name,
            ty: Rc::new(inferred.deref().quote(ctx.refs, ctx.env_lvl())),
            body
        })
    }
}

fn check(mut ctx: Context, term: &syntax::Term, ty: value::Handle) -> Result<Rc<core::Term>, ElabError> {
    let ty = Value::unfold_to_head(ctx.refs, ty);
    /* eprintln!("{} {:#?} \n{} {:#?}", "check:".red(), term, "against:".red(), ty.deref()); */
    match (term, ty.deref().as_ref()) {
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
                let anno = check(ctx.clone(), anno, Value::classifier(anno.sort()))?;
                let anno = Value::eval(ctx.refs, ctx.env(), anno);
                convertible(ctx.clone(), span, anno, *domain)?;
            }
            let value = LazyValue::computed(Value::var(ctx.env_lvl()));
            ctx.bind(*mode, name, *domain);
            let body_type = closure.apply(ctx.refs, EnvEntry::new(*mode, name, value));
            let elaborated_body = check(ctx, body, body_type)?;
            Ok(Rc::new(core::Term::Lambda { mode:*mode, name, body: elaborated_body }))
        }

        (syntax::Term::Let { mode, def, body, .. }, _) =>
        {
            let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
                let anno_elabed = check(ctx.clone(), anno, Value::star())?;
                let anno_value = Value::eval(ctx.refs, ctx.env(), anno_elabed.clone());
                (anno_elabed, anno_value)
            } else { infer(ctx.clone(), &def.body)? };
            let def_body_elabed = check(ctx.clone(), &def.body, anno_value)?;
            let def_body_value = LazyValue::new(ctx.env(), def_body_elabed.clone());
            ctx.define(*mode, def.name, def_body_value, anno_value);
            let body_elabed = check(ctx, body, ty)?;
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
            let first_elabed = check(ctx.clone(), first, *type1)?;
            let first_value = Value::eval(ctx.refs, ctx.env(), first_elabed.clone());
            let closure_arg = EnvEntry::new(Mode::Free, *name, LazyValue::computed(first_value));
            let type2 = type2.apply(ctx.refs, closure_arg);
            let second_elabed = check(ctx.clone(), second, type2)?;
            let second_value = Value::eval(ctx.refs, ctx.env(), second_elabed.clone());
            convertible(ctx, *span, first_value, second_value)?;
            Ok(Rc::new(core::Term::Intersect {
                first: first_elabed,
                second: second_elabed
            }))
        }

        (syntax::Term::Reflexivity { span, erasure, .. },
            Value::Equality { left, right }) =>
        {
            let erasure_elabed = if let Some(t) = erasure { erase(ctx.clone(), t)? }
                else { Rc::new(core::Term::id()) };
            convertible(ctx, *span, *left, *right)?;
            Ok(Rc::new(core::Term::Refl { erasure: erasure_elabed }))
        }

        (syntax::Term::Separate { span, equation, .. }, _) =>
        {
            let (equation_elabed, equality) = infer(ctx.clone(), equation)?;
            match equality.deref().as_ref() {
                Value::Equality { left, right } => {
                    if convertible(ctx, *span, *left, *right).is_ok() {
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
            let input_elabed = check(ctx.clone(), input, ty)?;
            let input_value = Value::eval(ctx.refs, ctx.env(), input_elabed.clone());
            let erasure_elabed = erase(ctx.clone(), erasure)?;
            let erasure_value = Value::eval(ctx.refs, ctx.env(), erasure_elabed.clone());
            let equality_type = Value::equality(input_value, erasure_value);
            let equation_elabed = check(ctx, equation, equality_type)?;
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
            let (result, inferred_type) = infer(ctx.clone(), term)?;
            convertible(ctx, term.span(), ty, inferred_type)?;
            Ok(result)
        }
    }
}

fn infer(mut ctx: Context, term: &syntax::Term) -> Result<(Rc<core::Term>, value::Handle), ElabError> {
    /* eprintln!("{} {:#?}", "infer:".red(), term); */
    let result = match term {
        syntax::Term::Pi { mode
            , sort
            , var
            , domain
            , body
            , .. } =>
        {
            let (mode, name) = (*mode, var.unwrap_or_default());
            let domain_elabed = check(ctx.clone(), domain, Value::classifier(domain.sort()))?;
            let domain_value = Value::eval(ctx.refs, ctx.env(), domain_elabed.clone());
            ctx.bind(mode, name, domain_value);
            let body_elabed = check(ctx, body, Value::classifier(body.sort()))?;
            let result = Rc::new(core::Term::Pi { 
                mode, 
                name,
                domain: domain_elabed,
                body: body_elabed
            });
            Ok((result, Value::classifier(*sort)))
        }

        syntax::Term::IntersectType { var, first, second, .. } => {
            let first_elabed = check(ctx.clone(), first, Value::star())?;
            let first_value = Value::eval(ctx.refs, ctx.env(), first_elabed.clone());
            let name = var.unwrap_or_default();
            ctx.bind(Mode::Free, name, first_value);
            let second_elabed = check(ctx, second, Value::star())?;
            let result = Rc::new(core::Term::IntersectType {
                name,
                first: first_elabed,
                second: second_elabed
            });
            Ok((result, Value::star()))
        }

        syntax::Term::Equality { left, right, .. } => {
            let left_elabed = erase(ctx.clone(), left)?;
            let right_elabed = erase(ctx.clone(), right)?;
            let result = Rc::new(core::Term::Equality {
                left: left_elabed,
                right: right_elabed
            });
            Ok((result, Value::star()))
        }

        syntax::Term::Let { mode, def, body, .. } => {
            let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
                let anno_elabed = check(ctx.clone(), anno, Value::star())?;
                let anno_value = Value::eval(ctx.refs, ctx.env(), anno_elabed.clone());
                (anno_elabed, anno_value)
            } else { infer(ctx.clone(), &def.body)? };
            let def_body_elabed = check(ctx.clone(), &def.body, anno_value)?;
            let def_body_value = LazyValue::new(ctx.env(), def_body_elabed.clone());
            ctx.define(*mode, def.name, def_body_value, anno_value);
            let (body_elabed, type_value) = infer(ctx.clone(), body)?;
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
            Ok((result, Value::unfold_to_head(ctx.refs, type_value)))
        }

        syntax::Term::Variable { id, .. } => {
            let env_level = ctx.env_lvl();
            let (var_type, level) = lookup_type(ctx.clone(), id)?;
            let var_type = Value::unfold_to_head(ctx.refs, var_type);
            if let Some(level) = level {
                let index = level.to_index(env_level);
                Ok((Rc::new(core::Term::Bound { index }), var_type))
            } else {
                Ok((Rc::new(core::Term::Free { id:id.clone() }), var_type))
            }
        }

        syntax::Term::Apply { mode, fun, arg, .. } => {
            let (fun_elabed, fun_type) = infer(ctx.clone(), fun)?;
            match fun_type.deref().as_ref() {
                Value::Pi { mode:type_mode, name, domain, closure } => {
                    if mode != type_mode { return Err(ElabError::ModeMismatch); }
                    let arg_elabed = check(ctx.clone(), arg, *domain)?;
                    let arg_value = LazyValue::new(ctx.env(), arg_elabed.clone());
                    let closure_arg = EnvEntry::new(*mode, *name, arg_value);
                    let result_type = closure.apply(ctx.refs, closure_arg);
                    let result = Rc::new(core::Term::Apply {
                        mode:*mode,
                        fun: fun_elabed,
                        arg: arg_elabed
                    });
                    Ok((result, Value::unfold_to_head(ctx.refs, result_type)))
                },
                _ => Err(ElabError::ExpectedFunctionType)
            }
        }

        syntax::Term::Project { variant, body, .. } => {
            let (body_elabed, body_type) = infer(ctx.clone(), body)?;
            match body_type.deref().as_ref() {
                Value::IntersectType { name, first, second } => {
                    let first_proj = Rc::new(core::Term::Project { variant:1, body: body_elabed.clone() });
                    let first_value = Value::eval(ctx.refs, ctx.env(), first_proj.clone());
                    match variant {
                        1 => Ok((first_proj, Value::unfold_to_head(ctx.refs, *first))),
                        2 => {
                            let second_proj = Rc::new(core::Term::Project { variant:2, body: body_elabed });
                            let closure_arg = EnvEntry::new(Mode::Free, *name, LazyValue::computed(first_value));
                            let result_type = Value::unfold_to_head(ctx.refs, second.apply(ctx.refs, closure_arg));
                            Ok((second_proj, result_type))
                        }
                        _ => Err(ElabError::UnsupportedProjection)
                    }
                },
                _ => Err(ElabError::ExpectedIntersectionType)
            }
        }

        syntax::Term::Cast { equation, input, erasure, .. } => {
            let (input_elabed, result_type) = infer(ctx.clone(), input)?;
            let input_value = Value::eval(ctx.refs, ctx.env(), input_elabed.clone());
            let erasure_elabed = erase(ctx.clone(), erasure)?;
            let erasure_value = Value::eval(ctx.refs, ctx.env(), erasure_elabed.clone());
            let equality_type = Value::equality(input_value, erasure_value);
            let equation_elabed = check(ctx.clone(), equation, equality_type)?;
            let result = Rc::new(core::Term::Cast { 
                equation: equation_elabed,
                input: input_elabed,
                erasure: erasure_elabed
            });
            Ok((result, Value::unfold_to_head(ctx.refs, result_type)))
        }

        syntax::Term::Star { .. } => Ok((Rc::new(core::Term::Star), Value::superstar())),

        syntax::Term::Hole { span, .. } => {
            Err(ElabError::Hole { span: *span })
        }

        syntax::Term::Annotate { anno, body, .. } => {
            let anno_elabed = check(ctx.clone(), anno, Value::star())?;
            let anno_value = Value::eval(ctx.refs, ctx.env(), anno_elabed.clone());
            let body_elabed = check(ctx.clone(), body, anno_value)?;
            let result = Rc::new(core::Term::Annotate {
                anno: anno_elabed,
                body: body_elabed
            });
            Ok((result, Value::unfold_to_head(ctx.refs, anno_value)))
        }

        _ => Err(ElabError::InferenceFailed { span:term.span() })
    };
    if let Ok((_, ty)) = result {
        /* eprintln!("{} {:#?}", "inferred:".red(), ty.deref()); */
    }
    result
}

fn erase(mut ctx: Context, term: &syntax::Term) -> Result<Rc<core::Term>, ElabError> {
    use syntax::Term;
    match term {
        Term::Lambda { mode, sort, var, body, .. } => {
            let (mode, sort) = (*mode, *sort);
            if mode == Mode::Erased || sort != Sort::Term { erase(ctx, body) }
            else {
                let name = var.unwrap_or_default();
                ctx.bind(mode, name, Value::star());
                let body = erase(ctx, body)?;
                Ok(Rc::new(core::Term::Lambda { mode, name, body }))
            }
        },
        Term::Let { mode, sort, def, body, .. } => {
            let (mode, sort) = (*mode, *sort);
            if mode == Mode::Erased || sort != Sort::Term { erase(ctx, body) }
            else {
                let let_body = erase(ctx.clone(), &def.body)?;
                ctx.bind(mode, def.name, Value::star());
                let body = erase(ctx, body)?;
                Ok(Rc::new(core::Term::Let { mode, name:def.name, let_body, body }))
            }
        },
        Term::Pi { .. }
        | Term::IntersectType { .. }
        | Term::Equality { .. } => Err(ElabError::ExpectedTerm { span:term.span() }),
        Term::Rewrite { body, .. } => erase(ctx, body),
        Term::Annotate { body, .. } => erase(ctx, body),
        Term::Project { body, .. } => erase(ctx, body),
        Term::Symmetry { .. } => unreachable!(),
        Term::Intersect { first, .. } => erase(ctx, first),
        Term::Separate { .. } => Ok(Rc::new(core::Term::id())),
        Term::Reflexivity { erasure, .. } => {
            if let Some(erasure) = erasure { erase(ctx, erasure) }
            else { Ok(Rc::new(core::Term::id())) }
        },
        Term::Cast { erasure, .. } => erase(ctx, erasure),
        Term::Induct { .. } => todo!(),
        Term::Match { .. } => todo!(),
        Term::Apply { mode, sort, fun, arg, .. } => {
            let (mode, sort) = (*mode, *sort);
            if mode == Mode::Erased || sort != Sort::Term { erase(ctx, fun) }
            else {
                let fun = erase(ctx.clone(), fun)?;
                let arg = erase(ctx, arg)?;
                Ok(Rc::new(core::Term::Apply { mode, fun, arg }))
            }
        },
        Term::Variable { id, .. } => {
            let (_, level) = lookup_type(ctx.clone(), id)?;
            if let Some(level) = level {
                let index = level.to_index(ctx.env_lvl());
                Ok(Rc::new(core::Term::Bound { index }))
            } else {
                Ok(Rc::new(core::Term::Free { id:id.clone() }))
            }
        },
        Term::Star { .. } => Err(ElabError::ExpectedTerm { span:term.span() }),
        Term::Hole { span, .. } => Err(ElabError::Hole { span:*span }),
    }
}

fn convertible(ctx: Context, span: Span, left: value::Handle, right: value::Handle) -> Result<(), ElabError> {
    /* eprintln!("{} {:#?} =? {:#?}", "convertible?".red(), left.deref(), right.deref()); */
    if Value::convertible(ctx.refs, ctx.env_lvl(), left, right) { Ok(()) }
    else { Err(ElabError::Inconvertible { span }) }
}

fn lookup_type(ctx: Context, id: &Id) -> Result<(value::Handle, Option<Level>), ElabError> {
    let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
    let toplevel_type = ctx.refs.lookup_type(id);
    let context_type = has_namespace
        .and(ctx.types.iter().enumerate().find(|(_, (x, _))| *x == id.name))
        .map(|(level, (_, ty))| (*ty, Some(level.into())));
    match (toplevel_type, context_type) {
        (_, Some((v, level))) => Ok((v, level)),
        (Ok(v), None) => Ok((v, None)),
        (Err(e), None) => Err(e)
    }
}
