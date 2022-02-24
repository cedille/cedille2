
use std::rc::Rc;
use std::sync::Arc;
use std::time;

use colored::Colorize;
use thiserror::Error;
use miette::{Diagnostic, SourceSpan};
use unicode_segmentation::UnicodeSegmentation;

use crate::common::*;
use crate::lang::syntax;
use crate::lang::rewriter;
use crate::kernel::core;
use crate::kernel::value::{Value, ValueEx, Closure, LazyValue, EnvEntry, Environment, EnvBound};
use crate::database::Database;
use crate::error::CedilleError;

type Span = (usize, usize);

#[derive(Debug, Error, Diagnostic)]
pub enum ElabError {
    #[error("Inconvertible")]
    #[diagnostic()]
    Inconvertible {
        #[source_code]
        src: Arc<String>,
        #[label("{left} ~= {right}")]
        span: SourceSpan,
        left: String,
        right: String
    },
    #[error("Convertible")]
    #[diagnostic()]
    Convertible {
        span: Span,
    },
    #[error("Open Term")]
    #[diagnostic()]
    OpenTerm {

    },
    #[error("Expected Term")]
    #[diagnostic()]
    ExpectedTerm { span: Span },
    #[error("Expected Function Type")]
    #[diagnostic()]
    ExpectedFunctionType,
    #[error("Expected Equality Type")]
    #[diagnostic()]
    ExpectedEqualityType,
    #[error("Expected Intersection Type")]
    #[diagnostic()]
    ExpectedIntersectionType {
        #[source_code]
        src: Arc<String>,
        #[label("Type must be a intersection but found {inferred_type}")]
        span: SourceSpan,
        inferred_type: String,
    },
    #[error("Mode Mismatch")]
    #[diagnostic()]
    ModeMismatch,
    #[error("Hole")]
    #[diagnostic(
        help("Context at hole: {context}")
    )]
    Hole {
        #[source_code]
        src: Arc<String>,
        #[label("Expected {expected_type}")]
        span: SourceSpan,
        expected_type: String,
        context: String
    },
    #[error("Definition Collision")]
    #[diagnostic()]
    DefinitionCollision,
    #[error("Missing Name")]
    #[diagnostic()]
    MissingName {
        #[source_code]
        source_code: Arc<String>,
        #[label("Identifier undefined")]
        span: SourceSpan
    },
    #[error("Intersection Inconvertible")]
    #[diagnostic()]
    IntersectionInconvertible {
        #[source_code]
        src: Arc<String>,
        #[label("(lhs) Must be convertible with")]
        left: SourceSpan,
        #[label("(rhs) this")]
        right: SourceSpan,
    },
    #[error("Inference Failed")]
    #[diagnostic()]
    InferenceFailed { span: Span },
    #[error("Unsupported Projection")]
    #[diagnostic()]
    UnsupportedProjection,
    #[error("Rewrite Failed")]
    #[diagnostic()]
    RewriteFailed
}

#[derive(Debug, Clone)]
pub struct Context {
    env: Environment,
    env_mask: Vec<EnvBound>,
    names: im_rc::Vector<Symbol>,
    types: im_rc::Vector<Rc<Value>>,
    sorts: im_rc::Vector<Sort>,
    pub module: Symbol
}

impl Context {
    fn new(module: Symbol) -> Context {
        Context {
            env: Environment::new(),
            env_mask: Vec::new(),
            names: im_rc::Vector::new(),
            types: im_rc::Vector::new(),
            sorts: im_rc::Vector::new(),
            module,
        }
    }

    pub fn bind_sort(&self, name: Symbol, sort: Sort) -> Context {
        let mut result = self.clone();
        result.names.push_back(name);
        result.sorts.push_back(sort);
        result
    }

    pub fn bind(&self, db: &Database, name: Symbol, mode: Mode, value_type: Rc<Value>) -> Context {
        let mut result = self.clone();
        let level = self.env_lvl();
        let sort = value_type.sort(db).demote();
        let value = LazyValue::computed(Value::variable(sort, level));
        log::trace!("\n{}\n{} {} {} {} {}", self.env, "bind".bright_blue(), name, value, ":".bright_blue(), value_type);
        result.env.push_back(EnvEntry::new(name, mode, value));
        result.env_mask.push(EnvBound::Bound);
        result.names.push_back(name);
        result.sorts.push_back(sort);
        result.types.push_back(value_type);
        result
    }

    pub fn define(&self, db: &Database, name: Symbol, mode: Mode, value: LazyValue, value_type: Rc<Value>) -> Context {
        let mut result = self.clone();
        log::trace!("\n{}\n{} {} {} {} {}", self.env, "define".bright_blue(), name, value, ":".bright_blue(), value_type);
        result.env.push_back(EnvEntry::new(name, mode, value));
        result.env_mask.push(EnvBound::Defined);
        result.names.push_back(name);
        result.sorts.push_back(value_type.sort(db).demote());
        result.types.push_back(value_type);
        result
    }

    pub fn to_string(&self, db: &Database) -> String {
        let mut result = String::new();
        for i in 0..self.names.len() {
            result.push('\n');
            let type_string = self.types[i].quote(db, self.env_lvl())
                .to_string_with_context(self.names.clone());
            result.push_str(format!("{}: {}", self.names[i], type_string).as_str());
        }
        result
    }

    pub fn env(&self) -> Environment { self.env.clone() }

    pub fn env_mask(&self) -> Vec<EnvBound> { self.env_mask.clone() }

    pub fn env_lvl(&self) -> Level { self.env.len().into() }
}

pub fn elaborate(db: &mut Database, module: Symbol, syntax: &syntax::Module) -> Result<(), CedilleError> {
    let mut errors = vec![];

    for import in syntax.header_imports.iter() {
        db.load_import(module, import)?;
    }

    for decl in syntax.decls.iter() {
        match elaborate_decl(db, module, &syntax.params, decl) {
            Ok(_) =>  { },
            Err(error) => errors.push(error)
        }
    }

    if errors.is_empty() { Ok(()) }
    else { Err(CedilleError::Collection(errors)) }
}

fn elaborate_decl(db: &mut Database, module: Symbol, params: &[syntax::Parameter], decl: &syntax::Decl) -> Result<(), CedilleError> {
    match decl {
        syntax::Decl::Term(def) => {
            if db.lookup_type(module, &Id::from(def.name)).is_some() {
                Err(ElabError::DefinitionCollision.into())
            } else {
                let ctx = Context::new(module);
                let result = elaborate_define_term(db, ctx, params, def);
                if let Ok(ref elabed) = result {
                    log::info!("\n{}\n{}\n{}", def.as_str(db.text_ref(module)), "elaborated to".green(), elabed);
                }
                match result {
                    Ok(decl) => db.insert_decl(module, decl),
                    e => e.map(|_| ()).map_err(|e| e.into()),
                }
            }
        }
        syntax::Decl::Import(import) => db.load_import(module, import),
        syntax::Decl::Kind(_) => todo!(),
        syntax::Decl::Datatype(_) => todo!(),
        syntax::Decl::NormalizeCommand(term) => {
            let (start, end) = term.span();
            let now = time::Instant::now();
            let erased = erase(db, Context::new(module), term)?;
            let value = Value::eval(db, module, Environment::new(), erased);
            let _normal_form = Value::reify(value, db, 0.into(), true);
            log::info!("Normalized {} in {}ms", &db.text(module)[start..end], now.elapsed().as_millis());
            Ok(())
        }
    }
}

fn elaborate_define_term(db: &mut Database, ctx: Context, _params: &[syntax::Parameter], def: &syntax::DefineTerm) -> Result<core::Decl, ElabError> {
    let (name, ty, body) = if let Some(anno) = &def.anno {
        let anno_sort = infer_sort(db, ctx.clone(), anno);
        let anno_elabed = check(db, ctx.clone(), anno, Value::classifier(anno_sort))?;
        let anno_value = Value::eval(db, ctx.module, ctx.env(), anno_elabed.clone());
        let body = check(db, ctx.clone(), &def.body, anno_value)?;
        (def.name, anno_elabed, body)
    } else {
        let (body, inferred) = infer(db, ctx.clone(), &def.body)?;
        let ty = Rc::new(inferred.quote(db, ctx.env_lvl()));
        (def.name, ty, body)
    };
    Ok(core::Decl { name, ty, body })
}

fn check(db: &mut Database, ctx: Context, term: &syntax::Term, ty: Rc<Value>) -> Result<Rc<core::Term>, ElabError> {
    fn check_lambda(db: &mut Database
        , ctx: Context
        , index: usize
        , vars: &[syntax::LambdaVar]
        , body: &syntax::Term
        , ty: Rc<Value>)
        -> Result<Rc<core::Term>, ElabError>
    {
        if let Some(var) = vars.get(index) {
            let ty = Value::unfold_to_head(db, ty);
            match ty.as_ref() {
                Value::Pi { sort:type_sort, mode:type_mode, domain, closure, .. } => {
                    let sort = type_sort.demote();
                    if sort == Sort::Term && var.mode != *type_mode {
                        return Err(ElabError::ModeMismatch)
                    }
                    let name = var.var.unwrap_or_default();
                    if let Some(ref anno) = var.anno {
                        let span = anno.span();
                        let anno_sort = infer_sort(db, ctx.clone(), anno);
                        let anno_elabed = check(db, ctx.clone(), anno, Value::classifier(anno_sort))?;
                        let anno_value = Value::eval(db, ctx.module, ctx.env(), anno_elabed);
                        unify(db, ctx.clone(), span, &anno_value, domain)?;
                    }
                    let value = LazyValue::computed(Value::variable(domain.sort(db), ctx.env_lvl()));
                    let ctx = ctx.bind(db, name, *type_mode, domain.clone());
                    let body_type = closure.eval(db, EnvEntry::new(name, var.mode, value));
                    let body_elabed = check_lambda(db, ctx, index + 1, vars, body, body_type)?;
                    Ok(Rc::new(core::Term::Lambda {
                        sort,
                        domain_sort: domain.sort(db).demote(),
                        mode: var.mode,
                        name,
                        body: body_elabed
                    }))
                }
                _ => Err(ElabError::ExpectedFunctionType)
            }
        } else { check(db, ctx, body, ty) }
    }

    let ty = Value::unfold_to_head(db, ty);
    log::trace!("\n{}\n  {}\n{} {}", ctx.env(), term.as_str(db.text_ref(ctx.module)), "<=".bright_blue(), ty);
    match (term, ty.as_ref()) {
        (syntax::Term::Lambda { vars, body, .. }, _) =>
            check_lambda(db, ctx, 0, vars, body, ty),

        (syntax::Term::Let { mode, def, body, .. }, _) =>
        {
            let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
                let anno_elabed = check(db, ctx.clone(), anno, Value::star())?;
                let anno_value = Value::eval(db, ctx.module, ctx.env(), anno_elabed.clone());
                (anno_elabed, anno_value)
            } else { infer(db, ctx.clone(), &def.body)? };
            let def_body_elabed = check(db, ctx.clone(), &def.body, anno_value.clone())?;
            let def_body_value = LazyValue::new(ctx.module, ctx.env(), def_body_elabed.clone());
            let ctx = ctx.define(db, def.name, *mode, def_body_value, anno_value);
            let body_elabed = check(db, ctx, body, ty)?;
            let result_let = Rc::new(core::Term::Let {
                sort: body_elabed.sort(),
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
            let first_value = Value::eval(db, ctx.module, ctx.env(), first_elabed.clone());
            let closure_arg = EnvEntry::new(*name, Mode::Free, LazyValue::computed(first_value.clone()));
            let type2 = type2.eval(db, closure_arg);
            let second_elabed = check(db, ctx.clone(), second, type2)?;
            let second_value = Value::eval(db, ctx.module, ctx.env(), second_elabed.clone());
            unify(db, ctx.clone(), *span, &first_value, &second_value)
                .map_err(|_| ElabError::IntersectionInconvertible {
                        src: db.text(ctx.module),
                        left: source_span(db, ctx.module, first.span()),
                        right: source_span(db, ctx.module, second.span())
                    })?;
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
            unify(db, ctx, *span, left, right)?;
            Ok(Rc::new(core::Term::Refl { erasure: erasure_elabed }))
        }

        (syntax::Term::Separate { span, equation, .. }, _) =>
        {
            let (equation_elabed, equality) = infer(db, ctx.clone(), equation)?;
            let equality = Value::unfold_to_head(db, equality);
            match equality.as_ref() {
                Value::Equality { left, right } => {
                    if unify(db, ctx, *span, left, right).is_ok() {
                        Err(ElabError::Convertible { span:*span })
                    } else if !left.is_closed(db) || !right.is_closed(db) {
                        Err(ElabError::OpenTerm { })
                    } else {
                        Ok(Rc::new(core::Term::Separate { equation: equation_elabed }))
                    }
                },
                _ => Err(ElabError::ExpectedEqualityType)
            }
        }

        (syntax::Term::Rewrite { span, equation, guide, body, occurrence, .. },
            _) =>
        {
            let (equation_elabed, equality) = infer(db, ctx.clone(), equation)?;
            let equality = Value::unfold_to_head(db, equality);
            match equality.as_ref() {
                Value::Equality { left, right } => {
                    let guide_name = guide.as_ref().map(|g| g.name).unwrap_or_default();
                    let guide_ctx = ctx.bind(db, guide_name, Mode::Free, Value::top_type());
                    let guide_ty_elabed = if let Some(guide) = guide {
                        check(db, guide_ctx, &guide.ty, Value::star())?
                    } else {
                        rewriter::match_term(db, guide_ctx, *occurrence, left, &ty)?
                    };
                    let guide_ty_closure = Closure::new(ctx.module, ctx.env(), guide_ty_elabed.clone());

                    unify(db
                        , ctx.clone()
                        , *span
                        , &guide_ty_closure.eval(db, EnvEntry::new(guide_name, Mode::Free, left))
                        , &ty)?;

                    let body_elabed = check(db
                        , ctx.clone()
                        , body
                        , guide_ty_closure.eval(db, EnvEntry::new(guide_name, Mode::Free, right)))?;

                    Ok(Rc::new(core::Term::Rewrite {
                        equation: equation_elabed,
                        guide: core::RewriteGuide {
                            name: guide_name,
                            hint: Rc::new(right.quote(db, ctx.env_lvl())),
                            ty: guide_ty_elabed
                        },
                        body: body_elabed
                    }))
                }
                _ => Err(ElabError::ExpectedEqualityType)
            }
        }

        (syntax::Term::Cast { equation, input, erasure, ..}, _) =>
        {
            let input_elabed = check(db, ctx.clone(), input, ty)?;
            let input_value = Value::eval(db, ctx.module, ctx.env(), input_elabed.clone());
            let erasure_elabed = erase(db, ctx.clone(), erasure)?;
            let erasure_value = Value::eval(db, ctx.module, ctx.env(), erasure_elabed.clone());
            let equality_type = Value::equality(input_value, erasure_value);
            let equation_elabed = check(db, ctx, equation, equality_type)?;
            Ok(Rc::new(core::Term::Cast { 
                equation: equation_elabed,
                input: input_elabed,
                erasure: erasure_elabed
            }))
        }

        (syntax::Term::Hole { span, .. }, _) => {
            Err(ElabError::Hole {
                src: db.text(ctx.module),
                span: source_span(db, ctx.module, *span),
                expected_type: ty.quote(db, ctx.env_lvl())
                    .to_string_with_context(ctx.names.clone()),
                context: ctx.to_string(db)
            })
        }

        (syntax::Term::Omission { .. }, _) => Ok(Rc::new(fresh_meta(db, ctx))),

        // change direction
        _ => {
            let (result, inferred_type) = infer(db, ctx.clone(), term)?;
            unify(db, ctx, term.span(), &ty, &inferred_type)?;
            Ok(result)
        }
    }
}

fn infer(db: &mut Database, ctx: Context, term: &syntax::Term) -> Result<(Rc<core::Term>, Rc<Value>), ElabError> {
    let module = ctx.module;
    let sort = infer_sort(db, ctx.clone(), term);
    let result = match term {
        syntax::Term::Pi { mode
            , var
            , domain
            , body
            , .. } =>
        {
            let (mode, name) = (*mode, var.unwrap_or_default());
            let domain_sort = infer_sort(db, ctx.clone(), domain);
            let domain_elabed = check(db, ctx.clone(), domain, Value::classifier(domain_sort))?;
            let domain_value = Value::eval(db, module, ctx.env(), domain_elabed.clone());
            let ctx = ctx.bind(db, name, mode, domain_value);
            let body_elabed = check(db, ctx, body, Value::classifier(sort))?;
            let result = Rc::new(core::Term::Pi { 
                sort,
                mode,
                name,
                domain: domain_elabed,
                body: body_elabed
            });
            Ok((result, Value::classifier(sort)))
        }

        syntax::Term::IntersectType { var, first, second, .. } => {
            let first_elabed = check(db, ctx.clone(), first, Value::star())?;
            let first_value = Value::eval(db, module, ctx.env(), first_elabed.clone());
            let name = var.unwrap_or_default();
            let ctx = ctx.bind(db, name, Mode::Free, first_value);
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

        syntax::Term::Symmetry { equation, .. } => {
            let (equation_elabed, eq_ty) = infer(db, ctx.clone(), equation)?;
            match eq_ty.as_ref() {
                Value::Equality { left, right } => {
                    let result_ty = Rc::new(Value::Equality { left:right.clone(), right:left.clone() });
                    Ok((equation_elabed, result_ty))
                }
                _ => Err(ElabError::ExpectedEqualityType)
            }
        }

        syntax::Term::Let { mode, def, body, .. } => {
            let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
                let anno_elabed = check(db, ctx.clone(), anno, Value::star())?;
                let anno_value = Value::eval(db, module, ctx.env(), anno_elabed.clone());
                (anno_elabed, anno_value)
            } else { infer(db, ctx.clone(), &def.body)? };
            let def_body_elabed = check(db, ctx.clone(), &def.body, anno_value.clone())?;
            let def_body_value = LazyValue::new(module, ctx.env(), def_body_elabed.clone());
            let ctx = ctx.define(db, def.name, *mode, def_body_value, anno_value);
            let (body_elabed, type_value) = infer(db, ctx, body)?;
            let result_let = Rc::new(core::Term::Let {
                sort,
                mode: *mode,
                name: def.name,
                let_body: def_body_elabed,
                body: body_elabed
            });
            let result = Rc::new(core::Term::Annotate { 
                anno: anno_elabed,
                body: result_let
            });
            Ok((result, type_value))
        }

        syntax::Term::Variable { span, id, .. } => {
            let (var_type, level) = lookup_type(db, &ctx, *span, id)?;
            if let Some(level) = level {
                let index = level.to_index(ctx.env.len());
                Ok((Rc::new(core::Term::Bound { sort, index }), var_type))
            } else {
                Ok((Rc::new(core::Term::Free { sort, id:id.clone() }), var_type))
            }
        }

        syntax::Term::Apply { span, mode, fun, arg, .. } => {
            let (mut fun_elabed, mut fun_type) = infer(db, ctx.clone(), fun)?;

            loop {
                fun_type = Value::unfold_to_head(db, fun_type);
                match fun_type.as_ref() {
                    Value::Pi { mode:type_mode, name, closure, .. }
                    if *type_mode != *mode
                    && *type_mode == Mode::Erased
                    && sort == Sort::Term =>
                    {
                        let meta = Rc::new(fresh_meta(db, ctx.clone()));
                        fun_elabed = Rc::new(core::Term::Apply {
                            sort,
                            mode: *type_mode,
                            fun: fun_elabed,
                            arg: meta.clone()
                        });
                        let arg = LazyValue::new(module, ctx.env(), meta);
                        let arg = EnvEntry::new(*name, *type_mode, arg);
                        fun_type = closure.eval(db, arg);
                    },
                    _ => break
                }
            }

            fun_type = Value::unfold_to_head(db, fun_type);
            let (name, type_mode, domain, closure) = match fun_type.as_ref() {
                Value::Pi { mode:type_mode, name, domain, closure, .. } => {
                    if sort == Sort::Term && *mode != *type_mode {
                        log::debug!("{:?} {} {:?}", mode , "=?".bright_blue(), type_mode);
                        return Err(ElabError::ModeMismatch);
                    }
                    (*name, *type_mode, domain.clone(), closure.clone())
                },
                _ => {
                    let name = Symbol::from("x");
                    let domain = Rc::new(fresh_meta(db, ctx.clone()));
                    let domain = Value::eval(db, ctx.module, ctx.env(), domain);
                    let meta = Rc::new(fresh_meta(db, ctx.bind(db, name, Mode::Free, domain.clone())));
                    let closure = Closure::new(ctx.module, ctx.env(), meta);
                    let candidate_type = Value::pi(sort, *mode, name, domain.clone(), closure.clone());
                    unify(db, ctx.clone(), *span, &fun_type, &candidate_type)?;
                    (name, *mode, domain, closure)
                }
            };

            let arg_elabed = check(db, ctx.clone(), arg, domain.clone())?;
            let arg_value = LazyValue::new(module, ctx.env(), arg_elabed.clone());
            let closure_arg = EnvEntry::new(name, type_mode, arg_value);
            let result_type = closure.eval(db, closure_arg);
            let result = Rc::new(core::Term::Apply {
                sort,
                mode: *mode,
                fun: fun_elabed,
                arg: arg_elabed
            });
            Ok((result, result_type))
        }

        syntax::Term::Project { span, variant, body, .. } => {
            let (body_elabed, body_type) = infer(db, ctx.clone(), body)?;
            let body_type_unfolded = Value::unfold_to_head(db, body_type.clone());
            match body_type_unfolded.as_ref() {
                Value::IntersectType { name, first, second } => {
                    let first_proj = Rc::new(core::Term::Project { variant:1, body: body_elabed.clone() });
                    let first_value = Value::eval(db, module, ctx.env(), first_proj.clone());
                    match variant {
                        1 => Ok((first_proj, first.clone())),
                        2 => {
                            let second_proj = Rc::new(core::Term::Project { variant:2, body: body_elabed });
                            let closure_arg = EnvEntry::new(*name, Mode::Free, LazyValue::computed(first_value));
                            let result_type = second.eval(db, closure_arg);
                            Ok((second_proj, result_type))
                        }
                        _ => Err(ElabError::UnsupportedProjection)
                    }
                },
                _ => Err(ElabError::ExpectedIntersectionType {
                    src: db.text(ctx.module),
                    span: source_span(db, ctx.module, *span),
                    inferred_type: body_type.quote(db, ctx.env_lvl()).to_string()
                })
            }
        }

        syntax::Term::Cast { equation, input, erasure, .. } => {
            let (input_elabed, result_type) = infer(db, ctx.clone(), input)?;
            let input_value = Value::eval(db, module, ctx.env(), input_elabed.clone());
            let erasure_elabed = erase(db, ctx.clone(), erasure)?;
            let erasure_value = Value::eval(db, module, ctx.env(), erasure_elabed.clone());
            let equality_type = Value::equality(input_value, erasure_value);
            let equation_elabed = check(db, ctx.clone(), equation, equality_type)?;
            let result = Rc::new(core::Term::Cast { 
                equation: equation_elabed,
                input: input_elabed,
                erasure: erasure_elabed
            });
            Ok((result, result_type))
        }

        syntax::Term::Star { .. } => Ok((Rc::new(core::Term::Star), Value::super_star())),

        syntax::Term::Hole { span, .. } => {
            Err(ElabError::Hole {
                src: db.text(ctx.module),
                span: source_span(db, ctx.module, *span),
                expected_type: String::from(""),
                context: ctx.to_string(db)
            })
        }

        syntax::Term::Omission { .. } => {
            let ty_meta = Rc::new(fresh_meta(db, ctx.clone()));
            let ty = Value::eval(db, module, ctx.env(), ty_meta);
            let term = Rc::new(fresh_meta(db, ctx.clone()));
            Ok((term, ty))
        }

        syntax::Term::Annotate { anno, body, .. } => {
            let anno_elabed = check(db, ctx.clone(), anno, Value::star())?;
            let anno_value = Value::eval(db, module, ctx.env(), anno_elabed.clone());
            let body_elabed = check(db, ctx.clone(), body, anno_value.clone())?;
            let result = Rc::new(core::Term::Annotate {
                anno: anno_elabed,
                body: body_elabed
            });
            Ok((result, anno_value))
        }

        _ => Err(ElabError::InferenceFailed { span:term.span() })
    };
    if let Ok((_, ref inferred_type)) = result {
        log::trace!("\n{}\n  {}\n{} {}", ctx.env(), term.as_str(db.text_ref(module)), "=>".bright_blue(), inferred_type);
    }
    result
}

pub fn erase(db: &mut Database, ctx: Context, term: &syntax::Term) -> Result<Rc<core::Term>, ElabError> {
    use syntax::Term;
    fn erase_lambda(db: &mut Database
        , ctx: Context
        , index: usize
        , vars: &[syntax::LambdaVar] 
        , body: &syntax::Term)
        -> Result<Rc<core::Term>, ElabError>
    {
        if let Some(var) = vars.get(index) {
            if var.mode == Mode::Erased {
                erase_lambda(db, ctx, index + 1, vars, body)
            } else {
                let name = var.var.unwrap_or_default();
                let ctx = ctx.bind(db, name, var.mode, Value::top_type());
                let body = erase_lambda(db, ctx, index + 1, vars, body)?;
                Ok(Rc::new(core::Term::Lambda {
                    sort: Sort::Term,
                    domain_sort: Sort::Term,
                    mode: var.mode,
                    name,
                    body
                }))
            }
        } else { erase(db, ctx, body) }
    }
    match term {
        Term::Lambda { vars, body, .. } =>
            erase_lambda(db, ctx, 0, vars, body),
        Term::Let { mode, def, body, .. } => {
            if *mode == Mode::Erased { erase(db, ctx, body) }
            else {
                let let_body = erase(db, ctx.clone(), &def.body)?;
                let ctx = ctx.bind(db, def.name, *mode, Value::star());
                let body = erase(db, ctx, body)?;
                Ok(Rc::new(core::Term::Let {
                    sort: Sort::Term,
                    mode: *mode,
                    name: def.name,
                    let_body,
                    body
                }))
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
        Term::Apply { mode, fun, arg, .. } => {
            let sort = Sort::Term;
            if *mode != Mode::Free { erase(db, ctx, fun) }
            else {
                let mode = Mode::Free;
                let fun = erase(db, ctx.clone(), fun)?;
                let arg = erase(db, ctx, arg)?;
                Ok(Rc::new(core::Term::Apply { sort, mode, fun, arg }))
            }
        },
        Term::Variable { span, id, .. } => {
            let sort = Sort::Term;
            let (_, level) = lookup_type(db, &ctx, *span, id)?;
            if let Some(level) = level {
                let index = level.to_index(ctx.env.len());
                Ok(Rc::new(core::Term::Bound { sort, index }))
            } else {
                Ok(Rc::new(core::Term::Free { sort, id:id.clone() }))
            }
        },
        Term::Star { .. } => Err(ElabError::ExpectedTerm { span:term.span() }),
        Term::Hole { span, .. } =>
            Err(ElabError::Hole {
                src: db.text(ctx.module),
                span: source_span(db, ctx.module, *span),
                expected_type: String::from(""),
                context: ctx.to_string(db)
            }),
        Term::Omission { .. } => {
            let fresh_meta_name = db.fresh_meta(ctx.module);
            Ok(Rc::new(core::Term::InsertedMeta {
                name: fresh_meta_name,
                mask: ctx.env_mask()
            }))
        }
    }
}

fn infer_sort(db: &Database, ctx: Context, term: &syntax::Term) -> Sort {
    let result = match term {
        syntax::Term::Lambda { vars, body, .. } => {
            let mut ctx = ctx.clone();
            for var in vars {
                let name = var.var.unwrap_or_default();
                if let Some(anno) = &var.anno {
                    let anno_sort = infer_sort(db, ctx.clone(), anno).demote();
                    ctx = ctx.bind_sort(name, anno_sort);
                } else {
                    ctx = ctx.bind_sort(name, Sort::Unknown);
                }
            }
            infer_sort(db, ctx, body)
        }
        syntax::Term::Let { body, .. } => infer_sort(db, ctx.clone(), body),
        syntax::Term::Pi { var, domain, body, .. } => {
            let name = var.unwrap_or_default();
            let domain_sort = infer_sort(db, ctx.clone(), domain).demote();
            let ctx = ctx.bind_sort(name, domain_sort);
            infer_sort(db, ctx, body)
        }
        syntax::Term::IntersectType { .. }
        | syntax::Term::Equality { .. } => Sort::Type,
        syntax::Term::Rewrite { .. } => Sort::Term,
        syntax::Term::Annotate { body, .. } => infer_sort(db, ctx.clone(), body),
        syntax::Term::Project { .. } => Sort::Term,
        syntax::Term::Symmetry { .. }
        | syntax::Term::Intersect { .. }
        | syntax::Term::Separate { .. }
        | syntax::Term::Reflexivity { .. }
        | syntax::Term::Cast { .. }
        | syntax::Term::Induct { .. }
        | syntax::Term::Match { .. } => Sort::Term,
        syntax::Term::Apply { fun, .. } => infer_sort(db, ctx.clone(), fun),
        syntax::Term::Variable { id, .. } => lookup_sort(db, &ctx, id),
        syntax::Term::Star { .. } => Sort::Kind,
        syntax::Term::Hole { .. } => Sort::Unknown,
        syntax::Term::Omission { .. } => Sort::Unknown,
    };
    result
}

fn unify(db: &mut Database, ctx: Context, span: Span, left: &Rc<Value>, right: &Rc<Value>) -> Result<(), ElabError> {
    match Value::unify(db, ctx.env_lvl(), left, right) {
        Ok(true) => Ok(()),
        Ok(false) | Err(_) => Err(ElabError::Inconvertible {
            src: db.text(ctx.module),
            span: source_span(db, ctx.module, span),
            left: left.quote(db, ctx.env_lvl())
                .to_string_with_context(ctx.names.clone()),
            right: right.quote(db, ctx.env_lvl())
                .to_string_with_context(ctx.names)
        })
    }
}

fn fresh_meta(db: &mut Database, ctx: Context) -> core::Term {
    let fresh_meta_name = db.fresh_meta(ctx.module);
    core::Term::InsertedMeta {
        name: fresh_meta_name,
        mask: ctx.env_mask()
    }
}

fn lookup_type(db: &Database, ctx: &Context, span: Span, id: &Id) -> Result<(Rc<Value>, Option<Level>), ElabError> {
    let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
    let toplevel_type = db.lookup_type(ctx.module, id);
    let context_type = has_namespace
        .and(ctx.names.iter().zip(ctx.types.iter()).enumerate().rev().find(|(_, (x, _))| **x == id.name))
        .map(|(level, (_, ty))| (ty.clone(), Some(level.into())));
    match (toplevel_type, context_type) {
        (_, Some((v, level))) => Ok((v, level)),
        (Some(v), None) => Ok((v.force(db), None)),
        (None, None) => { Err(ElabError::MissingName { source_code: db.text(ctx.module), span: source_span(db, ctx.module, span) }) }
    }
}

fn lookup_sort(db: &Database, ctx: &Context, id: &Id) -> Sort {
    let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
    let toplevel_sort = db.lookup_type(ctx.module, id)
        .map(|x| x.sort(db).demote());
    let context_sort = has_namespace
        .and(ctx.names.iter().zip(ctx.sorts.iter()).rev().find(|(x, _)| **x == id.name))
        .map(|(_, sort)| *sort);
    match (toplevel_sort, context_sort) {
        (_, Some(sort)) => sort,
        (Some(sort), None) => sort,
        (None, None) => Sort::Unknown
    }
}

fn source_span(db: &Database, module: Symbol, span: Span) -> SourceSpan {
    // TODO: This is a hack to fix the source positioning for miette
    // TODO: The parser should be grapheme relative (instead of byte relative)
    //       to properly fix this
    let (start, end) = span;
    let len = db.text_ref(module)[start..end].graphemes(true).count();
    // The positioning is "line-oriented" so you only have to correct up to the nearest newline
    let start_prefix = db.text_ref(module)[..start].as_bytes();
    let mut i = start - 1;
    while i > 0 && start_prefix[i] != b'\n' { i -= 1; }
    let byte_len = start - i;
    let graphemes_len = db.text_ref(module)[i..start].graphemes(true).count();
    // We subtract the extract internal bytes used to represent graphemes to correct the label source position
    let start = start - (byte_len - graphemes_len);
    SourceSpan::new(start.into(), len.into())
}
