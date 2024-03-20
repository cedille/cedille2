
use std::borrow::Borrow;
use std::sync::Arc;
use std::time;
use std::collections::HashMap;

use colored::Colorize;
use thiserror::Error;
use imbl::Vector;
use miette::{Diagnostic, SourceSpan};
use unicode_segmentation::UnicodeSegmentation;

use cedille2_core::prelude::*;
use crate::syntax::{self, Declaration};
use crate::database::{DatabaseExt};
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
    ModeMismatch {
        #[source_code]
        src: Arc<String>,
        #[label("Expected {expected} but found {provided}")]
        span: SourceSpan,
        expected: Mode,
        provided: Mode
    },
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
    DefinitionCollision {
        #[source_code]
        src: Arc<String>,
        #[label("Defined here")]
        span: SourceSpan,
    },
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
    InferenceFailed {
        #[source_code]
        src: Arc<String>,
        #[label("unable to infer type of term")]
        span: SourceSpan
    },
    #[error("Unsupported Projection")]
    #[diagnostic()]
    UnsupportedProjection,
    #[error("Rewrite Failed")]
    #[diagnostic()]
    RewriteFailed,
    #[error("Opaque definitions must have a valid type or kind")]
    #[diagnostic()]
    OpaqueMissingAnnotation,
    #[error("Sort Classifier Failed")]
    SortClassifier,
    #[error("Unknown error! {0}")]
    #[diagnostic()]
    Unknown(usize)
}

#[derive(Debug, Clone)]
pub struct Context {
    env: Env,
    env_mask: Vec<EnvBound>,
    pub names: Vector<Symbol>,
    pub types: Vector<Value>,
    pub sorts: Vector<Sort>,
    pub modes: Vector<Mode>,
    pub module: Symbol,
    pub mode: Mode,
    pub sort: Sort
}

impl Context {
    pub fn new(module: Symbol) -> Context {
        Context {
            env: Env::new(),
            env_mask: Vec::new(),
            names: Vector::new(),
            types: Vector::new(),
            sorts: Vector::new(),
            modes: Vector::new(),
            module,
            mode: Mode::Free,
            sort: Sort::Unknown
        }
    }

    pub fn phase_shift(mut self, mode: Mode, sort: Sort) -> Context {
        self.mode = mode;
        self.sort = sort;
        // If we phase shift into an erased context, then all currently erased variables can be treated as relevant
        if mode == Mode::Erased {
            self.modes = self.modes.iter()
                .map(|_| Mode::Free)
                .collect::<Vector<_>>();
        }
        self
    }

    pub fn bind_sort(&self, name: Symbol, sort: Sort) -> Context {
        let mut result = self.clone();
        result.names.push_back(name);
        result.sorts.push_back(sort);
        result
    }

    pub fn bind(&self, db: &mut Database, name: Symbol, mode: Mode, value_type: Value) -> Context {
        let mut result = self.clone();
        let level = self.env_lvl();
        let sort = value_type.sort().demote();
        let value = LazyValueData::var(db, sort, level);
        //log::trace!("\n{}\n{} {} {} {} {}", self.env, "bind".bright_blue(), name, value, ":".bright_blue(), value_type);
        result.env.push_back(EnvEntry::new(name, mode, value));
        result.env_mask.push(EnvBound::Bound);
        result.names.push_back(name);
        result.sorts.push_back(sort);
        result.types.push_back(value_type);
        result.modes.push_back(mode);
        result
    }

    pub fn define(&self, db: &Database, name: Symbol, mode: Mode, value: LazyValue, value_type: Value) -> Context {
        let mut result = self.clone();
        //log::trace!("\n{}\n{} {} {} {} {}", self.env, "define".bright_blue(), name, value, ":".bright_blue(), value_type);
        result.env.push_back(EnvEntry::new(name, mode, value));
        result.env_mask.push(EnvBound::Defined);
        result.names.push_back(name);
        result.sorts.push_back(value_type.sort().demote());
        result.types.push_back(value_type);
        result.modes.push_back(mode);
        result
    }

    pub fn to_string(&self, db: &mut Database) -> String {
        let mut result = String::new();
        for i in (0..self.len()).rev() {
            result.push('\n');
            let ty = self.types[i].clone();
            let type_string = quote(db, ty, self.env_lvl())
                .to_string_with_context(self.names.clone());
            let mode_prefix = if self.modes[i] == Mode::Erased { "-" } else { "" };
            result.push_str(format!("{}{}: {}", mode_prefix, self.names[i], type_string).as_str());
        }
        result
    }

    pub fn core_ctx(&self) -> core::Context {
        let env = self.env();
        core::Context {
            module: self.module,
            types: self.types.clone(),
            env
        }
    }

    pub fn env(&self) -> Env { self.env.clone() }

    pub fn env_mask(&self) -> Vec<EnvBound> { self.env_mask.clone() }

    pub fn env_lvl(&self) -> Level { self.env.len().into() }

    pub fn len(&self) -> usize { self.names.len() }
}

pub fn elaborate(db: &mut Database, module: Symbol, mut commands: Vec<syntax::Command>) -> Result<(), CedilleError> {
    let mut errors: Vec<CedilleError> = vec![];
    let mut decls = HashMap::new();
    let mut ctx: Context = Context::new(module);

    for command in commands.drain(..) {
        match command {
            syntax::Command::Module(_, params) => {
                match elaborate_module_params(db, Context::new(module), &params) {
                    Ok(c) => ctx = c,
                    Err(e) => errors.push(e.into())
                }
            }
            syntax::Command::Declare(Declaration { span, name, body }) => {
                decls.insert(name, body);
            }
            syntax::Command::Define(syntax::Definition { span, name, vars, body }) => {
                let body = if !vars.is_empty() {
                    let span = (0, 0);
                    syntax::Term::Lambda { span, vars, body }
                } else { *body };
                let anno = decls.get(&name).cloned();
                let def = syntax::DefineTerm {
                    span,
                    opaque: false,
                    name,
                    anno: anno.clone(),
                    body: body.boxed(),
                };
                match elaborate_define_term(db, ctx.clone(), &def) {
                    Ok(decl) => {
                        let inner_ann = decl.ty.clone();
                        let decl = Decl {
                            name: decl.name,
                            ty: wrap_type_from_context(db, ctx.clone(), decl.ty),
                            body: wrap_term_from_context(db, ctx.clone(), decl.body),
                        };
                        log::info!("\n{}\n{}\n{}", def.as_str(db.text_ref(module)), "elaborated to".green(), decl);
                        db.insert_decl(module, def.opaque, decl.clone(), inner_ann).ok().unwrap();
                    }
                    Err(e) => errors.push(e.into())
                }
            }
            syntax::Command::Import(import) => elaborate_import(db, ctx.clone(), &import)?,
            syntax::Command::Infer(_) => todo!(),
            syntax::Command::Check(_, _) => todo!(),
            syntax::Command::Erase(term) => {
                let (term_elabed, _) = infer(db, ctx.clone(), &term)?;
                let term_unfolded = unfold_all(db, term_elabed);
                let value = eval(db, ctx.env(), term_unfolded);
                let erased = erase(db, ctx.env_lvl(), value);
                let quote = quote(db, erased, ctx.env_lvl());
                log::info!("\n{}\n{}\n{}", term.as_str(db.text_ref(module)), "erased to".green(), quote.to_string());
            }
            syntax::Command::Value(_) => todo!(),
        }
    }
    // let ctx = elaborate_module_params(db, Context::new(module), &syntax.params)?;
    // for import in syntax.header_imports.iter() {
    //     elaborate_import(db, ctx.clone(), import)?;
    // }

    // for decl in syntax.decls.iter() {
    //     match elaborate_decl(db, ctx.clone(), decl) {
    //         Ok(_) =>  { },
    //         Err(error) => errors.push(error)
    //     }
    // }

    if errors.is_empty() { Ok(()) }
    else { Err(CedilleError::Collection(errors)) }
}

fn elaborate_module_params(db: &mut Database, ctx: Context, params: &[syntax::Parameter]) -> Result<Context, ElabError> {
    let mut ctx = ctx;
    let mut param_results = vec![];
    for param in params.iter() {
        let (body_elabed, _) = infer(db, ctx.clone(), &param.body)?;
        let body_value = eval(db, ctx.env(), body_elabed.clone());
        param_results.push(Parameter { name: param.name, mode: param.mode, body: body_elabed });
        ctx = ctx.bind(db, param.name, param.mode, body_value);
    }
    db.set_params(ctx.module, param_results);
    Ok(ctx)
}

// fn elaborate_decl(db: &mut Database, ctx: Context, decl: &syntax::Decl) -> Result<(), CedilleError> {
//     let module = ctx.module;
//     match decl {
//         syntax::Decl::Term(def) => {
//             if db.lookup_type(module, &Id::from(def.name)).is_some() {
//                 Err(ElabError::DefinitionCollision {
//                     src: db.text(module),
//                     span: source_span(db, module, def.span)
//                 }.into())
//             } else {
//                 let result = if def.opaque {
//                     elaborate_opaque_define_term(db, ctx.clone(), def)
//                 } else {
//                     elaborate_define_term(db, ctx.clone(), def)
//                 }.map_err(CedilleError::Elaborator)?;
//                 let result = term::Decl { 
//                     name: result.name,
//                     ty: wrap_type_from_context(db, ctx.clone(), result.ty),
//                     body: wrap_term_from_context(ctx, result.body)
//                 };
//                 log::info!("\n{}\n{}\n{}", def.as_str(db.text_ref(module)), "elaborated to".green(), result);
//                 db.insert_decl(module, def.opaque, result)
//                     .map_err(|()| CedilleError::Collection(vec![]))
//             }
//         }
//         syntax::Decl::Import(import) => elaborate_import(db, ctx, import),
//         syntax::Decl::Kind(_) => todo!(),
//         syntax::Decl::Datatype(_) => todo!(),
//         syntax::Decl::NormalizeCommand(term, erase_flag, print) => {
//             let (start, end) = term.span();
//             let now = time::Instant::now();
//             let erased = erase(db, ctx, term)?;
//             let value = eval(db, module, Environment::new(), erased);
//             let mut normal_form = Value::reify(value, db, 0.into(), true);
//             if *print {
//                 normal_form = if *erase_flag { normal_form.partial_erase() } else { normal_form };
//                 println!("{}", normal_form);
//             }
//             log::info!("Normalized {} in {}ms", &db.text(module)[start..end], now.elapsed().as_millis());
//             Ok(())
//         }
//     }
// }

fn elaborate_import_args(db: &mut Database
    , ctx: Context
    , args: &[(Mode, syntax::Term)]
    , params: &[Parameter])
    -> Result<Vec<(Mode, LazyValue)>, ElabError>
{
    let mut ctx = ctx;
    let mut result = vec![];
    for i in 0..args.len() {
        if let Some(Parameter { name, mode, body }) = params.get(i) {
            let ty = eval(db, ctx.env(), body.clone());
            let (arg_mode, arg) = &args[i];
            let arg_elabed = check(db, ctx.clone(), arg, ty.clone())?;

            if mode != arg_mode && arg_elabed.sort() == Sort::Term {
                return Err(ElabError::ModeMismatch { 
                    src: db.text(ctx.module), 
                    span: source_span(db, ctx.module, arg.span()), 
                    expected: *mode,
                    provided: *arg_mode
                })
            }
            let arg_value = LazyValueData::lazy(db, ctx.env(), arg_elabed);
            let arg_mode = if ty.sort() == Sort::Type { *arg_mode } else { Mode::Erased }; 
            result.push((arg_mode, arg_value.clone()));
            ctx = ctx.define(db, *name, *mode, arg_value, ty);
        } else {
            // TODO: add a reasonable error
            return Err(ElabError::Unknown(2))
        }
    }
    Ok(result)
}

fn elaborate_import(db: &mut Database, ctx: Context, import: &syntax::Import) -> Result<(), CedilleError> {
    let import_symbol = db.resolve_import_symbol(ctx.module, import.path)?;
    db.load_module(import_symbol)?; // Imported module may not be loaded at all, which means no parameters
    let params = db.lookup_params(import_symbol);
    let args = elaborate_import_args(db, ctx.clone(), &import.args, &params)?;
    db.load_import(ctx.module, import, args)?;
    Ok(())
}

// fn elaborate_opaque_define_term(db: &mut Database, ctx: Context, def: &syntax::DefineTerm) -> Result<Decl, ElabError> {
//     if let Some(anno) = &def.anno {
//         let anno_sort = infer_sort(db, ctx.clone(), anno)?;
//         let ctx = ctx.phase_shift(Mode::Free, anno_sort);
//         let anno_classifier = classifier(anno_sort).map_err(|_| ElabError::Unknown)?;
//         let ty = check(db, ctx, anno, anno_classifier)?;
//         let name = def.name;
//         let id = Id::from(def.name);
//         let body = db.make_term(TermData::Free {
//             sort: anno_sort,
//             id
//         });
//         Ok(Decl { name, ty, body })
//     } else {
//         Err(ElabError::OpaqueMissingAnnotation)
//     }
// }

fn elaborate_define_term(db: &mut Database, ctx: Context, def: &syntax::DefineTerm) -> Result<Decl, ElabError> {
    let (name, ty, body) = if let Some(anno) = &def.anno {
        let anno_sort = infer_sort(db, ctx.clone(), anno)?;
        let anno_classifier = classifier(anno_sort).map_err(|_| dbg!(ElabError::SortClassifier))?;
        let anno_ctx_mode = if anno_sort == Sort::Kind { Mode::TypeLevel } else { Mode::Free };
        let anno_ctx = ctx.clone().phase_shift(anno_ctx_mode, anno_sort);
        let anno_elabed = check(db, anno_ctx, anno, anno_classifier)?;
        let anno_value = eval(db, ctx.env(), anno_elabed.clone());
        let ctx = ctx.phase_shift(Mode::Free, anno_sort.demote());
        let body = check(db, ctx, &def.body, anno_value)?;
        (def.name, anno_elabed, body)
    } else {
        let (body, inferred) = infer(db, ctx.clone(), &def.body)?;
        let ty = quote(db, inferred, ctx.env_lvl());
        (def.name, ty, body)
    };
    Ok(Decl { name, ty, body })
}

fn check(db: &mut Database, ctx: Context, term: &syntax::Term, ty: Value) -> Result<Term, ElabError> {
    fn check_lambda(db: &mut Database
        , ctx: Context
        , index: usize
        , vars: &[syntax::LambdaVar]
        , body: &syntax::Term
        , ty: Value)
        -> Result<Term, ElabError>
    {
        if let Some(var) = vars.get(index) {
            let ty = unfold_to_head(db, ty);
            match ty.as_ref() {
                ValueData::Pi { sort:type_sort, mode:type_mode, domain, closure, .. } => {
                    let sort = type_sort.demote();
                    let var_mode =
                        if *type_sort == Sort::Kind && var.mode != Mode::Erased { Mode::TypeLevel }
                        else { var.mode };
                    if sort == Sort::Term && var_mode != *type_mode {
                        return Err(ElabError::ModeMismatch {
                            src: db.text(ctx.module),
                            span: source_span(db, ctx.module, body.span()),
                            expected: *type_mode,
                            provided: var_mode
                        })
                    }
                    let name = var.var.unwrap_or_default();
                    let anno = if let Some(ref anno) = var.anno {
                        let span = anno.span();
                        let anno_sort = infer_sort(db, ctx.clone(), anno)?;
                        let anno_classifier = classifier(anno_sort).map_err(|_| dbg!(ElabError::SortClassifier))?;
                        let anno_ctx_mode = if anno_sort == Sort::Kind { Mode::TypeLevel } else { Mode::Free };
                        let anno_ctx = ctx.clone().phase_shift(anno_ctx_mode, anno_sort);
                        let anno_elabed = check(db, anno_ctx, anno, anno_classifier)?;
                        let anno_value = eval(db, ctx.env(), anno_elabed.clone());
                        try_unify(db, ctx.clone(), span, anno_value, domain.clone())?;
                        anno_elabed
                    } else {
                        quote(db, domain.clone(), ctx.env_lvl())
                    };
                    let value = LazyValueData::var(db, domain.sort(), ctx.env_lvl());
                    let ctx = ctx.bind(db, name, *type_mode, domain.clone());
                    let body_type = closure.eval(db, EnvEntry::new(name, var_mode, value));
                    let body_elabed = check_lambda(db, ctx, index + 1, vars, body, body_type)?;
                    Ok(db.make_term(TermData::Lambda {
                        sort,
                        domain: anno,
                        mode: var_mode,
                        name,
                        body: body_elabed
                    }))
                }
                _ => Err(ElabError::ExpectedFunctionType)
            }
        } else { check(db, ctx, body, ty) }
    }

    let ty_folded = ty.clone();
    let ty = unfold_to_head(db, ty);
    //log::trace!("\n{}\n  {}\n{} {}", ctx.env(), term.as_str(db.text_ref(ctx.module)), "<=".bright_blue(), ty);
    match (term, ty.as_ref()) {
        (syntax::Term::Lambda { vars, body, .. }, _) =>
            check_lambda(db, ctx, 0, vars, body, ty),

        (syntax::Term::Let { mode, def, body, .. }, _) =>
        {
            let (_, anno_value) = if let Some(anno) = &def.anno {
                let anno_ctx = ctx.clone().phase_shift(Mode::Free, Sort::Type);
                let anno_elabed = check(db, anno_ctx, anno, ValueData::Star.rced())?;
                let anno_value = eval(db, ctx.env(), anno_elabed.clone());
                (anno_elabed, anno_value)
            } else { infer(db, ctx.clone(), &def.body)? };
            let def_body_elabed = check(db, ctx.clone(), &def.body, anno_value.clone())?;
            let def_body_value = LazyValueData::lazy(db, ctx.env(), def_body_elabed.clone());
            let ctx = ctx.define(db, def.name, *mode, def_body_value, anno_value);
            let body_elabed = check(db, ctx, body, ty)?;
            let result = db.make_term(TermData::Let {
                sort: body_elabed.sort(),
                name: def.name,
                let_body: def_body_elabed,
                body: body_elabed
            });
            Ok(result)
        }

        (syntax::Term::Pair { span, first, second, anno },
            ValueData::Intersect { name, first:type1, second:type2 }) =>
        {
            let first_elabed = check(db, ctx.clone(), first, type1.clone())?;
            let first_value = LazyValueData::lazy(db, ctx.env(), first_elabed.clone());
            let closure_arg = EnvEntry::new(*name, Mode::Free, first_value.clone());
            let type2_value = type2.eval(db, closure_arg.clone());
            let second_elabed = check(db, ctx.clone(), second, type2_value.clone())?;
            let second_value = eval(db, ctx.env(), second_elabed.clone());
            let first_value = first_value.force(db);
            let anno_elabed = if let Some(anno) = anno {
                let (anno_elabed, anno_value) = infer(db, ctx.clone(), anno)?;
                match anno_value.as_ref() {
                    ValueData::Pi { sort, mode, name, domain, closure } => {
                        let closure = closure.eval(db, closure_arg);
                        try_unify(db, ctx.clone(), anno.span(), domain.clone(), type1.clone())?;
                        try_unify(db, ctx.clone(), anno.span(), closure.clone(), type2_value.clone())?;
                        anno_elabed
                    },
                    _ => return Err(ElabError::Unknown(1))
                }
            } else {
                let (sort, mode, name) = (Sort::Type, Mode::TypeLevel, *name);
                let (domain, closure) = (type1.clone(), type2.clone());
                let anno_value = ValueData::Lambda { sort, mode, name, domain, closure }.rced();
                quote(db, anno_value, ctx.env_lvl())
            };
            try_unify(db, ctx.clone(), *span, first_value, second_value)
                .map_err(|_| ElabError::IntersectionInconvertible {
                        src: db.text(ctx.module),
                        left: source_span(db, ctx.module, first.span()),
                        right: source_span(db, ctx.module, second.span())
                    })?;
            Ok(db.make_term(TermData::Pair {
                first: first_elabed,
                second: second_elabed,
                anno: anno_elabed
            }))
        }

        // (syntax::Term::Reflexivity { span, input, .. },
        //     Value::Equality { left, right }) =>
        // {
        //     let input_elabed = 
        //     let erasure_elabed = if let Some(t) = erasure { erase(db, ctx.clone(), t)? }
        //         else { Rc::new(term::Term::id()) };
        //     unify(db, ctx, *span, left, right)?;
        //     Ok(Rc::new(term::Term::Refl { erasure: erasure_elabed }))
        // }

        // (syntax::Term::Separate { span, equation, .. }, _) =>
        // {
        //     let equation_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
        //     let (equation_elabed, equality) = infer(db, equation_ctx, equation)?;
        //     let equality = unfold_to_head(db, equality);
        //     match equality.as_ref() {
        //         ValueData::Equality { left, right, anno } => {
        //             if try_unify(db, ctx, *span, left.clone(), right.clone()).is_ok() {
        //                 Err(ElabError::Convertible { span:*span })
        //             } else {
        //                 Ok(db.make_term(TermData::Separate { equation: equation_elabed }))
        //             }
        //         },
        //         _ => Err(ElabError::ExpectedEqualityType)
        //     }
        // }

        // (syntax::Term::Rewrite { span, equation, guide, body, occurrence, .. },
        //     _) =>
        // {
        //     let equation_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
        //     let (equation_elabed, equality) = infer(db, equation_ctx, equation)?;
        //     let equality = Value::unfold_to_head(db, equality);
        //     match equality.as_ref() {
        //         Value::Equality { left, right } => {
        //             let guide_name = guide.as_ref().map(|g| g.name).unwrap_or_default();
        //             let guide_ctx = ctx
        //                 .bind(db, guide_name, Mode::Free, Value::top_type())
        //                 .phase_shift(Mode::Free, Sort::Type);
        //             let guide_ty_elabed = if let Some(guide) = guide {
        //                 check(db, guide_ctx, &guide.ty, Value::star())?
        //             } else {
        //                 rewriter::match_term(db, guide_ctx, *occurrence, left, &ty)?
        //             };
        //             let guide_ty_closure = Closure::new(ctx.module, ctx.env(), guide_ty_elabed.clone());

        //             unify(db
        //                 , ctx.clone()
        //                 , *span
        //                 , &guide_ty_closure.eval(db, EnvEntry::new(guide_name, Mode::Free, left))
        //                 , &ty)?;

        //             let body_elabed = check(db
        //                 , ctx.clone()
        //                 , body
        //                 , guide_ty_closure.eval(db, EnvEntry::new(guide_name, Mode::Free, right)))?;

        //             Ok(Rc::new(term::Term::Rewrite {
        //                 equation: equation_elabed,
        //                 guide: term::RewriteGuide {
        //                     name: guide_name,
        //                     hint: Rc::new(right.quote(db, ctx.env_lvl())),
        //                     ty: guide_ty_elabed
        //                 },
        //                 body: body_elabed
        //             }))
        //         }
        //         _ => Err(ElabError::ExpectedEqualityType)
        //     }
        // }

        // (syntax::Term::Cast { span, input, witness, evidence }, _) =>
        // {
        //     // let input_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
        //     // let input_elabed = check(db, input_ctx, input, ty)?;
        //     // let input_value = eval(db, ctx.module, ctx.env(), input_elabed.clone());
        //     // let witness_elabed = erase(db, ctx.clone(), witness)?;
        //     // let witness_value = eval(db, ctx.module, ctx.env(), witness_elabed.clone());
        //     unimplemented!();
        //     // let equality_type = ValueData:Equality { input(input_value, witness_value);
        //     // let evidence_ctx = ctx.phase_shift(Mode::Erased, Sort::Term);
        //     // let evidence_elabed = check(db, evidence_ctx, evidence, equality_type)?;
        //     // Ok(Rc::new(term::Term::Cast { 
        //     //     evidence: evidence_elabed,
        //     //     input: input_elabed,
        //     //     witness: witness_elabed
        //     // }))
        // }

        (syntax::Term::Hole { span, .. }, _) => {
            let ty_folded = quote(db, ty_folded, ctx.env_lvl());
            let expected_type = ty_folded.to_string_with_context(ctx.names.clone());
            Err(ElabError::Hole { 
                src: db.text(ctx.module), 
                span: source_span(db, ctx.module, *span),
                expected_type,
                context: ctx.clone().to_string(db)
            })
        }

        (syntax::Term::Omission { .. }, _) => Ok(fresh_meta(db, ctx, ty.sort().demote())),

        // change direction
        _ => {
            let (mut result, mut inferred_type) = infer(db, ctx.clone(), term)?;

            loop {
                match (&*result, inferred_type.as_ref()) {
                    (TermData::Free { sort, .. }, ValueData::Pi { mode, name, domain, closure, .. })
                    if *mode == Mode::Erased && *sort == Sort::Term =>
                    {
                        let sort = domain.sort().demote();
                        let meta = fresh_meta(db, ctx.clone(), sort);
                        let meta_value = LazyValueData::lazy(db, ctx.env(), meta.clone());

                        result = db.make_term(TermData::Apply {
                            sort,
                            mode: *mode,
                            fun: result,
                            arg: meta
                        });
                        inferred_type = closure.eval(db, EnvEntry::new(*name, *mode, meta_value));
                    }
                    _ => break
                }
            }

            try_unify(db, ctx, term.span(), ty, inferred_type)?;
            Ok(result)
        }
    }
}

fn infer(db: &mut Database, ctx: Context, term: &syntax::Term) -> Result<(Term, Value), ElabError> {
    let module = ctx.module;
    let sort = infer_sort(db, ctx.clone(), term)?;
    let result = match term {

        syntax::Term::Set { .. } => {
            let result = db.make_term(TermData::Star);
            let ty = ValueData::SuperStar.rced();
            Ok((result, ty))
        }

        syntax::Term::Pi { mode
            , var
            , domain
            , body
            , .. } =>
        {
            let name = var.unwrap_or_default();
            let domain_sort = infer_sort(db, ctx.clone(), domain)?;
            let mode = if sort == Sort::Kind && *mode != Mode::Erased { Mode::TypeLevel } else { *mode };
            let domain_classifier = classifier(domain_sort).map_err(|_| dbg!(ElabError::SortClassifier))?;
            let domain_elabed = check(db, ctx.clone(), domain, domain_classifier)?;
            let domain_value = eval(db, ctx.env(), domain_elabed.clone());
            let ctx = ctx.bind(db, name, mode, domain_value);
            let body_classifier = classifier(sort).map_err(|_| dbg!(ElabError::SortClassifier))?;
            let body_elabed = check(db, ctx, body, body_classifier.clone())?;
            let result = db.make_term(TermData::Pi { 
                sort,
                mode,
                name,
                domain: domain_elabed,
                body: body_elabed
            });
            Ok((result, body_classifier))
        }

        syntax::Term::Intersect { var, first, second, .. } => {
            let first_elabed = check(db, ctx.clone(), first, ValueData::Star.rced())?;
            let first_value = eval(db, ctx.env(), first_elabed.clone());
            let name = var.unwrap_or_default();
            let ctx = ctx.bind(db, name, Mode::Free, first_value);
            let second_elabed = check(db, ctx, second, ValueData::Star.rced())?;
            let result = db.make_term(TermData::Intersect {
                name,
                first: first_elabed,
                second: second_elabed
            });
            Ok((result, ValueData::Star.rced()))
        }

        syntax::Term::Equality { left, right, domain, .. } => {
            if let Some(domain) = domain {
                let domain_elab = check(db, ctx.clone(), domain, ValueData::Star.rced())?;
                let domain_value = eval(db, ctx.env(), domain_elab.clone());
                let left_elab = check(db, ctx.clone(), left, domain_value.clone())?;
                let right_elab = check(db, ctx, right, domain_value)?;
                let result = db.make_term(TermData::Equality {
                    left: left_elab,
                    right: right_elab,
                    anno: domain_elab
                });
                Ok((result, ValueData::Star.rced()))
            } else {
                let (left_elab, domain_value) = infer(db, ctx.clone(), left)?;
                let domain_elab = quote(db, domain_value.clone(), ctx.env_lvl());
                let right_elab = check(db, ctx, right, domain_value)?;
                let result = db.make_term(TermData::Equality {
                    left: left_elab,
                    right: right_elab,
                    anno: domain_elab
                });
                Ok((result, ValueData::Star.rced()))
            }
        }

        syntax::Term::Let { mode, def, body, .. } => {
            let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
                let anno_ctx = ctx.clone().phase_shift(Mode::Free, Sort::Type);
                let anno_elabed = check(db, anno_ctx, anno, ValueData::Star.rced())?;
                let anno_value = eval(db, ctx.env(), anno_elabed.clone());
                (anno_elabed, anno_value)
            } else { infer(db, ctx.clone(), &def.body)? };
            let def_body_elabed = check(db, ctx.clone(), &def.body, anno_value.clone())?;
            let def_body_value = LazyValueData::lazy(db, ctx.env(), def_body_elabed.clone());
            let ctx = ctx.define(db, def.name, *mode, def_body_value, anno_value);
            let (body_elabed, type_value) = infer(db, ctx, body)?;
            let result = db.make_term(TermData::Let {
                sort,
                name: def.name,
                let_body: def_body_elabed,
                body: body_elabed
            });
            Ok((result, type_value))
        }

        syntax::Term::Variable { span, id, .. } => {
            let (var_type, level, mode) = lookup_type(db, &ctx, *span, id)?;
            if mode == Mode::Erased && ctx.mode == Mode::Free && ctx.sort == Sort::Term {
                Err(ElabError::ModeMismatch { 
                    src: db.text(ctx.module),
                    span: source_span(db, ctx.module, *span),
                    expected: ctx.mode,
                    provided: mode
                })
            } else if let Some(level) = level {
                let index = level.to_index(ctx.env.len());
                Ok((db.make_term(TermData::Bound { sort, index }), var_type))
            } else {
                Ok((db.make_term(TermData::Free { sort, id:id.clone() }), var_type))
            }
        }

        syntax::Term::Apply { span, fun, arg, .. } => {
            let arg_sort = infer_sort(db, ctx.clone(), arg)?;
            let (mut fun_elabed, mut fun_type) = infer(db, ctx.clone(), fun)?;

            // loop {
            //     fun_type = Value::unfold_to_head(db, fun_type);
            //     match fun_type.as_ref() {
            //         Value::Pi { mode, name, domain, closure, .. }
            //         if *mode == Mode::Erased =>
            //         {
            //             let arg_sort = domain.sort(db).demote();
            //             let meta = Rc::new(fresh_meta(db, ctx.clone(), arg_sort));
            //             fun_elabed = Rc::new(term::Term::Apply {
            //                 sort,
            //                 mode: *mode,
            //                 fun: fun_elabed,
            //                 arg: meta.clone()
            //             });
            //             let arg = LazyValue::new(module, ctx.env(), meta);
            //             let arg = EnvEntry::new(*name, *mode, arg);
            //             fun_type = closure.eval(db, arg);
            //         },
            //         _ => break
            //     }
            // }

            fun_type = unfold_to_head(db, fun_type);
            let (name, mode, domain, closure) = match fun_type.as_ref() {
                ValueData::Pi { mode, name, domain, closure, .. } => {
                    // if sort == Sort::Term && *mode != *type_mode {
                    //     return Err(ElabError::ModeMismatch {
                    //         src: db.text(ctx.module),
                    //         span: source_span(db, ctx.module, arg.span()),
                    //         expected: *type_mode,
                    //         provided: *mode
                    //     });
                    // }
                    (*name, *mode, domain.clone(), closure.clone())
                },
                _ => {
                    let name = Symbol::from("x");
                    let sort = Sort::Unknown;
                    let domain = fresh_meta(db, ctx.clone(), sort);
                    let domain = eval(db, ctx.env(), domain.clone());
                    let meta_ctx = ctx.bind(db, name, Mode::Free, domain.clone());
                    let meta = fresh_meta(db, meta_ctx, sort);
                    let closure = Closure::new(ctx.env(), meta.clone());
                    let candidate_type = ValueData::Pi {
                        sort,
                        mode: Mode::Free,
                        name,
                        domain: domain.clone(),
                        closure: closure.clone()
                    }.rced();
                    try_unify(db, ctx.clone(), *span, fun_type, candidate_type)?;
                    (name, Mode::Free, domain, closure)
                }
            };

            let ctx = ctx.clone().phase_shift(mode, ctx.sort);
            let arg_elabed = check(db, ctx.clone(), arg, domain)?;
            let arg_value = LazyValueData::lazy(db, ctx.env(), arg_elabed.clone());
            //let arg_value_forced = arg_value.force(db);
            let closure_arg = EnvEntry::new(name, mode, arg_value);
            let result_type = closure.eval(db, closure_arg);
            let result = db.make_term(TermData::Apply {
                sort,
                mode,
                fun: fun_elabed,
                arg: arg_elabed
            });
            Ok((result, result_type))
        }

        syntax::Term::Project { span, variant, body, .. } => {
            let (body_elabed, body_type) = infer(db, ctx.clone(), body)?;
            let body_type_unfolded = unfold_to_head(db, body_type.clone());
            match body_type_unfolded.as_ref() {
                ValueData::Intersect { name, first, second } => {
                    let first_proj = db.make_term(TermData::Project { variant:1, body: body_elabed.clone() });
                    let first_value = LazyValueData::lazy(db, ctx.env(), first_proj.clone());
                    match variant {
                        1 => Ok((first_proj, first.clone())),
                        2 => {
                            let second_proj = db.make_term(TermData::Project { variant:2, body: body_elabed });
                            let closure_arg = EnvEntry::new(*name, Mode::Free, first_value);
                            let result_type = second.eval(db, closure_arg);
                            Ok((second_proj, result_type))
                        }
                        _ => Err(ElabError::UnsupportedProjection)
                    }
                },
                _ => Err(ElabError::ExpectedIntersectionType {
                    src: db.text(ctx.module),
                    span: source_span(db, ctx.module, *span),
                    inferred_type: quote(db, body_type, ctx.env_lvl()).to_string()
                })
            }
        }

        syntax::Term::Refl { span, input, .. } => {
            let input_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
            let (input_elab, anno) = infer(db, input_ctx, input)?;
            let input_value = LazyValueData::lazy(db, ctx.env(), input_elab.clone());
            let result = db.make_term(TermData::Refl { input: input_elab });
            let result_type = ValueData::Equality {
                left: input_value.clone(),
                right: input_value,
                anno
            }.rced();
            Ok((result, result_type))
        }

        syntax::Term::Promote { span, variant, equation, lhs, rhs } => {
            let (lhs_elabed, inter_type) = infer(db, ctx.clone(), lhs)?;
            let rhs_elabed = check(db, ctx.clone(), rhs, inter_type.clone())?;
            let inter_type = unfold_to_head(db, inter_type);
            let ValueData::Intersect { first, second, .. } = inter_type.as_ref()
                else { return Err(ElabError::ExpectedIntersectionType { 
                    src: db.text(ctx.module),
                    span: source_span(db, ctx.module, lhs.span()),
                    inferred_type: quote(db, inter_type, ctx.env_lvl()).to_string() 
                })
            };
            let equation_elabed = if *variant == 1 {
                let eq_lhs = db.make_term(TermData::Project { variant: 1, body: lhs_elabed.clone() });
                let eq_lhs = LazyValueData::lazy(db, ctx.env(), eq_lhs);
                let eq_rhs = db.make_term(TermData::Project { variant: 1, body: rhs_elabed.clone() });
                let eq_rhs = LazyValueData::lazy(db, ctx.env(), eq_rhs);
                let eq_anno = first.clone();
                let eq = ValueData::Equality { left: eq_lhs, right: eq_rhs, anno: eq_anno }.rced();
                check(db, ctx.clone(), equation, eq)?
            } else {
                let eq_lhs = db.make_term(TermData::Project { variant: 2, body: lhs_elabed.clone() });
                let eq_lhs = LazyValueData::lazy(db, ctx.env(), eq_lhs);
                let eq_rhs = db.make_term(TermData::Project { variant: 2, body: rhs_elabed.clone() });
                let eq_rhs = LazyValueData::lazy(db, ctx.env(), eq_rhs);
                let entry = EnvEntry::new(Symbol::default(), Mode::TypeLevel, LazyValueData::var(db, Sort::Type, 0.into()));
                let eq_anno = second.clone().eval(db, entry);
                let eq = ValueData::Equality { left: eq_lhs, right: eq_rhs, anno: eq_anno }.rced();
                check(db, ctx.clone(), equation, eq)?
            };
            let result = db.make_term(TermData::Promote {
                variant: *variant,
                equation: equation_elabed,
                lhs: lhs_elabed.clone(),
                rhs: rhs_elabed.clone()
            });
            let left = LazyValueData::lazy(db, ctx.env(), lhs_elabed);
            let right = LazyValueData::lazy(db, ctx.env(), rhs_elabed);
            let result_ty = ValueData::Equality { left, right, anno: inter_type }.rced();
            Ok((result, result_ty))
        }

        syntax::Term::Subst { span, predicate, equation } => {
            let (equation_elabed, eq_type) = infer(db, ctx.clone(), equation)?;
            let ValueData::Equality { left, right, anno } = eq_type.as_ref()
                else { return Err(ElabError::ExpectedEqualityType) };

            let inner_ty_value = ValueData::Pi {
                sort: Sort::Kind,
                mode: Mode::TypeLevel,
                name: Symbol::default(),
                domain: ValueData::Equality {
                    left: left.clone(),
                    right: LazyValueData::var(db, Sort::Term, ctx.env_lvl()),
                    anno: anno.clone()
                }.rced(),
                closure: Closure::new(Env::new(), db.make_term(TermData::Star)),
            }.rced();
            let inner_ty = quote(db, inner_ty_value, ctx.env_lvl() + 1);

            let predicate_ty = ValueData::Pi {
                sort: Sort::Kind,
                mode: Mode::TypeLevel,
                name: Symbol::default(),
                domain: anno.clone(),
                closure: Closure::new(ctx.env(), inner_ty),
            }.rced();

            let predicate_elabed = check(db, ctx.clone().phase_shift(Mode::TypeLevel, Sort::Type), predicate, predicate_ty)?;

            let result = db.make_term(TermData::Subst {
                predicate: predicate_elabed.clone(),
                equation: equation_elabed.clone()
            });
            let left_refl = db.make_term(TermData::Refl { input: left.code.clone() });
            let domain_ty = eval(db, ctx.env(), predicate_elabed.clone())
                .perform(db, Action::Apply(Mode::TypeLevel, left.clone()))
                .perform(db, Action::Apply(Mode::TypeLevel, LazyValueData::lazy(db, left.env.clone(), left_refl)));
            let codomain_ty = eval(db, ctx.env(), predicate_elabed.clone())
                .perform(db, Action::Apply(Mode::TypeLevel, right.clone()))
                .perform(db, Action::Apply(Mode::TypeLevel, LazyValueData::lazy(db, ctx.env(), equation_elabed)));
            let result_ty = ValueData::Pi {
                sort: Sort::Type,
                mode: Mode::Free,
                name: Symbol::default(),
                domain: domain_ty,
                closure: Closure::new(ctx.env(), quote(db, codomain_ty, ctx.env_lvl() + 1)),
            }.rced();
            
            Ok((result, result_ty))
        }

        syntax::Term::Cast { witness, evidence, .. } => {
            let (witness_elabed, witness_ty) = infer(db, ctx.clone(), witness)?;
            let witness_ty_unfolded = unfold_to_head(db, witness_ty);
            match witness_ty_unfolded.as_ref() {
                ValueData::Pi { mode:Mode::Free, domain, closure, .. } => {
                    let var = LazyValueData::var(db, sort, ctx.env_lvl());
                    let entry = EnvEntry::new(Symbol::default(), Mode::Free, var);
                    let closure_ty = closure.eval(db, entry);
                    let closure_ty_unfolded = unfold_to_head(db, closure_ty);
                    match closure_ty_unfolded.as_ref() {
                        ValueData::Intersect { first, .. } => {
                            try_unify(db, ctx.clone(), witness.span(), domain.clone(), first.clone())?;
                            let first_term = quote(db, first.clone(), ctx.env_lvl());
                            let evidence_ty = core::cast_evidence_ty(db, first_term, witness_elabed.clone());
                            let evidence_ty_value = eval(db, ctx.env(), evidence_ty);
                            let evidence_elabed = check(db, ctx.clone(), evidence, evidence_ty_value)?;
                            let evidence_value = eval(db, ctx.env(), evidence_elabed.clone());
                            let evidence_erased = erase(db, ctx.env_lvl(), evidence_value);
                            let evidence_erased_quote = quote(db, evidence_erased, ctx.env_lvl());
                            if !evidence_erased_quote.fv_empty_index(0.into()) { todo!() }
                            let result = db.make_term(TermData::Cast {
                                witness: witness_elabed,
                                evidence: evidence_elabed
                            });
                            Ok((result, witness_ty_unfolded))
                        }
                        _ => Err(ElabError::Unknown(7))
                    }
                }
                _ => Err(ElabError::ExpectedFunctionType)
            }
        }

        syntax::Term::Separate { span, equation } => {
            todo!()
        }

        syntax::Term::Omission { .. } => {
            let sort = Sort::Unknown;
            let ty_meta = fresh_meta(db, ctx.clone(), sort);
            let ty = eval(db, ctx.env(), ty_meta);
            let term = fresh_meta(db, ctx.clone(), sort);
            Ok((term, ty))
        }

        _ => {
            Err(ElabError::InferenceFailed {
                src: db.text(module),
                span: source_span(db, module, term.span())
            })
        }
    };
    if let Ok((_, ref inferred_type)) = result {
        //log::trace!("\n{}\n  {}\n{} {}", ctx.env(), term.as_str(db.text_ref(module)), "=>".bright_blue(), inferred_type);
    }
    result
}

// // If something is represented at the level of values (i.e. abstractions and applications) then we do not want to
// // erase it here. Convertibility modulo erasure is handled in values, and erasing it here just causes problems with
// // indices and other things.
// pub fn erase(db: &mut Database, ctx: Context, term: &syntax::Term) -> Result<Term, ElabError> {
//     use syntax::Term;
//     fn erase_lambda(db: &mut Database
//         , ctx: Context
//         , index: usize
//         , vars: &[syntax::LambdaVar] 
//         , body: &syntax::Term)
//         -> Result<Term, ElabError>
//     {
//         if let Some(var) = vars.get(index) {
//             let name = var.var.unwrap_or_default();
//             let ctx = ctx.bind(db, name, var.mode, Value::top_type());
//             let body = erase_lambda(db, ctx, index + 1, vars, body)?;
//             Ok(Rc::new(term::Term::Lambda {
//                 sort: Sort::Term,
//                 domain_sort: Sort::Term,
//                 mode: var.mode,
//                 name,
//                 body
//             }))
//         } else { erase(db, ctx, body) }
//     }
//     match term {
//         Term::Lambda { vars, body, .. } =>
//             erase_lambda(db, ctx, 0, vars, body),
//         Term::Let { mode, def, body, .. } => {
//             let let_body = erase(db, ctx.clone(), &def.body)?;
//             let ctx = ctx.bind(db, def.name, *mode, Value::star());
//             let body = erase(db, ctx, body)?;
//             Ok(Rc::new(term::Term::Let {
//                 sort: Sort::Term,
//                 name: def.name,
//                 let_body,
//                 body
//             }))
//         },
//         Term::Pi { .. }
//         | Term::Intersect { .. }
//         | Term::Equality { .. } => Err(ElabError::ExpectedTerm { span:term.span() }),
//         Term::Project { body, .. } => erase(db, ctx, body),
//         Term::Pair { first, .. } => erase(db, ctx, first),
//         Term::Separate { .. } => Ok(Rc::new(term::Term::id())),
//         Term::Refl { .. } => {
//             Ok(Rc::new(term::Term::id()))
//         },
//         Term::Promote { equation, .. } => erase(db, ctx, equation),
//         Term::J { .. } => unimplemented!(),
//         Term::Cast { input, .. } => erase(db, ctx, input),
//         Term::Apply { fun, arg, .. } => {
//             let (mode, sort) = (Mode::Free, Sort::Term);
//             let fun = erase(db, ctx.clone(), fun)?;
//             let arg = erase(db, ctx, arg)?;
//             Ok(Rc::new(term::Term::Apply { sort, mode, fun, arg }))
//         },
//         Term::Variable { span, id, .. } => {
//             let sort = Sort::Term;
//             let (_, level, _) = lookup_type(db, &ctx, *span, id)?;
//             if let Some(level) = level {
//                 let index = level.to_index(ctx.env.len());
//                 Ok(Rc::new(term::Term::Bound { sort, index }))
//             } else {
//                 Ok(Rc::new(term::Term::Free { sort, id:id.clone() }))
//             }
//         },
//         Term::Hole { span, .. } =>
//             Err(ElabError::Hole {
//                 src: db.text(ctx.module),
//                 span: source_span(db, ctx.module, *span),
//                 expected_type: String::from(""),
//                 context: ctx.to_string(db)
//             }),
//         Term::Omission { .. } => {
//             let fresh_meta_name = db.fresh_meta(ctx.module);
//             Ok(Rc::new(term::Term::InsertedMeta {
//                 sort: Sort::Term,
//                 name: fresh_meta_name,
//                 mask: ctx.env_mask()
//             }))
//         }
//         Term::Set { .. } => unimplemented!()
//     }
// }

fn infer_sort(db: &Database, ctx: Context, term: &syntax::Term) -> Result<Sort, ElabError> {
    let result: Sort = match term {
        syntax::Term::Lambda { vars, body, .. } => {
            let mut ctx = ctx;
            for var in vars {
                let name = var.var.unwrap_or_default();
                if let Some(anno) = &var.anno {
                    let anno_sort = infer_sort(db, ctx.clone(), anno)?.demote();
                    ctx = ctx.bind_sort(name, anno_sort);
                } else {
                    ctx = ctx.bind_sort(name, Sort::Unknown);
                }
            }
            infer_sort(db, ctx, body)?
        }
        syntax::Term::Let { def, body, .. } => {
            let def_sort = infer_sort(db, ctx.clone(), &def.body)?;
            let ctx = ctx.bind_sort(def.name, def_sort);
            infer_sort(db, ctx, body)?
        }
        syntax::Term::Pi { var, domain, body, .. } => {
            let name = var.unwrap_or_default();
            let domain_sort = infer_sort(db, ctx.clone(), domain)?.demote();
            let ctx = ctx.bind_sort(name, domain_sort);
            infer_sort(db, ctx, body)?
        }
        syntax::Term::Intersect { .. }
        | syntax::Term::Equality { .. } => Sort::Type,
        syntax::Term::Project { .. } => Sort::Term,
        syntax::Term::Pair { .. }
        | syntax::Term::Separate { .. }
        | syntax::Term::Refl { .. }
        | syntax::Term::Cast { .. }
        | syntax::Term::Promote { .. }
        | syntax::Term::Subst { .. } => Sort::Term,
        syntax::Term::Apply { fun, .. } => infer_sort(db, ctx, fun)?,
        syntax::Term::Variable { id, span } => lookup_sort(db, &ctx, *span, id)?,
        syntax::Term::Hole { .. } => Sort::Unknown,
        syntax::Term::Omission { .. } => Sort::Unknown,
        syntax::Term::Set { .. } => Sort::Kind
    };
    Ok(result)
}

fn try_unify(db: &mut Database, ctx: Context, span: Span, left: Value, right: Value) -> Result<(), ElabError> {
    let left = erase(db, ctx.env_lvl(), left);
    let right = erase(db, ctx.env_lvl(), right);
    match unify(db, ctx.env_lvl(), left.clone(), right.clone()) {
        true => Ok(()),
        false => Err(ElabError::Inconvertible {
            src: db.text(ctx.module),
            span: source_span(db, ctx.module, span),
            left: quote(db, left, ctx.env_lvl())
                .to_string_with_context(ctx.names.clone()),
            right: quote(db, right, ctx.env_lvl())
                .to_string_with_context(ctx.names)
        })
    }
}

// fn fresh_hole(db: &mut Database, ctx: Context, data: HoleData, sort: Sort) -> Term {
//     let fresh_hole_name = db.fresh_hole(ctx.module, data);
//     let id = Id { namespace: vec![], name: fresh_hole_name };
//     Rc::new(term::Term::Free { sort, id })
// }

fn fresh_meta(db: &mut Database, ctx: Context, sort: Sort) -> Term {
    let fresh_meta_name = db.fresh_meta(ctx.module);
    db.make_term(TermData::InsertedMeta {
        sort,
        name: fresh_meta_name,
        mask: ctx.env_mask()
    })
}

fn lookup_type(db: &mut Database, ctx: &Context, span: Span, id: &Id) -> Result<(Value, Option<Level>, Mode), ElabError> {
    let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
    let toplevel_type = db.lookup_type(id);
    let context_type = has_namespace
        .and(ctx.names.iter().zip(ctx.types.iter()).zip(ctx.modes.iter()).enumerate().rev().find(|(_, ((x, _), _))| **x == id.name))
        .map(|(level, ((_, ty), mode))| (ty.clone(), Some(level.into()), mode));
    match (toplevel_type, context_type) {
        (_, Some((v, level, mode))) => Ok((v, level, *mode)),
        (Some(v), None) => Ok((v, None, Mode::Free)),
        (None, None) => {
            Err(ElabError::MissingName { source_code: db.text(ctx.module), span: source_span(db, ctx.module, span) })
        }
    }
}

fn lookup_sort(db: &Database, ctx: &Context, span: Span, id: &Id) -> Result<Sort, ElabError> {
    let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
    let toplevel_sort = db.lookup_type(id)
        .map(|x| x.sort().demote());
    let context_sort = has_namespace
        .and(ctx.names.iter().zip(ctx.sorts.iter()).rev().find(|(x, _)| **x == id.name))
        .map(|(_, sort)| *sort);
    match (toplevel_sort, context_sort) {
        (_, Some(sort)) => Ok(sort),
        (Some(sort), None) => Ok(sort),
        (None, None) => {
            Err(ElabError::MissingName { source_code: db.text(ctx.module), span: source_span(db, ctx.module, span) })
        }
    }
}

fn wrap_term_from_context(db: &Database, ctx: Context, body: Term) -> Term {
    let sort = body.sort();
    let mut result = body;
    let mut level = ctx.env_lvl();
    for i in (0..ctx.len()).rev() {
        level = level - 1; // As we peel off a module parameter, the context maximum level is reduced by one
        let name = ctx.names[i];
        let domain = quote(db, ctx.types[i].clone(), level);
        let mode = if sort != Sort::Term { Mode::TypeLevel } else { ctx.modes[i] };
        result = db.make_term(TermData::Lambda {
            sort: result.sort(),
            mode,
            name,
            domain,
            body: result
        })
    }
    result
}

fn wrap_type_from_context(db: &Database, ctx: Context, body: Term) -> Term {
    let sort = body.sort();
    let mut result = body;
    let mut level = ctx.env_lvl();
    for i in (0..ctx.len()).rev() {
        level = level - 1; // As we peel off a module parameter, the context maximum level is reduced by one
        let name = ctx.names[i];
        let domain = quote(db, ctx.types[i].clone(), level);
        let mode = if sort != Sort::Term { Mode::TypeLevel } else { ctx.modes[i] };
        result = db.make_term(TermData::Pi {
            sort: result.sort(),
            domain,
            mode,
            name,
            body: result
        })
    }
    result
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

// fn shift(db: &mut Database, term: Term, amount: usize, cutoff: usize) -> Term {
//     let borrow: &TermData = term.borrow();
//     match borrow.clone() {
//         TermData::Lambda { sort, mode, name, domain, body } => {
//             let domain = shift(db, domain, amount, cutoff);
//             let body = shift(db, body, amount, cutoff + 1);
//             db.make_term(TermData::Lambda { sort, mode, name, domain, body })
//         }
//         TermData::Let { sort, name, let_body, body } => {
//             let let_body = shift(db, let_body, amount, cutoff);
//             let body = shift(db, body, amount, cutoff + 1);
//             db.make_term(TermData::Let { sort, name, let_body, body })
//         }
//         TermData::Pi { sort, mode, name, domain, body } => {
//             let domain = shift(db, domain, amount, cutoff);
//             let body = shift(db, body, amount, cutoff + 1);
//             db.make_term(TermData::Pi { sort, mode, name, domain, body })
//         }
//         TermData::Intersect { name, first, second } => {
//             let first = shift(db, first, amount, cutoff);
//             let second = shift(db, second, amount, cutoff + 1);
//             db.make_term(TermData::Intersect { name, first, second })
//         }
//         TermData::Equality { left, right, anno } => {
//             let left = shift(db, left, amount, cutoff);
//             let right = shift(db, right, amount, cutoff);
//             let anno = shift(db, anno, amount, cutoff);
//             db.make_term(TermData::Equality { left, right, anno })
//         }
//         TermData::Project { variant, body } => {
//             let body = shift(db, body, amount, cutoff);
//             db.make_term(TermData::Project { variant, body })
//         }
//         TermData::Pair { first, second, anno } => {
//             let first = shift(db, first, amount, cutoff);
//             let second = shift(db, second, amount, cutoff);
//             let anno = shift(db, anno, amount, cutoff);
//             db.make_term(TermData::Pair { first, second, anno })
//         }
//         TermData::Separate { equation } => {
//             let equation = shift(db, equation, amount, cutoff);
//             db.make_term(TermData::Separate { equation })
//         }
//         TermData::Refl { input } => {
//             let input = shift(db, input, amount, cutoff);
//             db.make_term(TermData::Refl { input })
//         }
//         TermData::Cast { witness, evidence } => {
//             let witness = shift(db, witness, amount, cutoff);
//             let evidence = shift(db, evidence, amount, cutoff);
//             db.make_term(TermData::Cast { witness, evidence })
//         }
//         TermData::Promote { equation } => {
//             let equation = shift(db, equation, amount, cutoff);
//             db.make_term(TermData::Promote { equation })
//         }
//         TermData::EqInduct { domain, predicate, lhs, rhs, equation, case } => {
//             let domain = shift(db, domain, amount, cutoff);
//             let predicate = shift(db, predicate, amount, cutoff);
//             let lhs = shift(db, lhs, amount, cutoff);
//             let rhs = shift(db, rhs, amount, cutoff);
//             let equation = shift(db, equation, amount, cutoff);
//             let case = shift(db, case, amount, cutoff);
//             db.make_term(TermData::EqInduct { domain, predicate, lhs, rhs, equation, case })
//         }
//         TermData::Apply { sort, mode, fun, arg } => {
//             let fun = shift(db, fun, amount, cutoff);
//             let arg = shift(db, arg, amount, cutoff);
//             db.make_term(TermData::Apply { sort, mode, fun, arg })
//         }
//         TermData::Bound { sort, index } => {
//             let index = if *index < cutoff { index } else { index + amount };
//             db.make_term(TermData::Bound { sort, index })
//         }
//         TermData::Free { .. } => term,
//         TermData::Meta { .. } => term,
//         TermData::InsertedMeta { .. } => term,
//         TermData::Star => term,
//         TermData::SuperStar => term,
//     }
// }

fn unfold_all(db: &mut Database, term : Term) -> Term {
    let borrow: &TermData = term.borrow();
    match borrow.clone() {
        TermData::Lambda { sort, mode, name, domain, body } => {
            let domain = unfold_all(db, domain);
            let body = unfold_all(db, body);
            db.make_term(TermData::Lambda { sort, mode, name, domain, body })
        }
        TermData::Let { sort, name, let_body, body } => {
            let let_body = unfold_all(db, let_body);
            let body = unfold_all(db, body);
            db.make_term(TermData::Let { sort, name, let_body, body })
        }
        TermData::Pi { sort, mode, name, domain, body } => {
            let domain = unfold_all(db, domain);
            let body = unfold_all(db, body);
            db.make_term(TermData::Pi { sort, mode, name, domain, body })
        }
        TermData::Intersect { name, first, second } => {
            let first = unfold_all(db, first);
            let second = unfold_all(db, second);
            db.make_term(TermData::Intersect { name, first, second })
        }
        TermData::Equality { left, right, anno } => {
            let left = unfold_all(db, left);
            let right = unfold_all(db, right);
            let anno = unfold_all(db, anno);
            db.make_term(TermData::Equality { left, right, anno })
        }
        TermData::Project { variant, body } => {
            let body = unfold_all(db, body);
            db.make_term(TermData::Project { variant, body })
        }
        TermData::Pair { first, second, anno } => {
            let first = unfold_all(db, first);
            let second = unfold_all(db, second);
            let anno = unfold_all(db, anno);
            db.make_term(TermData::Pair { first, second, anno })
        }
        TermData::Separate { equation } => {
            let equation = unfold_all(db, equation);
            db.make_term(TermData::Separate { equation })
        }
        TermData::Refl { input } => {
            let input = unfold_all(db, input);
            db.make_term(TermData::Refl { input })
        }
        TermData::Cast { witness, evidence } => {
            let witness = unfold_all(db, witness);
            let evidence = unfold_all(db, evidence);
            db.make_term(TermData::Cast { witness, evidence })
        }
        TermData::Promote { variant, equation, lhs, rhs } => {
            let equation = unfold_all(db, equation);
            let lhs = unfold_all(db, lhs);
            let rhs = unfold_all(db, rhs);
            db.make_term(TermData::Promote { variant, equation, lhs, rhs })
        }
        TermData::Subst { predicate, equation } => {
            let predicate = unfold_all(db, predicate);
            let equation = unfold_all(db, equation);
            db.make_term(TermData::Subst { predicate, equation })
        }
        TermData::Apply { sort, mode, fun, arg } => {
            let fun = unfold_all(db, fun);
            let arg = unfold_all(db, arg);
            db.make_term(TermData::Apply { sort, mode, fun, arg })
        }
        TermData::Bound { .. } => term,
        TermData::Free { id, .. } => {
            if let Some(def) = db.lookup_def(&id) {
                let result = def;
                let result = quote(db, result, 0.into());
                unfold_all(db, result)
            } else { term }
        }
        TermData::Meta { sort, name } => todo!(),
        TermData::InsertedMeta { sort, name, mask } => todo!(),
        TermData::Star => term,
        TermData::SuperStar => term,
    }
}
