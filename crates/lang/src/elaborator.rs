
// use std::rc::Rc;
// use std::sync::Arc;
// use std::time;

// use colored::Colorize;
// use thiserror::Error;
// use miette::{Diagnostic, SourceSpan};
// use unicode_segmentation::UnicodeSegmentation;

// use cedille2_core::utility::*;
// use crate::syntax;
// use crate::rewriter;
// use cedille2_core::term;
// use cedille2_core::value::{Value, ValueEx, Closure, LazyValue, EnvEntry, Environment, EnvBound};
// use cedille2_core::database::Database;
// use crate::database::{DatabaseExt};
// use crate::error::CedilleError;

// type Span = (usize, usize);

// #[derive(Debug, Error, Diagnostic)]
// pub enum ElabError {
//     #[error("Inconvertible")]
//     #[diagnostic()]
//     Inconvertible {
//         #[source_code]
//         src: Arc<String>,
//         #[label("{left} ~= {right}")]
//         span: SourceSpan,
//         left: String,
//         right: String
//     },
//     #[error("Convertible")]
//     #[diagnostic()]
//     Convertible {
//         span: Span,
//     },
//     #[error("Open Term")]
//     #[diagnostic()]
//     OpenTerm {

//     },
//     #[error("Expected Term")]
//     #[diagnostic()]
//     ExpectedTerm { span: Span },
//     #[error("Expected Function Type")]
//     #[diagnostic()]
//     ExpectedFunctionType,
//     #[error("Expected Equality Type")]
//     #[diagnostic()]
//     ExpectedEqualityType,
//     #[error("Expected Intersection Type")]
//     #[diagnostic()]
//     ExpectedIntersectionType {
//         #[source_code]
//         src: Arc<String>,
//         #[label("Type must be a intersection but found {inferred_type}")]
//         span: SourceSpan,
//         inferred_type: String,
//     },
//     #[error("Mode Mismatch")]
//     #[diagnostic()]
//     ModeMismatch {
//         #[source_code]
//         src: Arc<String>,
//         #[label("Expected {expected} but found {provided}")]
//         span: SourceSpan,
//         expected: Mode,
//         provided: Mode
//     },
//     #[error("Hole")]
//     #[diagnostic(
//         help("Context at hole: {context}")
//     )]
//     Hole {
//         #[source_code]
//         src: Arc<String>,
//         #[label("Expected {expected_type}")]
//         span: SourceSpan,
//         expected_type: String,
//         context: String
//     },
//     #[error("Definition Collision")]
//     #[diagnostic()]
//     DefinitionCollision {
//         #[source_code]
//         src: Arc<String>,
//         #[label("Defined here")]
//         span: SourceSpan,
//     },
//     #[error("Missing Name")]
//     #[diagnostic()]
//     MissingName {
//         #[source_code]
//         source_code: Arc<String>,
//         #[label("Identifier undefined")]
//         span: SourceSpan
//     },
//     #[error("Intersection Inconvertible")]
//     #[diagnostic()]
//     IntersectionInconvertible {
//         #[source_code]
//         src: Arc<String>,
//         #[label("(lhs) Must be convertible with")]
//         left: SourceSpan,
//         #[label("(rhs) this")]
//         right: SourceSpan,
//     },
//     #[error("Inference Failed")]
//     #[diagnostic()]
//     InferenceFailed {
//         #[source_code]
//         src: Arc<String>,
//         #[label("unable to infer type of term")]
//         span: SourceSpan
//     },
//     #[error("Unsupported Projection")]
//     #[diagnostic()]
//     UnsupportedProjection,
//     #[error("Rewrite Failed")]
//     #[diagnostic()]
//     RewriteFailed,
//     #[error("Opaque definitions must have a valid type or kind")]
//     #[diagnostic()]
//     OpaqueMissingAnnotation,
//     #[error("Unknown error!")]
//     #[diagnostic()]
//     Unknown
// }

// #[derive(Debug, Clone)]
// pub struct Context {
//     env: Environment,
//     env_mask: Vec<EnvBound>,
//     pub names: im_rc::Vector<Symbol>,
//     pub types: im_rc::Vector<Rc<Value>>,
//     pub sorts: im_rc::Vector<Sort>,
//     pub modes: im_rc::Vector<Mode>,
//     pub module: Symbol,
//     pub mode: Mode,
//     pub sort: Sort
// }

// impl Context {
//     pub fn new(module: Symbol) -> Context {
//         Context {
//             env: Environment::new(),
//             env_mask: Vec::new(),
//             names: im_rc::Vector::new(),
//             types: im_rc::Vector::new(),
//             sorts: im_rc::Vector::new(),
//             modes: im_rc::Vector::new(),
//             module,
//             mode: Mode::Free,
//             sort: Sort::Unknown
//         }
//     }

//     pub fn phase_shift(mut self, mode: Mode, sort: Sort) -> Context {
//         self.mode = mode;
//         self.sort = sort;
//         // If we phase shift into an erased context, then all currently erased variables can be treated as relevant
//         if mode == Mode::Erased {
//             self.modes = self.modes.iter().map(|_| Mode::Free).collect::<im_rc::Vector<_>>();
//         }
//         self
//     }

//     pub fn bind_sort(&self, name: Symbol, sort: Sort) -> Context {
//         let mut result = self.clone();
//         result.names.push_back(name);
//         result.sorts.push_back(sort);
//         result
//     }

//     pub fn bind(&self, db: &Database, name: Symbol, mode: Mode, value_type: Rc<Value>) -> Context {
//         let mut result = self.clone();
//         let level = self.env_lvl();
//         let sort = value_type.sort(db).demote();
//         let value = LazyValue::computed(Value::variable(sort, level));
//         log::trace!("\n{}\n{} {} {} {} {}", self.env, "bind".bright_blue(), name, value, ":".bright_blue(), value_type);
//         result.env.push_back(EnvEntry::new(name, mode, value));
//         result.env_mask.push(EnvBound::Bound);
//         result.names.push_back(name);
//         result.sorts.push_back(sort);
//         result.types.push_back(value_type);
//         result.modes.push_back(mode);
//         result
//     }

//     pub fn define(&self, db: &Database, name: Symbol, mode: Mode, value: LazyValue, value_type: Rc<Value>) -> Context {
//         let mut result = self.clone();
//         log::trace!("\n{}\n{} {} {} {} {}", self.env, "define".bright_blue(), name, value, ":".bright_blue(), value_type);
//         result.env.push_back(EnvEntry::new(name, mode, value));
//         result.env_mask.push(EnvBound::Defined);
//         result.names.push_back(name);
//         result.sorts.push_back(value_type.sort(db).demote());
//         result.types.push_back(value_type);
//         result.modes.push_back(mode);
//         result
//     }

//     pub fn to_string(&self, db: &Database) -> String {
//         let mut result = String::new();
//         for i in (0..self.len()).rev() {
//             result.push('\n');
//             let ty = self.types[i].clone();
//             let type_string = ty.quote(db, self.env_lvl())
//                 .to_string_with_context(self.names.clone());
//             let mode_prefix = if self.modes[i] == Mode::Erased { "-" } else { "" };
//             result.push_str(format!("{}{}: {}", mode_prefix, self.names[i], type_string).as_str());
//         }
//         result
//     }

//     pub fn env(&self) -> Environment { self.env.clone() }

//     pub fn env_mask(&self) -> Vec<EnvBound> { self.env_mask.clone() }

//     pub fn env_lvl(&self) -> Level { self.env.len().into() }

//     pub fn len(&self) -> usize { self.names.len() }
// }

// pub fn elaborate(db: &mut Database, module: Symbol, syntax: &syntax::Module) -> Result<(), CedilleError> {
//     let mut errors = vec![];

//     let ctx = elaborate_module_params(db, Context::new(module), &syntax.params)?;
//     for import in syntax.header_imports.iter() {
//         elaborate_import(db, ctx.clone(), import)?;
//     }

//     for decl in syntax.decls.iter() {
//         match elaborate_decl(db, ctx.clone(), decl) {
//             Ok(_) =>  { },
//             Err(error) => errors.push(error)
//         }
//     }

//     if errors.is_empty() { Ok(()) }
//     else { Err(CedilleError::Collection(errors)) }
// }

// fn elaborate_module_params(db: &mut Database, ctx: Context, params: &[syntax::Parameter]) -> Result<Context, ElabError> {
//     let mut ctx = ctx;
//     let mut param_results = vec![];
//     for param in params.iter() {
//         let (body_elabed, _) = infer(db, ctx.clone(), &param.body)?;
//         let body_value = Value::eval(db, ctx.module, ctx.env(), body_elabed.clone());
//         param_results.push(term::Parameter { name: param.name, mode: param.mode, body: body_elabed });
//         ctx = ctx.bind(db, param.name, param.mode, body_value);
//     }
//     db.set_params(ctx.module, param_results);
//     Ok(ctx)
// }

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
//             let value = Value::eval(db, module, Environment::new(), erased);
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

// fn elaborate_import_args(db: &mut Database
//     , ctx: Context
//     , args: &[(Mode, syntax::Term)]
//     , params: &[term::Parameter])
//     -> Result<Vec<(Mode, Rc<Value>)>, ElabError>
// {
//     let mut ctx = ctx;
//     let mut result = vec![];
//     for i in 0..args.len() {
//         if let Some(term::Parameter { name, mode, body }) = params.get(i) {
//             let ty = Value::eval(db, ctx.module, ctx.env(), body.clone());
//             let (arg_mode, arg) = &args[i];
//             let arg_elabed = check(db, ctx.clone(), arg, ty.clone())?;

//             if mode != arg_mode && arg_elabed.sort() == Sort::Term {
//                 return Err(ElabError::ModeMismatch { 
//                     src: db.text(ctx.module), 
//                     span: source_span(db, ctx.module, arg.span()), 
//                     expected: *mode,
//                     provided: *arg_mode
//                 })
//             }
//             let arg_value = Value::eval(db, ctx.module, ctx.env(), arg_elabed);
//             let arg_mode = if ty.sort(db) == Sort::Type { *arg_mode } else { Mode::Erased }; 
//             result.push((arg_mode, arg_value.clone()));
//             let value = LazyValue::computed(arg_value);
//             ctx = ctx.define(db, *name, *mode, value, ty);
//         } else {
//             // TODO: add a reasonable error
//             return Err(ElabError::Unknown)
//         }
//     }
//     Ok(result)
// }

// fn elaborate_import(db: &mut Database, ctx: Context, import: &syntax::Import) -> Result<(), CedilleError> {
//     let import_symbol = db.resolve_import_symbol(ctx.module, import.path)?;
//     db.load_module(import_symbol)?; // Imported module may not be loaded at all, which means no parameters
//     let params = db.lookup_params(import_symbol);
//     let args = elaborate_import_args(db, ctx.clone(), &import.args, &params)?;
//     db.load_import(ctx.module, import, args)?;
//     Ok(())
// }

// fn elaborate_opaque_define_term(db: &mut Database, ctx: Context, def: &syntax::DefineTerm) -> Result<term::Decl, ElabError> {
//     if let Some(anno) = &def.anno {
//         let anno_sort = infer_sort(db, ctx.clone(), anno)?;
//         let ctx = ctx.phase_shift(Mode::Free, anno_sort);
//         let anno_classifier = Value::classifier(anno_sort).map_err(|_| ElabError::Unknown)?;
//         let ty = check(db, ctx, anno, anno_classifier)?;
//         let name = def.name;
//         let id = Id::from(def.name);
//         let body = Rc::new(term::Term::Free {
//             sort: anno_sort,
//             id
//         });
//         Ok(term::Decl { name, ty, body })
//     } else {
//         Err(ElabError::OpaqueMissingAnnotation)
//     }
// }

// fn elaborate_define_term(db: &mut Database, ctx: Context, def: &syntax::DefineTerm) -> Result<term::Decl, ElabError> {
//     let (name, ty, body) = if let Some(anno) = &def.anno {
//         let anno_sort = infer_sort(db, ctx.clone(), anno)?;
//         let anno_classifier = Value::classifier(anno_sort).map_err(|_| ElabError::Unknown)?;
//         let ctx = ctx.phase_shift(Mode::Free, anno_sort);
//         let anno_elabed = check(db, ctx.clone(), anno, anno_classifier)?;
//         let anno_value = Value::eval(db, ctx.module, ctx.env(), anno_elabed.clone());
//         let ctx = ctx.phase_shift(Mode::Free, anno_sort.demote());
//         let body = check(db, ctx, &def.body, anno_value)?;
//         (def.name, anno_elabed, body)
//     } else {
//         let (body, inferred) = infer(db, ctx.clone(), &def.body)?;
//         let ty = Rc::new(inferred.quote(db, ctx.env_lvl()));
//         (def.name, ty, body)
//     };
//     Ok(term::Decl { name, ty, body })
// }

// fn check(db: &mut Database, ctx: Context, term: &syntax::Term, ty: Rc<Value>) -> Result<Rc<term::Term>, ElabError> {
//     fn check_lambda(db: &mut Database
//         , ctx: Context
//         , index: usize
//         , vars: &[syntax::LambdaVar]
//         , body: &syntax::Term
//         , ty: Rc<Value>)
//         -> Result<Rc<term::Term>, ElabError>
//     {
//         if let Some(var) = vars.get(index) {
//             let ty = Value::unfold_to_head(db, ty);
//             match ty.as_ref() {
//                 Value::Pi { sort:type_sort, mode:type_mode, domain, closure, .. } => {
//                     let sort = type_sort.demote();
//                     if sort == Sort::Term && var.mode != *type_mode {
//                         return Err(ElabError::ModeMismatch {
//                             src: db.text(ctx.module),
//                             span: source_span(db, ctx.module, body.span()),
//                             expected: *type_mode,
//                             provided: var.mode
//                         })
//                     }
//                     let name = var.var.unwrap_or_default();
//                     if let Some(ref anno) = var.anno {
//                         let span = anno.span();
//                         let anno_sort = infer_sort(db, ctx.clone(), anno)?;
//                         let anno_classifier = Value::classifier(anno_sort).map_err(|_| ElabError::Unknown)?;
//                         let anno_ctx = ctx.clone().phase_shift(Mode::Free, anno_sort);
//                         let anno_elabed = check(db, anno_ctx, anno, anno_classifier)?;
//                         let anno_value = Value::eval(db, ctx.module, ctx.env(), anno_elabed);
//                         unify(db, ctx.clone(), span, &anno_value, domain)?;
//                     }
//                     let value = LazyValue::computed(Value::variable(domain.sort(db), ctx.env_lvl()));
//                     let ctx = ctx.bind(db, name, *type_mode, domain.clone());
//                     let body_type = closure.eval(db, EnvEntry::new(name, var.mode, value));
//                     let body_elabed = check_lambda(db, ctx, index + 1, vars, body, body_type)?;
//                     Ok(Rc::new(term::Term::Lambda {
//                         sort,
//                         domain_sort: domain.sort(db).demote(),
//                         mode: var.mode,
//                         name,
//                         body: body_elabed
//                     }))
//                 }
//                 _ => Err(ElabError::ExpectedFunctionType)
//             }
//         } else { check(db, ctx, body, ty) }
//     }

//     let ty_folded = ty.clone();
//     let ty = Value::unfold_to_head(db, ty);
//     log::trace!("\n{}\n  {}\n{} {}", ctx.env(), term.as_str(db.text_ref(ctx.module)), "<=".bright_blue(), ty);
//     match (term, ty.as_ref()) {
//         (syntax::Term::Lambda { vars, body, .. }, _) =>
//             check_lambda(db, ctx, 0, vars, body, ty),

//         (syntax::Term::Let { mode, def, body, .. }, _) =>
//         {
//             let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
//                 let anno_ctx = ctx.clone().phase_shift(Mode::Free, Sort::Type);
//                 let anno_elabed = check(db, anno_ctx, anno, Value::star())?;
//                 let anno_value = Value::eval(db, ctx.module, ctx.env(), anno_elabed.clone());
//                 (anno_elabed, anno_value)
//             } else { infer(db, ctx.clone(), &def.body)? };
//             let def_body_elabed = check(db, ctx.clone(), &def.body, anno_value.clone())?;
//             let def_body_value = LazyValue::new(ctx.module, ctx.env(), def_body_elabed.clone());
//             let ctx = ctx.define(db, def.name, *mode, def_body_value, anno_value);
//             let body_elabed = check(db, ctx, body, ty)?;
//             let result_let = Rc::new(term::Term::Let {
//                 sort: body_elabed.sort(),
//                 mode: *mode,
//                 name: def.name,
//                 let_body: def_body_elabed,
//                 body: body_elabed
//             });
//             let result = term::Term::Annotate { 
//                 anno: anno_elabed,
//                 body: result_let
//             };
//             Ok(Rc::new(result))
//         }

//         (syntax::Term::Intersect { span, first, second },
//             Value::IntersectType { name, first:type1, second:type2 }) =>
//         {
//             let first_elabed = check(db, ctx.clone(), first, type1.clone())?;
//             let first_value = Value::eval(db, ctx.module, ctx.env(), first_elabed.clone());
//             let closure_arg = EnvEntry::new(*name, Mode::Free, LazyValue::computed(first_value.clone()));
//             let type2 = type2.eval(db, closure_arg);
//             let second_elabed = check(db, ctx.clone(), second, type2)?;
//             let second_value = Value::eval(db, ctx.module, ctx.env(), second_elabed.clone());
//             unify(db, ctx.clone(), *span, &first_value, &second_value)
//                 .map_err(|_| ElabError::IntersectionInconvertible {
//                         src: db.text(ctx.module),
//                         left: source_span(db, ctx.module, first.span()),
//                         right: source_span(db, ctx.module, second.span())
//                     })?;
//             Ok(Rc::new(term::Term::Intersect {
//                 first: first_elabed,
//                 second: second_elabed
//             }))
//         }

//         (syntax::Term::Reflexivity { span, erasure, .. },
//             Value::Equality { left, right }) =>
//         {
//             let erasure_elabed = if let Some(t) = erasure { erase(db, ctx.clone(), t)? }
//                 else { Rc::new(term::Term::id()) };
//             unify(db, ctx, *span, left, right)?;
//             Ok(Rc::new(term::Term::Refl { erasure: erasure_elabed }))
//         }

//         (syntax::Term::Separate { span, equation, .. }, _) =>
//         {
//             let equation_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
//             let (equation_elabed, equality) = infer(db, equation_ctx, equation)?;
//             let equality = Value::unfold_to_head(db, equality);
//             match equality.as_ref() {
//                 Value::Equality { left, right } => {
//                     if unify(db, ctx, *span, left, right).is_ok() {
//                         Err(ElabError::Convertible { span:*span })
//                     } else if !left.is_closed(db) || !right.is_closed(db) {
//                         Err(ElabError::OpenTerm { })
//                     } else {
//                         Ok(Rc::new(term::Term::Separate { equation: equation_elabed }))
//                     }
//                 },
//                 _ => Err(ElabError::ExpectedEqualityType)
//             }
//         }

//         (syntax::Term::Rewrite { span, equation, guide, body, occurrence, .. },
//             _) =>
//         {
//             let equation_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
//             let (equation_elabed, equality) = infer(db, equation_ctx, equation)?;
//             let equality = Value::unfold_to_head(db, equality);
//             match equality.as_ref() {
//                 Value::Equality { left, right } => {
//                     let guide_name = guide.as_ref().map(|g| g.name).unwrap_or_default();
//                     let guide_ctx = ctx
//                         .bind(db, guide_name, Mode::Free, Value::top_type())
//                         .phase_shift(Mode::Free, Sort::Type);
//                     let guide_ty_elabed = if let Some(guide) = guide {
//                         check(db, guide_ctx, &guide.ty, Value::star())?
//                     } else {
//                         rewriter::match_term(db, guide_ctx, *occurrence, left, &ty)?
//                     };
//                     let guide_ty_closure = Closure::new(ctx.module, ctx.env(), guide_ty_elabed.clone());

//                     unify(db
//                         , ctx.clone()
//                         , *span
//                         , &guide_ty_closure.eval(db, EnvEntry::new(guide_name, Mode::Free, left))
//                         , &ty)?;

//                     let body_elabed = check(db
//                         , ctx.clone()
//                         , body
//                         , guide_ty_closure.eval(db, EnvEntry::new(guide_name, Mode::Free, right)))?;

//                     Ok(Rc::new(term::Term::Rewrite {
//                         equation: equation_elabed,
//                         guide: term::RewriteGuide {
//                             name: guide_name,
//                             hint: Rc::new(right.quote(db, ctx.env_lvl())),
//                             ty: guide_ty_elabed
//                         },
//                         body: body_elabed
//                     }))
//                 }
//                 _ => Err(ElabError::ExpectedEqualityType)
//             }
//         }

//         (syntax::Term::Cast { equation, input, erasure, ..}, _) =>
//         {
//             let input_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
//             let input_elabed = check(db, input_ctx, input, ty)?;
//             let input_value = Value::eval(db, ctx.module, ctx.env(), input_elabed.clone());
//             let erasure_elabed = erase(db, ctx.clone(), erasure)?;
//             let erasure_value = Value::eval(db, ctx.module, ctx.env(), erasure_elabed.clone());
//             let equality_type = Value::equality(input_value, erasure_value);
//             let equation_ctx = ctx.phase_shift(Mode::Erased, Sort::Term);
//             let equation_elabed = check(db, equation_ctx, equation, equality_type)?;
//             Ok(Rc::new(term::Term::Cast { 
//                 equation: equation_elabed,
//                 input: input_elabed,
//                 erasure: erasure_elabed
//             }))
//         }

//         (syntax::Term::Hole { span, .. }, _) => {
//             //println!("\n{}\n  {}\n{} {}", ctx.env(), term.as_str(db.text_ref(ctx.module)), "<=".bright_blue(), ty);
//             // let data = HoleData {
//             //     span: source_span(db, ctx.module, *span),
//             //     expected_type: ty_folded,
//             //     context: ctx.clone()
//             // };
//             // let sort = ty.sort(db).demote();
//             // let hole = fresh_hole(db, ctx, data, sort);
//             // Ok(hole)
//             unimplemented!()
//         }

//         (syntax::Term::Omission { .. }, _) => Ok(Rc::new(fresh_meta(db, ctx, ty.sort(db).demote()))),

//         // change direction
//         _ => {
//             let (mut result, mut inferred_type) = infer(db, ctx.clone(), term)?;

//             loop {
//                 match (result.as_ref(), inferred_type.as_ref()) {
//                     (term::Term::Free { sort, .. }, Value::Pi { mode, name, domain, closure, .. })
//                     if *mode == Mode::Erased && *sort == Sort::Term =>
//                     {
//                         let sort = domain.sort(db).demote();
//                         let meta = Rc::new(fresh_meta(db, ctx.clone(), sort));
//                         let meta_value = Value::eval(db, ctx.module, ctx.env(), meta.clone());
//                         result = Rc::new(term::Term::Apply {
//                             sort,
//                             mode: *mode,
//                             fun: result,
//                             arg: meta
//                         });
//                         inferred_type = closure.eval(db, EnvEntry::new(*name, *mode, meta_value));
//                     }
//                     _ => break
//                 }
//             }

//             unify(db, ctx, term.span(), &ty, &inferred_type)?;
//             Ok(result)
//         }
//     }
// }

// fn infer(db: &mut Database, ctx: Context, term: &syntax::Term) -> Result<(Rc<term::Term>, Rc<Value>), ElabError> {
//     let module = ctx.module;
//     let sort = infer_sort(db, ctx.clone(), term)?;
//     let result = match term {
//         syntax::Term::Pi { mode
//             , var
//             , domain
//             , body
//             , .. } =>
//         {
//             let (mode, name) = (*mode, var.unwrap_or_default());
//             let domain_sort = infer_sort(db, ctx.clone(), domain)?;
//             let domain_classifier = Value::classifier(domain_sort).map_err(|_| ElabError::Unknown)?;
//             let domain_elabed = check(db, ctx.clone(), domain, domain_classifier)?;
//             let domain_value = Value::eval(db, module, ctx.env(), domain_elabed.clone());
//             let ctx = ctx.bind(db, name, mode, domain_value);
//             let body_classifier = Value::classifier(sort).map_err(|_| ElabError::Unknown)?;
//             let body_elabed = check(db, ctx, body, body_classifier.clone())?;
//             let result = Rc::new(term::Term::Pi { 
//                 sort,
//                 mode,
//                 name,
//                 domain: domain_elabed,
//                 body: body_elabed
//             });
//             Ok((result, body_classifier))
//         }

//         syntax::Term::IntersectType { var, first, second, .. } => {
//             let first_elabed = check(db, ctx.clone(), first, Value::star())?;
//             let first_value = Value::eval(db, module, ctx.env(), first_elabed.clone());
//             let name = var.unwrap_or_default();
//             let ctx = ctx.bind(db, name, Mode::Free, first_value);
//             let second_elabed = check(db, ctx, second, Value::star())?;
//             let result = Rc::new(term::Term::IntersectType {
//                 name,
//                 first: first_elabed,
//                 second: second_elabed
//             });
//             Ok((result, Value::star()))
//         }

//         syntax::Term::Equality { left, right, .. } => {
//             let left_elabed = erase(db, ctx.clone(), left)?;
//             let right_elabed = erase(db, ctx.clone(), right)?;
//             let result = Rc::new(term::Term::Equality {
//                 left: left_elabed,
//                 right: right_elabed
//             });
//             Ok((result, Value::star()))
//         }

//         syntax::Term::Symmetry { equation, .. } => {
//             let (equation_elabed, eq_ty) = infer(db, ctx.clone(), equation)?;
//             match eq_ty.as_ref() {
//                 Value::Equality { left, right } => {
//                     let result_ty = Rc::new(Value::Equality { left:right.clone(), right:left.clone() });
//                     Ok((equation_elabed, result_ty))
//                 }
//                 _ => Err(ElabError::ExpectedEqualityType)
//             }
//         }

//         syntax::Term::Let { mode, def, body, .. } => {
//             let (anno_elabed, anno_value) = if let Some(anno) = &def.anno {
//                 let anno_ctx = ctx.clone().phase_shift(Mode::Free, Sort::Type);
//                 let anno_elabed = check(db, anno_ctx, anno, Value::star())?;
//                 let anno_value = Value::eval(db, module, ctx.env(), anno_elabed.clone());
//                 (anno_elabed, anno_value)
//             } else { infer(db, ctx.clone(), &def.body)? };
//             let def_body_elabed = check(db, ctx.clone(), &def.body, anno_value.clone())?;
//             let def_body_value = LazyValue::new(module, ctx.env(), def_body_elabed.clone());
//             let ctx = ctx.define(db, def.name, *mode, def_body_value, anno_value);
//             let (body_elabed, type_value) = infer(db, ctx, body)?;
//             let result_let = Rc::new(term::Term::Let {
//                 sort,
//                 mode: *mode,
//                 name: def.name,
//                 let_body: def_body_elabed,
//                 body: body_elabed
//             });
//             let result = Rc::new(term::Term::Annotate { 
//                 anno: anno_elabed,
//                 body: result_let
//             });
//             Ok((result, type_value))
//         }

//         syntax::Term::Variable { span, id, .. } => {
//             let (var_type, level, mode) = lookup_type(db, &ctx, *span, id)?;
//             //dbg!(id, mode, ctx.mode, ctx.sort);
//             if mode == Mode::Erased && ctx.mode == Mode::Free && ctx.sort == Sort::Term {
//                 Err(ElabError::ModeMismatch { 
//                     src: db.text(ctx.module),
//                     span: source_span(db, ctx.module, *span),
//                     expected: ctx.mode,
//                     provided: mode
//                 })
//             } else if let Some(level) = level {
//                 let index = level.to_index(ctx.env.len());
//                 Ok((Rc::new(term::Term::Bound { sort, index }), var_type))
//             } else {
//                 Ok((Rc::new(term::Term::Free { sort, id:id.clone() }), var_type))
//             }
//         }

//         syntax::Term::Apply { span, mode, fun, arg, .. } => {
//             let arg_sort = infer_sort(db, ctx.clone(), arg)?;
//             let (mut fun_elabed, mut fun_type) = infer(db, ctx.clone(), fun)?;

//             loop {
//                 fun_type = Value::unfold_to_head(db, fun_type);
//                 match fun_type.as_ref() {
//                     Value::Pi { mode:type_mode, name, domain, closure, .. }
//                     if (*mode == Mode::Free && *type_mode == Mode::Erased && arg_sort != Sort::Unknown)
//                     || (*mode == Mode::Erased && *type_mode == Mode::Erased && arg_sort == Sort::Term && domain.sort(db) == Sort::Kind) =>
//                     {
//                         let arg_sort = domain.sort(db).demote();
//                         let meta = Rc::new(fresh_meta(db, ctx.clone(), arg_sort));
//                         fun_elabed = Rc::new(term::Term::Apply {
//                             sort,
//                             mode: *type_mode,
//                             fun: fun_elabed,
//                             arg: meta.clone()
//                         });
//                         let arg = LazyValue::new(module, ctx.env(), meta);
//                         let arg = EnvEntry::new(*name, *type_mode, arg);
//                         fun_type = closure.eval(db, arg);
//                     },
//                     _ => break
//                 }
//             }

//             fun_type = Value::unfold_to_head(db, fun_type);
//             let (name, type_mode, domain, closure) = match fun_type.as_ref() {
//                 Value::Pi { mode:type_mode, name, domain, closure, .. } => {
//                     if sort == Sort::Term && *mode != *type_mode {
//                         return Err(ElabError::ModeMismatch {
//                             src: db.text(ctx.module),
//                             span: source_span(db, ctx.module, arg.span()),
//                             expected: *type_mode,
//                             provided: *mode
//                         });
//                     }
//                     (*name, *type_mode, domain.clone(), closure.clone())
//                 },
//                 _ => {
//                     let name = Symbol::from("x");
//                     let sort = Sort::Unknown;
//                     let domain = Rc::new(fresh_meta(db, ctx.clone(), sort));
//                     let domain = Value::eval(db, ctx.module, ctx.env(), domain);
//                     let meta = Rc::new(fresh_meta(db, ctx.bind(db, name, Mode::Free, domain.clone()), sort));
//                     let closure = Closure::new(ctx.module, ctx.env(), meta);
//                     let candidate_type = Value::pi(sort, *mode, name, domain.clone(), closure.clone());
//                     unify(db, ctx.clone(), *span, &fun_type, &candidate_type)?;
//                     (name, *mode, domain, closure)
//                 }
//             };

//             let ctx = ctx.clone().phase_shift(*mode, ctx.sort);
//             let arg_elabed = check(db, ctx.clone(), arg, domain)?;
//             let arg_value = LazyValue::new(module, ctx.env(), arg_elabed.clone());
//             let closure_arg = EnvEntry::new(name, type_mode, arg_value);
//             let result_type = closure.eval(db, closure_arg);
//             let result = Rc::new(term::Term::Apply {
//                 sort,
//                 mode: *mode,
//                 fun: fun_elabed,
//                 arg: arg_elabed
//             });
//             Ok((result, result_type))
//         }

//         syntax::Term::Project { span, variant, body, .. } => {
//             let (body_elabed, body_type) = infer(db, ctx.clone(), body)?;
//             let body_type_unfolded = Value::unfold_to_head(db, body_type.clone());
//             match body_type_unfolded.as_ref() {
//                 Value::IntersectType { name, first, second } => {
//                     let first_proj = Rc::new(term::Term::Project { variant:1, body: body_elabed.clone() });
//                     let first_value = Value::eval(db, module, ctx.env(), first_proj.clone());
//                     match variant {
//                         1 => Ok((first_proj, first.clone())),
//                         2 => {
//                             let second_proj = Rc::new(term::Term::Project { variant:2, body: body_elabed });
//                             let closure_arg = EnvEntry::new(*name, Mode::Free, LazyValue::computed(first_value));
//                             let result_type = second.eval(db, closure_arg);
//                             Ok((second_proj, result_type))
//                         }
//                         _ => Err(ElabError::UnsupportedProjection)
//                     }
//                 },
//                 _ => Err(ElabError::ExpectedIntersectionType {
//                     src: db.text(ctx.module),
//                     span: source_span(db, ctx.module, *span),
//                     inferred_type: body_type.quote(db, ctx.env_lvl()).to_string()
//                 })
//             }
//         }

//         syntax::Term::Cast { equation, input, erasure, .. } => {
//             let input_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
//             let (input_elabed, result_type) = infer(db, input_ctx, input)?;
//             let input_value = Value::eval(db, module, ctx.env(), input_elabed.clone());
//             let erasure_elabed = erase(db, ctx.clone(), erasure)?;
//             let erasure_value = Value::eval(db, module, ctx.env(), erasure_elabed.clone());
//             let equality_type = Value::equality(input_value, erasure_value);
//             let equation_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Term);
//             let equation_elabed = check(db, equation_ctx, equation, equality_type)?;
//             let result = Rc::new(term::Term::Cast { 
//                 equation: equation_elabed,
//                 input: input_elabed,
//                 erasure: erasure_elabed
//             });
//             Ok((result, result_type))
//         }

//         syntax::Term::Star { .. } => Ok((Rc::new(term::Term::Star), Value::super_star())),

//         syntax::Term::Omission { .. } => {
//             let sort = Sort::Unknown;
//             let ty_meta = Rc::new(fresh_meta(db, ctx.clone(), sort));
//             let ty = Value::eval(db, module, ctx.env(), ty_meta);
//             let term = Rc::new(fresh_meta(db, ctx.clone(), sort));
//             Ok((term, ty))
//         }

//         syntax::Term::Annotate { anno, body, .. } => {
//             let anno_ctx = ctx.clone().phase_shift(Mode::Erased, Sort::Type);
//             let anno_elabed = check(db, anno_ctx, anno, Value::star())?;
//             let anno_value = Value::eval(db, module, ctx.env(), anno_elabed.clone());
//             let body_elabed = check(db, ctx.clone(), body, anno_value.clone())?;
//             let result = Rc::new(term::Term::Annotate {
//                 anno: anno_elabed,
//                 body: body_elabed
//             });
//             Ok((result, anno_value))
//         }

//         _ => {
//             Err(ElabError::InferenceFailed {
//                 src: db.text(module),
//                 span: source_span(db, module, term.span())
//             })
//         }
//     };
//     if let Ok((_, ref inferred_type)) = result {
//         log::trace!("\n{}\n  {}\n{} {}", ctx.env(), term.as_str(db.text_ref(module)), "=>".bright_blue(), inferred_type);
//     }
//     result
// }

// // If something is represented at the level of values (i.e. abstractions and applications) then we do not want to
// // erase it here. Convertibility modulo erasure is handled in values, and erasing it here just causes problems with
// // indices and other things.
// pub fn erase(db: &mut Database, ctx: Context, term: &syntax::Term) -> Result<Rc<term::Term>, ElabError> {
//     use syntax::Term;
//     fn erase_lambda(db: &mut Database
//         , ctx: Context
//         , index: usize
//         , vars: &[syntax::LambdaVar] 
//         , body: &syntax::Term)
//         -> Result<Rc<term::Term>, ElabError>
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
//                 mode: *mode,
//                 name: def.name,
//                 let_body,
//                 body
//             }))
//         },
//         Term::Pi { .. }
//         | Term::IntersectType { .. }
//         | Term::Equality { .. } => Err(ElabError::ExpectedTerm { span:term.span() }),
//         Term::Rewrite { body, .. } => erase(db, ctx, body),
//         Term::Annotate { body, .. } => erase(db, ctx, body),
//         Term::Project { body, .. } => erase(db, ctx, body),
//         Term::Symmetry { .. } => unreachable!(),
//         Term::Intersect { first, .. } => erase(db, ctx, first),
//         Term::Separate { .. } => Ok(Rc::new(term::Term::id())),
//         Term::Reflexivity { erasure, .. } => {
//             if let Some(erasure) = erasure { erase(db, ctx, erasure) }
//             else { Ok(Rc::new(term::Term::id())) }
//         },
//         Term::Cast { erasure, .. } => erase(db, ctx, erasure),
//         Term::Induct { .. } => todo!(),
//         Term::Match { .. } => todo!(),
//         Term::Apply { mode, fun, arg, .. } => {
//             let (mode, sort) = (*mode, Sort::Term);
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
//         Term::Star { .. } => Err(ElabError::ExpectedTerm { span:term.span() }),
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
//     }
// }

// fn infer_sort(db: &Database, ctx: Context, term: &syntax::Term) -> Result<Sort, ElabError> {
//     let result: Sort = match term {
//         syntax::Term::Lambda { vars, body, .. } => {
//             let mut ctx = ctx;
//             for var in vars {
//                 let name = var.var.unwrap_or_default();
//                 if let Some(anno) = &var.anno {
//                     let anno_sort = infer_sort(db, ctx.clone(), anno)?.demote();
//                     ctx = ctx.bind_sort(name, anno_sort);
//                 } else {
//                     ctx = ctx.bind_sort(name, Sort::Unknown);
//                 }
//             }
//             infer_sort(db, ctx, body)?
//         }
//         syntax::Term::Let { def, body, .. } => {
//             let def_sort = infer_sort(db, ctx.clone(), &def.body)?;
//             let ctx = ctx.bind_sort(def.name, def_sort);
//             infer_sort(db, ctx, body)?
//         }
//         syntax::Term::Pi { var, domain, body, .. } => {
//             let name = var.unwrap_or_default();
//             let domain_sort = infer_sort(db, ctx.clone(), domain)?.demote();
//             let ctx = ctx.bind_sort(name, domain_sort);
//             infer_sort(db, ctx, body)?
//         }
//         syntax::Term::IntersectType { .. }
//         | syntax::Term::Equality { .. } => Sort::Type,
//         syntax::Term::Rewrite { .. } => Sort::Term,
//         syntax::Term::Annotate { body, .. } => infer_sort(db, ctx, body)?,
//         syntax::Term::Project { .. } => Sort::Term,
//         syntax::Term::Symmetry { .. }
//         | syntax::Term::Intersect { .. }
//         | syntax::Term::Separate { .. }
//         | syntax::Term::Reflexivity { .. }
//         | syntax::Term::Cast { .. }
//         | syntax::Term::Induct { .. }
//         | syntax::Term::Match { .. } => Sort::Term,
//         syntax::Term::Apply { fun, .. } => infer_sort(db, ctx, fun)?,
//         syntax::Term::Variable { id, span } => lookup_sort(db, &ctx, *span, id)?,
//         syntax::Term::Star { .. } => Sort::Kind,
//         syntax::Term::Hole { .. } => Sort::Unknown,
//         syntax::Term::Omission { .. } => Sort::Unknown,
//     };
//     Ok(result)
// }

// fn unify(db: &mut Database, ctx: Context, span: Span, left: &Rc<Value>, right: &Rc<Value>) -> Result<(), ElabError> {
//     match Value::unify(db, ctx.env_lvl(), left, right) {
//         Ok(true) => Ok(()),
//         Ok(false) | Err(_) => Err(ElabError::Inconvertible {
//             src: db.text(ctx.module),
//             span: source_span(db, ctx.module, span),
//             left: left.quote(db, ctx.env_lvl())
//                 .to_string_with_context(ctx.names.clone()),
//             right: right.quote(db, ctx.env_lvl())
//                 .to_string_with_context(ctx.names)
//         })
//     }
// }

// // fn fresh_hole(db: &mut Database, ctx: Context, data: HoleData, sort: Sort) -> Rc<term::Term> {
// //     let fresh_hole_name = db.fresh_hole(ctx.module, data);
// //     let id = Id { namespace: vec![], name: fresh_hole_name };
// //     Rc::new(term::Term::Free { sort, id })
// // }

// fn fresh_meta(db: &mut Database, ctx: Context, sort: Sort) -> term::Term {
//     let fresh_meta_name = db.fresh_meta(ctx.module);
//     term::Term::InsertedMeta {
//         sort,
//         name: fresh_meta_name,
//         mask: ctx.env_mask()
//     }
// }

// fn lookup_type(db: &Database, ctx: &Context, span: Span, id: &Id) -> Result<(Rc<Value>, Option<Level>, Mode), ElabError> {
//     let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
//     let toplevel_type = db.lookup_type(ctx.module, id);
//     let context_type = has_namespace
//         .and(ctx.names.iter().zip(ctx.types.iter()).zip(ctx.modes.iter()).enumerate().rev().find(|(_, ((x, _), _))| **x == id.name))
//         .map(|(level, ((_, ty), mode))| (ty.clone(), Some(level.into()), mode));
//     match (toplevel_type, context_type) {
//         (_, Some((v, level, mode))) => Ok((v, level, *mode)),
//         (Some(v), None) => Ok((v.force(db), None, Mode::Free)),
//         (None, None) => {
//             Err(ElabError::MissingName { source_code: db.text(ctx.module), span: source_span(db, ctx.module, span) })
//         }
//     }
// }

// fn lookup_sort(db: &Database, ctx: &Context, span: Span, id: &Id) -> Result<Sort, ElabError> {
//     let has_namespace = if id.namespace.is_empty() { Some(()) } else { None };
//     let toplevel_sort = db.lookup_type(ctx.module, id)
//         .map(|x| x.sort(db).demote());
//     let context_sort = has_namespace
//         .and(ctx.names.iter().zip(ctx.sorts.iter()).rev().find(|(x, _)| **x == id.name))
//         .map(|(_, sort)| *sort);
//     match (toplevel_sort, context_sort) {
//         (_, Some(sort)) => Ok(sort),
//         (Some(sort), None) => Ok(sort),
//         (None, None) => {
//             Err(ElabError::MissingName { source_code: db.text(ctx.module), span: source_span(db, ctx.module, span) })
//         }
//     }
// }

// fn wrap_term_from_context(ctx: Context, body: Rc<term::Term>) -> Rc<term::Term> {
//     let mut result = body;
//     for i in (0..ctx.len()).rev() {
//         let name = ctx.names[i];
//         let sort = ctx.sorts[i];
//         let mode = ctx.modes[i];
//         result = Rc::new(term::Term::Lambda {
//             sort: result.sort(),
//             domain_sort: sort,
//             mode,
//             name,
//             body: result
//         })
//     }
//     result
// }

// fn wrap_type_from_context(db: &Database, ctx: Context, body: Rc<term::Term>) -> Rc<term::Term> {
//     let mut result = body;
//     let mut level = ctx.env_lvl();
//     for i in (0..ctx.len()).rev() {
//         level = level - 1; // As we peel off a module parameter, the context maximum level is reduced by one
//         let name = ctx.names[i];
//         let domain = Rc::new(ctx.types[i].quote(db, level));
//         let mode = ctx.modes[i];
//         result = Rc::new(term::Term::Pi {
//             sort: result.sort(),
//             domain,
//             mode,
//             name,
//             body: result
//         })
//     }
//     result
// }

// fn source_span(db: &Database, module: Symbol, span: Span) -> SourceSpan {
//     // TODO: This is a hack to fix the source positioning for miette
//     // TODO: The parser should be grapheme relative (instead of byte relative)
//     //       to properly fix this
//     let (start, end) = span;
//     let len = db.text_ref(module)[start..end].graphemes(true).count();
//     // The positioning is "line-oriented" so you only have to correct up to the nearest newline
//     let start_prefix = db.text_ref(module)[..start].as_bytes();
//     let mut i = start - 1;
//     while i > 0 && start_prefix[i] != b'\n' { i -= 1; }
//     let byte_len = start - i;
//     let graphemes_len = db.text_ref(module)[i..start].graphemes(true).count();
//     // We subtract the extract internal bytes used to represent graphemes to correct the label source position
//     let start = start - (byte_len - graphemes_len);
//     SourceSpan::new(start.into(), len.into())
// }
