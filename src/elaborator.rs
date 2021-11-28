
use internment::Intern;

use crate::database::{Id, Database};
use crate::syntax;
use crate::kernel;

pub fn elaborate(db: &Database, module: &syntax::Module) -> kernel::Module {
    kernel::Module {
        imports: vec![],
        id: Id { module:Intern::from(""), namespace:None, decl:None, index:None },
        decls: module.decls.iter().map(|d| elaborate_decl(db, &module.params, d)).collect()
    }
}

fn elaborate_decl(db: &Database, params: &[syntax::Parameter], decl: &syntax::Decl) -> kernel::Decl {
    match decl {
        syntax::Decl::Type(ty) => kernel::Decl::Type(elaborate_define_type(db, params, ty)),
        syntax::Decl::Term(term) => kernel::Decl::Term(elaborate_define_term(db, params, term)),
        syntax::Decl::Kind(_) => todo!(),
        syntax::Decl::Datatype(_) => todo!(),
    }
}

fn elaborate_define_type(db: &Database
    , params: &[syntax::Parameter]
    , decl: &syntax::DefineType)
    -> kernel::DefineType {
    let body = elaborate_type(db, &decl.body);
    let body = Box::new(type_parameter_prefix(params, body));
    kernel::DefineType { 
        id: decl.id,
        annotation: Box::new(elaborate_kind(db, &decl.annotation)),
        body
    }
}

fn elaborate_define_term(db: &Database
    , params: &[syntax::Parameter]
    , decl: &syntax::DefineTerm)
    -> kernel::DefineTerm {
    let annotation = decl.annotation.as_ref().unwrap();
    let body = elaborate_term(db, &decl.body);
    let body = Box::new(term_parameter_prefix(params, body));
    kernel::DefineTerm {
        id: decl.id,
        annotation: Box::new(elaborate_type(db, annotation)),
        body
    }
}

fn elaborate_term(db: &Database, term: &syntax::Term) -> kernel::Term {
    match term {
        syntax::Term::Lambda { span, mode, id, annotation, body } => todo!(),
        syntax::Term::TypeLambda { span, id, annotation, body } => todo!(),
        syntax::Term::Let { span, mode, def, body } => todo!(),
        syntax::Term::TypeLet { span, def, body } => todo!(),
        syntax::Term::Rewrite { span, reduce, occurrence, equation, guide, body } => todo!(),
        syntax::Term::Annotate { span, annotation, body } => todo!(),
        syntax::Term::Project { span, variant, body } => todo!(),
        syntax::Term::Symmetry { span, equation } => todo!(),
        syntax::Term::Intersection { span, first, second } => todo!(),
        syntax::Term::Separate { span, annotation, equation } => todo!(),
        syntax::Term::Refl { span, guide, erasure } => todo!(),
        syntax::Term::Cast { span, equation, input, erasure } => todo!(),
        syntax::Term::Induct { span, id, inductee, motive, cases } => todo!(),
        syntax::Term::Match { span, guide, matched, motive, cases } => todo!(),
        syntax::Term::Apply { span, mode, fun, arg } => todo!(),
        syntax::Term::TypeApply { span, fun, arg } => todo!(),
        syntax::Term::Var { span, id } => todo!(),
        syntax::Term::Hole { span } => todo!(),
    }
}

fn elaborate_type(db: &Database, ty: &syntax::Type) -> kernel::Type {
    match ty {
        syntax::Type::Fn { span, id, domain, body } => {
            let domain = Box::new(elaborate_kind(db, domain));
            let body = Box::new(elaborate_type(db, body));
            kernel::Type::Fn { domain, body }
        },
        syntax::Type::TermFn { span, mode, id, domain, body } => {
            let mode = elaborate_mode(mode);
            let domain = Box::new(elaborate_type(db, domain));
            let body = Box::new(elaborate_type(db, body));
            kernel::Type::TermFn { mode, domain, body }
        },
        syntax::Type::Lambda { span, id, annotation, body } => {
            let domain = Box::new(elaborate_kind(db, annotation));
            let body =  Box::new(elaborate_type(db, body));
            kernel::Type::Lambda { domain, body }
        },
        syntax::Type::TermLambda { span, id, annotation, body } => {
            let domain = Box::new(elaborate_type(db, annotation));
            let body = Box::new(elaborate_type(db, body));
            kernel::Type::TermLambda { domain, body }
        },
        syntax::Type::Let { span, def, body } => todo!(),
        syntax::Type::TermLet { span, def, body } => todo!(),
        syntax::Type::Intersection { span, id, first, second } => {
            let first = Box::new(elaborate_type(db, first));
            let second = Box::new(elaborate_type(db, second));
            kernel::Type::Intersection { first, second }
        },
        syntax::Type::Equality { span, left, right } => {
            let left = Box::new(elaborate_term(db, left));
            let right = Box::new(elaborate_term(db, right));
            kernel::Type::Equality { left, right }
        },
        syntax::Type::Apply { span, fun, arg } => {
            let fun = Box::new(elaborate_type(db, fun));
            let arg = Box::new(elaborate_type(db, arg));
            kernel::Type::Apply { fun, arg }
        },
        syntax::Type::TermApply { span, fun, arg } => {
            let fun = Box::new(elaborate_type(db, fun));
            let arg = Box::new(elaborate_term(db, arg));
            kernel::Type::TermApply { fun, arg }
        },
        syntax::Type::Var { span, id } => {
            kernel::Type::Var { index:0 }
        },
        syntax::Type::Hole { span } => kernel::Type::Hole,
    }
}

fn elaborate_kind(db: &Database, kind: &syntax::Kind) -> kernel::Kind {
    match kind {
        syntax::Kind::Fn { span, id, domain, body } => {
            let domain = Box::new(elaborate_kind(db, domain));
            let body = Box::new(elaborate_kind(db, body));
            kernel::Kind::Fn { domain, body }
        },
        syntax::Kind::TypeFn { span, id, domain, body } => {
            let domain = Box::new(elaborate_type(db, domain));
            let body = Box::new(elaborate_kind(db, body));
            kernel::Kind::TypeFn { domain, body }
        },
        syntax::Kind::Apply { span, id, args } => todo!(),
        syntax::Kind::Star { span } => kernel::Kind::Star,
    }
}

fn term_parameter_prefix(params: &[syntax::Parameter], body: kernel::Term) -> kernel::Term {
    todo!()
}

fn type_parameter_prefix(params: &[syntax::Parameter], body: kernel::Type) -> kernel::Type {
    todo!()
}

fn elaborate_mode(mode: &syntax::Mode) -> kernel::Mode {
    match mode {
        syntax::Mode::Erased => kernel::Mode::Erased,
        syntax::Mode::Free => kernel::Mode::Free,
    }
}
