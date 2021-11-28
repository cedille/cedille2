
use crate::database::Id;

type Span = (usize, usize);

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Erased,
    Free
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TermOrType {
    Term(Term),
    Type(Type)
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Module {
    pub imports: Vec<Import>,
    pub id: Id,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Decl {
    Type(DefineType),
    Term(DefineTerm),
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Import {
    pub public: bool,
    pub path: Span,
    pub namespace: Id,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefineTerm {
    pub id: Id,
    pub annotation: Box<Type>,
    pub body: Box<Term>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DefineType {
    pub id: Id,
    pub annotation: Box<Kind>,
    pub body: Box<Type>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RewriteGuide {
    pub id: Id,
    pub hint: Box<Term>,
    pub equation: Box<Type>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Lambda {
        mode: Mode,
        body: Box<Term>
    },
    TypeLambda {
        body: Box<Term>
    },
    Rewrite {
        equation: Box<Term>,
        guide: RewriteGuide,
        body: Box<Term>
    },
    Annotate {
        annotation: Box<Type>,
        body: Box<Term>
    },
    Project {
        variant: usize,
        body: Box<Term>
    },
    Intersect {
        first: Box<Term>,
        second: Box<Term>
    },
    Separate {
        equation: Box<Term>
    },
    Refl {
        erasure: Box<Term>
    },
    Cast {
        equation: Box<Term>,
        input: Box<Term>,
        erasure: Box<Term>
    },
    Apply {
        mode: Mode,
        fun: Box<Term>,
        arg: Box<Term>
    },
    TypeApply {
        fun: Box<Term>,
        arg: Box<Type>
    },
    Var { index: isize },
    Ref { id: Id },
    Hole,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Fn {
        domain: Box<Kind>,
        body: Box<Type>
    },
    TermFn {
        mode: Mode,
        domain: Box<Type>,
        body: Box<Type>
    },
    Lambda {
        domain: Box<Kind>,
        body: Box<Type>
    },
    TermLambda {
        domain: Box<Type>,
        body: Box<Type>
    },
    Intersection {
        first: Box<Type>,
        second: Box<Type>
    },
    Equality {
        left: Box<Term>,
        right: Box<Term>
    },
    Apply {
        fun: Box<Type>,
        arg: Box<Type>
    },
    TermApply {
        fun: Box<Type>,
        arg: Box<Term>
    },
    Var { index: isize },
    Ref { id: Id },
    Hole,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Fn {
        domain: Box<Kind>,
        body: Box<Kind>
    },
    TypeFn {
        domain: Box<Type>,
        body: Box<Kind>
    },
    Star
}

impl Term {
    pub fn erase(&self) -> Term {
        match self {
            Term::Lambda { mode, body } => match mode {
                Mode::Erased => body.erase(),
                Mode::Free => {
                    let body = Box::new(body.erase());
                    Term::Lambda { mode: *mode, body }
                }
            }
            Term::TypeLambda { body }
            | Term::Rewrite { body, .. }
            | Term::Annotate { body, .. }
            | Term::Project { body, .. } => body.erase(),
            Term::Intersect { first, .. } => first.erase(),
            Term::Separate { .. } => Term::id(),
            Term::Refl { erasure }
            | Term::Cast { erasure, .. } => erasure.erase(),
            Term::Apply { mode, fun, arg } => match mode {
                Mode::Erased => fun.erase(),
                Mode::Free => {
                    let fun = Box::new(fun.erase());
                    let arg = Box::new(arg.erase());
                    Term::Apply { mode: *mode, fun, arg }
                },
            },
            Term::TypeApply { fun, .. } => fun.erase(),
            t @ Term::Var { .. } => t.clone(),
            t @ Term::Ref { .. } => t.clone(),
            t @ Term::Hole => t.clone(),
        }
    }

    pub fn id() -> Term {
        let mode = Mode::Free;
        let body = Box::new(Term::Var { index:0 });
        Term::Lambda { mode, body }
    }
}

impl TermOrType {
    pub fn unwrap_term(self) -> Term {
        match self {
            TermOrType::Term(t) => t,
            _ => panic!()
        }
    }

    pub fn unwrap_type(self) -> Type {
        match self {
            TermOrType::Type(t) => t,
            _ => panic!()
        }
    }
}
