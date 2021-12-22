
use crate::common::debruijn::Index;
use crate::common::Id;

type Span = (usize, usize);

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sort {
    Term,
    Type,
    Kind
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Erased,
    Free
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Module {
    pub imports: Vec<Import>,
    pub id: Id,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Decl {
    Type(DefineTerm),
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
    pub annotation: Box<Term>,
    pub body: Box<Term>
}


#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RewriteGuide {
    pub id: Id,
    pub hint: Box<Term>,
    pub equation: Box<Term>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Lambda {
        mode: Mode,
        sort: Sort,
        body: Box<Term>
    },
    Let {
        mode: Mode,
        sort: Sort,
        def: DefineTerm,
        body: Box<Term>
    },
    Pi {
        mode: Mode,
        sort: Sort,
        domain: Box<Term>,
        body: Box<Term>
    },
    IntersectType {
        first: Box<Term>,
        second: Box<Term>
    },
    Equality {
        left: Box<Term>,
        right: Box<Term>
    },
    Rewrite {
        equation: Box<Term>,
        guide: RewriteGuide,
        body: Box<Term>
    },
    Annotate {
        annotation: Box<Term>,
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
        sort: Sort,
        fun: Box<Term>,
        arg: Box<Term>
    },
    Bound {
        sort: Sort,
        index: Index
    },
    Free {
        sort: Sort,
        id: Id
    },
    Star,
    Hole { sort: Sort },
}

/* impl Term {
    pub fn erase(&self) -> Term {
        match self {
            Term::Lambda { mode, sort, body } => match mode {
                Mode::Erased => body.erase(),
                Mode::Free => {
                    let body = Box::new(body.erase());
                    Term::Lambda { mode: *mode, sort: *sort, body }
                }
            }
            Term::Let { mode, sort, def, body } => match mode {
                Mode::Erased => body.erase(),
                Mode::Free => {
                    let body = Box::new(body.erase());
                    Term::Let { mode: *mode, sort: *sort, def: def.clone(), body }
                }
            }
            Term::Fn { .. }
            | Term::IntersectType { .. }
            | Term::Equality { .. } => unreachable!(),
            Term::Rewrite { body, .. }
            | Term::Annotate { body, .. }
            | Term::Project { body, .. } => body.erase(),
            Term::Intersect { first, .. } => first.erase(),
            Term::Separate { .. } => Term::id(),
            Term::Refl { erasure }
            | Term::Cast { erasure, .. } => erasure.erase(),
            Term::Apply { mode, sort, fun, arg } => match mode {
                Mode::Erased => fun.erase(),
                Mode::Free => {
                    let fun = Box::new(fun.erase());
                    let arg = Box::new(arg.erase());
                    Term::Apply { mode: *mode, sort: *sort, fun, arg }
                },
            },
            t @ Term::Bound { .. } => t.clone(),
            t @ Term::Free { .. } => t.clone(),
            t @ Term::Star => t.clone(),
            t @ Term::Hole { .. } => t.clone(),
        }
    }

    pub fn id() -> Term {
        let (mode, sort) = (Mode::Free, Sort::Term);
        let body = Box::new(Term::Bound { sort, index:0 });
        Term::Lambda { mode, sort, body }
    }
}
 */