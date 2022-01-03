
use std::rc::Rc;

use crate::common::*;

type Span = (usize, usize);

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Module {
    pub imports: Vec<Import>,
    pub id: Id,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Import {
    pub public: bool,
    pub path: Span,
    pub namespace: Id,
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Decl {
    pub name: Symbol,
    pub ty: Rc<Term>,
    pub body: Rc<Term>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct RewriteGuide {
    pub id: Id,
    pub hint: Rc<Term>,
    pub equation: Rc<Term>
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Lambda {
        mode: Mode,
        name: Symbol,
        body: Rc<Term>
    },
    Let {
        mode: Mode,
        name: Symbol,
        let_body: Rc<Term>,
        body: Rc<Term>
    },
    Pi {
        mode: Mode,
        name: Symbol,
        domain: Rc<Term>,
        body: Rc<Term>
    },
    IntersectType {
        name: Symbol,
        first: Rc<Term>,
        second: Rc<Term>
    },
    Equality {
        left: Rc<Term>,
        right: Rc<Term>
    },
    Rewrite {
        equation: Rc<Term>,
        guide: RewriteGuide,
        body: Rc<Term>
    },
    Annotate {
        anno: Rc<Term>,
        body: Rc<Term>
    },
    Project {
        variant: usize,
        body: Rc<Term>
    },
    Intersect {
        first: Rc<Term>,
        second: Rc<Term>
    },
    Separate {
        equation: Rc<Term>
    },
    Refl {
        erasure: Rc<Term>
    },
    Cast {
        equation: Rc<Term>,
        input: Rc<Term>,
        erasure: Rc<Term>
    },
    Apply {
        mode: Mode,
        fun: Rc<Term>,
        arg: Rc<Term>
    },
    Bound { index: Index },
    Free { id: Id },
    Star,
    SuperStar,
}

impl Term {
    pub fn id() -> Term {
        let (mode, name) = (Mode::Free, Symbol::from("x"));
        let body = Rc::new(Term::Bound { index:0.into() });
        Term::Lambda { mode, name, body }
    }
}
