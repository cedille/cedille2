
use internment::Intern;
use crate::database::Id;

type Span = (usize, usize);

#[derive(Debug, Clone, Copy)]
pub enum Mode {
    Erased,
    Free
}

#[derive(Debug, Clone, Copy)]
pub enum Sort {
    Term,
    Type,
    Kind
}

#[derive(Debug)]
pub struct Parameter {
    pub span: Span,
    pub mode: Mode,
    pub name: Intern<String>,
    pub body: Term
}

#[derive(Debug)]
pub struct Module {
    pub imports: Vec<Import>,
    pub id: Id,
    pub decls: Vec<Decl>,
    pub params: Vec<Parameter>
}

#[derive(Debug)]
pub enum Decl {
    Type(DefineTerm),
    Term(DefineTerm),
    Kind(DefineKind),
    Datatype(DefineDatatype)
}

#[derive(Debug)]
pub struct Import {
    pub span: Span,
    pub public: bool,
    pub path: Span,
    pub namespace: Option<Intern<String>>,
    pub args : Vec<(Mode, Term)>
}

#[derive(Debug)]
pub struct DefineTerm {
    pub span: Span,
    pub name: Intern<String>,
    pub anno: Option<Box<Term>>,
    pub body: Box<Term>
}

#[derive(Debug)]
pub struct DefineKind {
    pub span: Span,
    pub name: Intern<String>,
    pub args: Vec<KindArg>,
    pub body: Box<Term>
}

#[derive(Debug)]
pub struct DefineDatatype {
    pub span: Span,
    pub name: Intern<String>,
    pub params: Vec<Parameter>,
    pub kind: Box<Term>,
    pub ctors: Vec<Constructor>
}

#[derive(Debug)]
pub struct RewriteGuide {
    pub name: Intern<String>,
    pub hint: Option<Box<Term>>,
    pub equation: Box<Term>
}

#[derive(Debug)]
pub struct KindArg {
    pub name: Intern<String>,
    pub body: Term
}

#[derive(Debug)]
pub enum CaseArg {
    Erased(Intern<String>),
    Free(Intern<String>),
    Type(Intern<String>)
}

#[derive(Debug)]
pub struct Case {
    pub span: Span,
    pub id: Id,
    pub args: Vec<CaseArg>,
    pub body: Term
}

#[derive(Debug)]
pub struct Constructor {
    pub name: Intern<String>,
    pub anno: Term
}

#[derive(Debug)]
pub enum Term {
    Lambda {
        span: Span,
        mode: Mode,
        sort: Sort,
        var: Intern<String>,
        anno: Option<Box<Term>>,
        body: Box<Term>
    },
    Let {
        span: Span,
        mode: Mode,
        sort: Sort,
        def: DefineTerm,
        body: Box<Term>
    },
    Fn {
        span: Span,
        mode: Mode,
        sort: Sort,
        var: Option<Intern<String>>,
        domain: Box<Term>,
        body: Box<Term>
    },
    IntersectType {
        span: Span,
        var: Intern<String>,
        first: Box<Term>,
        second: Box<Term>
    },
    Equality {
        span: Span,
        left: Box<Term>,
        right: Box<Term>
    },
    Rewrite {
        span: Span,
        reduce: bool,
        occurrence: Option<usize>,
        equation: Box<Term>,
        guide: Option<RewriteGuide>,
        body: Box<Term>
    },
    Annotate {
        span: Span,
        anno: Box<Term>,
        body: Box<Term>
    },
    Project {
        span: Span,
        variant: usize,
        body: Box<Term>
    },
    Symmetry {
        span: Span,
        equation: Box<Term>
    },
    Intersect {
        span: Span,
        first: Box<Term>,
        second: Box<Term>
    },
    Separate {
        span: Span,
        anno: Option<Box<Term>>,
        equation: Box<Term>
    },
    Refl {
        span: Span,
        guide: Option<Box<Term>>,
        erasure: Option<Box<Term>>
    },
    Cast {
        span: Span,
        equation: Box<Term>,
        input: Box<Term>,
        erasure: Box<Term>
    },
    Induct {
        span: Span,
        var: Intern<String>,
        inductee: Box<Term>,
        motive: Option<Box<Term>>,
        cases: Vec<Case>
    },
    Match {
        span: Span,
        guide: Option<Box<Term>>,
        matched: Box<Term>,
        motive: Option<Box<Term>>,
        cases: Vec<Case>
    },
    Apply {
        span: Span,
        mode: Mode,
        sort: Sort,
        fun: Box<Term>,
        arg: Box<Term>
    },
    Bound {
        span: Span,
        sort: Sort,
        var: Intern<String>,
        index: usize
    },
    Free {
        span: Span,
        sort: Sort,
        id: Id
    },
    Star { 
        span: Span
    },
    Hole {
        span: Span,
        sort: Sort
    },
}
