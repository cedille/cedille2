
use crate::common::*;

type Span = (usize, usize);

#[derive(Debug, Clone)]
pub struct Parameter {
    pub span: Span,
    pub mode: Mode,
    pub name: Symbol,
    pub body: Term
}

#[derive(Debug, Clone)]
pub struct Module {
    pub header_imports: Vec<Import>,
    pub path: Span,
    pub decls: Vec<Decl>,
    pub params: Vec<Parameter>
}

#[derive(Debug, Clone)]
pub enum Decl {
    Type(DefineTerm),
    Term(DefineTerm),
    Kind(DefineKind),
    Import(Import),
    Datatype(DefineDatatype)
}

#[derive(Debug, Clone)]
pub struct Import {
    pub span: Span,
    pub public: bool,
    pub path: Span,
    pub namespace: Option<Symbol>,
    pub args : Vec<(Mode, Term)>
}

#[derive(Debug, Clone)]
pub struct DefineTerm {
    pub span: Span,
    pub name: Symbol,
    pub anno: Option<Box<Term>>,
    pub body: Box<Term>
}

#[derive(Debug, Clone)]
pub struct DefineKind {
    pub span: Span,
    pub name: Symbol,
    pub args: Vec<KindArg>,
    pub body: Box<Term>
}

#[derive(Debug, Clone)]
pub struct DefineDatatype {
    pub span: Span,
    pub name: Symbol,
    pub params: Vec<Parameter>,
    pub kind: Box<Term>,
    pub ctors: Vec<Constructor>
}

#[derive(Debug, Clone)]
pub struct RewriteGuide {
    pub name: Symbol,
    pub hint: Option<Box<Term>>,
    pub ty: Box<Term>
}

#[derive(Debug, Clone)]
pub struct KindArg {
    pub name: Symbol,
    pub body: Term
}

#[derive(Debug, Clone)]
pub enum CaseArg {
    Erased(Symbol),
    Free(Symbol),
    Type(Symbol)
}

#[derive(Debug, Clone)]
pub struct Case {
    pub span: Span,
    pub id: Id,
    pub args: Vec<CaseArg>,
    pub body: Term
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub name: Symbol,
    pub anno: Term
}

#[derive(Debug, Clone)]
pub struct LambdaVar {
    pub mode: Mode,
    pub var: Option<Symbol>,
    pub anno: Option<Term>
}

#[derive(Debug, Clone)]
pub enum Term {
    Lambda {
        span: Span,
        sort: Sort,
        vars: Vec<LambdaVar>,
        body: Box<Term>
    },
    Let {
        span: Span,
        mode: Mode,
        sort: Sort,
        def: DefineTerm,
        body: Box<Term>
    },
    Pi {
        span: Span,
        mode: Mode,
        sort: Sort,
        var: Option<Symbol>,
        domain: Box<Term>,
        body: Box<Term>
    },
    IntersectType {
        span: Span,
        var: Option<Symbol>,
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
    Reflexivity {
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
        var: Symbol,
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
        apply_type: ApplyType,
        sort: Sort,
        fun: Box<Term>,
        arg: Box<Term>
    },
    Variable {
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

impl DefineTerm {
    pub fn as_str<'a, 'b>(&'a self, text: &'b str) -> &'b str {
        let (start, end) = self.span;
        &text[start..end]
    }
}

impl Term {
    pub fn span(&self) -> Span {
        match self {
            Term::Lambda { span, .. }
            | Term::Let { span, .. }
            | Term::Pi { span, .. }
            | Term::IntersectType { span, .. }
            | Term::Equality { span, .. }
            | Term::Rewrite { span, .. }
            | Term::Annotate { span, .. }
            | Term::Project { span, .. }
            | Term::Symmetry { span, .. }
            | Term::Intersect { span, .. }
            | Term::Separate { span, .. }
            | Term::Reflexivity { span, .. }
            | Term::Cast { span, .. }
            | Term::Induct { span, .. }
            | Term::Match { span, .. }
            | Term::Apply { span, .. }
            | Term::Variable { span, .. }
            | Term::Star { span }
            | Term::Hole { span, .. }
            => *span,
        }
    }

    pub fn as_str<'a, 'b>(&'a self, text: &'b str) -> &'b str {
        let (start, end) = self.span();
        &text[start..end]
    }

    pub fn sort(&self) -> Sort {
        match self {
            Term::Lambda { sort, .. }
            | Term::Let { sort, .. }
            | Term::Pi { sort, .. } => *sort,
            Term::IntersectType { .. }
            | Term::Equality { .. } => Sort::Type,
            Term::Rewrite { .. }
            | Term::Annotate { .. }
            | Term::Project { .. }
            | Term::Symmetry { .. }
            | Term::Intersect { .. }
            | Term::Separate { .. }
            | Term::Reflexivity { .. }
            | Term::Cast { .. }
            | Term::Induct { .. }
            | Term::Match { .. } => Sort::Term,
            Term::Apply { sort, .. }
            | Term::Variable { sort, .. } => *sort,
            Term::Star { .. } => Sort::Kind,
            Term::Hole { sort, .. } => *sort,
        }
    }
}
