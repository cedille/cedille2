
use cedille2_core::utility::*;

type Span = (usize, usize);

#[derive(Debug, Clone)]
pub struct Parameter {
    pub span: Span,
    pub mode: Mode,
    pub name: Symbol,
    pub body: Term
}

#[derive(Debug, Clone)]
pub enum Command {
    Module(Span, Vec<Parameter>),
    Declare(Declaration),
    Define(Definition),
    Import(Import),
    Infer(Term),
    Check(Term, Term),
    Erase(Term),
    Value(Term),
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
pub struct Declaration {
    pub span: Span,
    pub name: Symbol,
    pub body: Box<Term>
}

#[derive(Debug, Clone)]
pub struct Definition {
    pub span: Span,
    pub name: Symbol,
    pub vars: Vec<LambdaVar>,
    pub body: Box<Term>
}

#[derive(Debug, Clone)]
pub struct DefineTerm {
    pub span: Span,
    pub opaque: bool,
    pub name: Symbol,
    pub anno: Option<Box<Term>>,
    pub body: Box<Term>
}

#[derive(Debug, Clone)]
pub struct KindArg {
    pub name: Symbol,
    pub body: Term
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
        vars: Vec<LambdaVar>,
        body: Box<Term>
    },
    Let {
        span: Span,
        mode: Mode,
        def: DefineTerm,
        body: Box<Term>
    },
    Pi {
        span: Span,
        mode: Mode,
        var: Option<Symbol>,
        domain: Box<Term>,
        body: Box<Term>
    },
    Intersect {
        span: Span,
        var: Option<Symbol>,
        first: Box<Term>,
        second: Box<Term>
    },
    Equality {
        span: Span,
        left: Box<Term>,
        right: Box<Term>,
        domain: Option<Box<Term>>
    },
    Project {
        span: Span,
        variant: usize,
        body: Box<Term>
    },
    Pair {
        span: Span,
        anno: Option<Box<Term>>,
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
        input: Box<Term>
    },
    Cast {
        span: Span,
        input: Box<Term>,
        witness: Box<Term>,
        evidence: Box<Term>
    },
    Promote {
        span: Span,
        equation: Box<Term>
    },
    Subst {
        span: Span,
        predicate: Box<Term>,
        equation: Box<Term>,
    },
    Apply {
        span: Span,
        fun: Box<Term>,
        arg: Box<Term>
    },
    Variable {
        span: Span,
        id: Id
    },
    Hole {
        span: Span
    },
    Omission {
        span: Span
    },
    Set {
        span: Span
    }
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
            | Term::Intersect { span, .. }
            | Term::Equality { span, .. }
            | Term::Project { span, .. }
            | Term::Pair { span, .. }
            | Term::Separate { span, .. }
            | Term::Refl { span, .. }
            | Term::Promote { span, .. }
            | Term::Subst { span, .. }
            | Term::Cast { span, .. }
            | Term::Apply { span, .. }
            | Term::Variable { span, .. }
            | Term::Hole { span, .. }
            | Term::Omission { span, .. }
            | Term::Set { span, ..}
            => *span,
        }
    }

    pub fn as_str<'a, 'b>(&'a self, text: &'b str) -> &'b str {
        let (start, end) = self.span();
        &text[start..end]
    }
}
