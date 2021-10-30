
type Span = (usize, usize);
type Symbol = u16;

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id {
    pub module: Symbol,
    pub namespace: Option<Symbol>,
    pub decl: Symbol,
    pub index: Option<Symbol>
}

#[derive(Debug)]
pub enum Mode {
    Erased,
    Free
}

#[derive(Debug)]
pub struct Module {
    pub imports: Vec<Import>,
    pub id: Id,
    pub decls: Vec<Decl>,
}

#[derive(Debug)]
pub enum Decl {
    Type(DefineType),
    Term(DefineTerm),
}

#[derive(Debug)]
pub struct Import {
    pub public: bool,
    pub path: Span,
    pub namespace: Id,
}

#[derive(Debug)]
pub struct DefineTerm {
    pub annotation: Option<Box<Type>>,
    pub body: Box<Term>
}

#[derive(Debug)]
pub struct DefineType {
    pub annotation: Box<Kind>,
    pub body: Box<Type>
}

#[derive(Debug)]
pub struct RewriteGuide {
    pub id: Id,
    pub hint: Box<Term>,
    pub equation: Box<Type>
}

#[derive(Debug)]
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
    Var { index: Id },
    Hole,
}

#[derive(Debug)]
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
    Var { index: Id },
    Hole,
}

#[derive(Debug)]
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
