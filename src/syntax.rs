
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
pub enum TermOrType {
    Term(Term),
    Type(Type)
}

#[derive(Debug)]
pub enum TypeOrKind {
    Type(Type),
    Kind(Kind)
}

#[derive(Debug)]
pub struct Parameter {
    pub span: Span,
    pub mode: Mode,
    pub id: Id,
    pub body: TypeOrKind
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
    Type(DefineType),
    Term(DefineTerm),
    Kind(DefineKind),
    Datatype(DefineDatatype)
}

#[derive(Debug)]
pub enum ImportArg {
    Term(Mode, Term),
    Type(Type)
}

#[derive(Debug)]
pub struct Import {
    pub span: Span,
    pub public: bool,
    pub path: Span,
    pub namespace: Option<Id>,
    pub args : Vec<ImportArg>
}

#[derive(Debug)]
pub struct DefineTerm {
    pub span: Span,
    pub id: Id,
    pub annotation: Option<Box<Type>>,
    pub body: Box<Term>
}

#[derive(Debug)]
pub struct DefineType {
    pub span: Span,
    pub id: Id,
    pub annotation: Box<Kind>,
    pub body: Box<Type>
}

#[derive(Debug)]
pub struct DefineKind {
    pub span: Span,
    pub id: Id,
    pub args: Vec<KindArg>,
    pub body: Box<Kind>
}

#[derive(Debug)]
pub struct DefineDatatype {
    pub span: Span,
    pub id: Id,
    pub params: Vec<Parameter>,
    pub kind: Box<Kind>,
    pub ctors: Vec<Constructor>
}

#[derive(Debug)]
pub struct RewriteGuide {
    pub id: Id,
    pub hint: Option<Box<Term>>,
    pub equation: Box<Type>
}

#[derive(Debug)]
pub struct KindArg {
    pub id: Id,
    pub arg: TypeOrKind
}

#[derive(Debug)]
pub enum CaseArg {
    Erased(Id),
    Free(Id),
    Type(Id)
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
    pub id: Id,
    pub annotation: Type
}

#[derive(Debug)]
pub enum Term {
    Lambda {
        span: Span,
        mode: Mode,
        id: Id,
        annotation: Option<Box<Type>>,
        body: Box<Term>
    },
    TypeLambda {
        span: Span,
        id: Id,
        annotation: Box<Kind>,
        body: Box<Term>
    },
    Let {
        span: Span,
        mode: Mode,
        def: DefineTerm,
        body: Box<Term>
    },
    TypeLet {
        span: Span,
        def: DefineType,
        body: Box<Term>
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
        annotation: Box<Type>,
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
    Intersection {
        span: Span,
        first: Box<Term>,
        second: Box<Term>
    },
    Separate {
        span: Span,
        annotation: Option<Box<Type>>,
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
        id: Id,
        inductee: Box<Term>,
        motive: Option<Box<Type>>,
        cases: Vec<Case>
    },
    Match {
        span: Span,
        guide: Option<Box<Term>>,
        matched: Box<Term>,
        motive: Option<Box<Type>>,
        cases: Vec<Case>
    },
    Apply {
        span: Span,
        mode: Mode,
        fun: Box<Term>,
        arg: Box<Term>
    },
    TypeApply {
        span: Span,
        fun: Box<Term>,
        arg: Box<Type>
    },
    Var {
        span: Span,
        id: Id
    },
    Hole {
        span: Span
    },
}

#[derive(Debug)]
pub enum Type {
    Fn {
        span: Span,
        id: Id,
        domain: Box<Kind>,
        body: Box<Type>
    },
    TermFn {
        span: Span,
        mode: Mode,
        id: Id,
        domain: Box<Type>,
        body: Box<Type>
    },
    Lambda {
        span: Span,
        id: Id,
        annotation: Box<Kind>,
        body: Box<Type>
    },
    TermLambda {
        span: Span,
        id: Id,
        annotation: Box<Type>,
        body: Box<Type>
    },
    Let {
        span: Span,
        def: DefineType,
        body: Box<Type>
    },
    TermLet {
        span: Span,
        def: DefineTerm,
        body: Box<Type>
    },
    Intersection {
        span: Span,
        id: Id,
        first: Box<Type>,
        second: Box<Type>
    },
    Equality {
        span: Span,
        left: Box<Term>,
        right: Box<Term>
    },
    Apply {
        span: Span,
        fun: Box<Type>,
        arg: Box<Type>
    },
    TermApply {
        span: Span,
        fun: Box<Type>,
        arg: Box<Term>
    },
    Var {
        span: Span,
        id: Id
    },
    Hole {
        span: Span
    },
}

#[derive(Debug)]
pub enum Kind {
    Fn {
        span: Span,
        id: Id,
        domain: Box<Kind>,
        body: Box<Kind>
    },
    TypeFn {
        span: Span,
        id: Id,
        domain: Box<Type>,
        body: Box<Kind>
    },
    Apply {
        span: Span,
        id: Id,
        args: Vec<TermOrType>
    },
    Star { 
        span: Span
    }
}
