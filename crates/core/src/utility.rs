
use std::{rc, ops, fmt};
use internment::Intern;
use imbl::{Vector, vector};

pub struct Verbose<'a, T : ?Sized> {
    level: usize,
    data: &'a T
}

pub trait VerboseDebug {
    fn vvv(&self, level: usize) -> Verbose<'_, Self>;
}

impl<T> VerboseDebug for T {
    fn vvv(&self, level: usize) -> Verbose<'_, Self> {
        Verbose { level, data: self }
    }
}

impl<'a, T> fmt::Debug for Verbose<'a, Vector<T>>
where Verbose<'a, T> : fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for i in 0..self.data.len() {
            let v = self.data[i].vvv(self.level);
            v.fmt(f)?;
            if i < self.data.len() - 1 {
                write!(f, ",")?;
            }
        }
        write!(f, "]")
    }
}

pub trait Boxable {
    fn boxed(self) -> Box<Self>;
}

impl<T> Boxable for T {
    fn boxed(self: T) -> Box<T> {
        Box::new(self)
    }
}

pub trait ReferenceCountable {
    fn rced(self) -> rc::Rc<Self>;
}

impl<T> ReferenceCountable for T {
    fn rced(self: T) -> rc::Rc<T> {
        rc::Rc::new(self)
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(Intern<String>);

impl From<&str> for Symbol {
    fn from(s: &str) -> Self { Symbol(Intern::from_ref(s)) }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &'static str { self.0.as_ref() }
}

impl ops::Deref for Symbol {
    type Target = String;
    fn deref(&self) -> &Self::Target { self.0.deref() }
}

impl Default for Symbol {
    fn default() -> Self { Self::from("_") }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl<'a> fmt::Debug for Verbose<'a, Symbol> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.level {
            0 => {
                if self.data.len() <= 4 {
                    <str as fmt::Display>::fmt(self.data.as_str(), f)
                } else {
                    <str as fmt::Display>::fmt(&self.data.as_str()[0..2], f)?;
                    <str as fmt::Display>::fmt("..", f)
                }
            },
            1 => <Symbol as fmt::Display>::fmt(self.data, f),
            _ => <Symbol as fmt::Debug>::fmt(self.data, f)
        }
    }
}

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id {
    pub namespace: Vector<Symbol>,
    pub module: Symbol,
    pub name: Symbol,
}

impl Id {
    pub fn new(module: Symbol, name: Symbol) -> Id {
        Id {
            namespace: vector![],
            module,
            name
        }
    }

    pub fn add_qualifier(&self, sym: Symbol) -> Id {
        let mut namespace = self.namespace.clone();
        namespace.push_front(sym); 
        Id {
            namespace,
            module: self.module,
            name: self.name
        }
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = Ok(());
        for component in self.namespace.iter() {
            result = result.and_then(|_| write!(f, "{}.", component));
        }
        result.and_then(|_| write!(f, "{}", self.name))
    }
}

impl<'a> fmt::Debug for Verbose<'a, Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.level {
            level if level <= 2 => {
                self.data.namespace.vvv(self.level).fmt(f)?;
                self.data.name.vvv(level).fmt(f)
            }
            _ => <Id as fmt::Debug>::fmt(self.data, f)
        }
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Erased,
    Free,
    TypeLevel
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mode::Erased => write!(f, "Erased"),
            Mode::Free => write!(f, "Free"),
            Mode::TypeLevel => write!(f, "TypeLevel")
        }
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sort {
    Unknown,
    Term,
    Type,
    Kind
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Unknown => write!(f, "Unknown"),
            Sort::Term => write!(f, "Term"),
            Sort::Type => write!(f, "Type"),
            Sort::Kind => write!(f, "Kind"),
        }
    }
}

impl Sort {
    pub fn demote(self) -> Sort {
        match self {
            Sort::Unknown => Sort::Unknown,
            Sort::Term => Sort::Unknown,
            Sort::Type => Sort::Term,
            Sort::Kind => Sort::Type,
        }
    }

    pub fn promote(self) -> Sort {
        match self {
            Sort::Unknown => Sort::Unknown,
            Sort::Term => Sort::Type,
            Sort::Type => Sort::Kind,
            Sort::Kind => Sort::Unknown,
        }
    }
}

// , From, AsRef, AsMut, Deref, Display

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Index(usize);

impl ops::Add<usize> for Index {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        (*self + rhs).into()
    }
}

impl ops::Deref for Index {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        let Index(result) = self;
        result
    }
}

impl From<usize> for Index {
    fn from(value: usize) -> Self {
        Index(value)
    }
}

impl Index {
    pub fn to_level(self, env: usize) -> Level {
        (env - *self - 1).into()
    }
}


#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level(usize);

impl ops::Add<usize> for Level {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        (*self + rhs).into()
    }
}

impl ops::Sub<usize> for Level {
    type Output = Self;
    
    fn sub(self, rhs: usize) -> Self::Output {
        (*self - rhs).into()
    }
}

impl ops::Deref for Level {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        let Level(result) = self;
        result
    }
}

impl From<usize> for Level {
    fn from(value: usize) -> Self {
        Level(value)
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl Level {
    pub fn to_index(self, env: usize) -> Index {
        (env - *self - 1).into()
    }
}
