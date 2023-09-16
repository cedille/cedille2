
use std::{ops, fmt};
use internment::LocalIntern;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(LocalIntern<String>);

impl From<&str> for Symbol {
    fn from(s: &str) -> Self { Symbol(LocalIntern::from(s)) }
}

impl AsRef<String> for Symbol {
    fn as_ref(&self) -> &String { self.0.as_ref() }
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

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id {
    pub namespace: Vec<Symbol>,
    pub name: Symbol,
}

impl Id {
    pub fn add_qualifier(&self, sym: Symbol) -> Id {
        let mut namespace = vec![sym];
        namespace.extend(self.namespace.iter());
        Id {
            namespace,
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

impl From<Symbol> for Id {
    fn from(sym: Symbol) -> Self { Id { namespace: vec![], name: sym } }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Erased,
    Free
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mode::Erased => write!(f, "Erased"),
            Mode::Free => write!(f, "Free")
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

impl Sort {
    pub fn demote(self) -> Sort {
        match self {
            Sort::Unknown => Sort::Unknown,
            Sort::Term => Sort::Unknown,
            Sort::Type => Sort::Term,
            Sort::Kind => Sort::Type,
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
