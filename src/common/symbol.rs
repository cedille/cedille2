
use std::ops::Deref;
use std::fmt;

use internment::LocalIntern;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(LocalIntern<String>);

impl From<&str> for Symbol {
    fn from(s: &str) -> Symbol { 
        Symbol(LocalIntern::from(s))
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        match self {
            Symbol(u) => u.as_ref()
        }
    }
}

impl Deref for Symbol {
    type Target = String;
    fn deref(&self) -> &Self::Target { 
        match self {
            Symbol(u) => &**u
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Symbol(inner) = self;
        inner.fmt(f)
    }
}

impl Default for Symbol {
    fn default() -> Self {
        Self(LocalIntern::default())
    }
}
