
use std::ops::{Deref, Add};
use std::fmt;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Index(usize);

unsafe impl Send for Index { }
unsafe impl Sync for Index { }
impl Unpin for Index { }

impl From<usize> for Index {
    fn from(u: usize) -> Index { Index(u) }
}

impl AsRef<usize> for Index {
    fn as_ref(&self) -> &usize {
        match self {
            Index(u) => u
        }
    }
}

impl AsMut<usize> for Index {
    fn as_mut(&mut self) -> &mut usize {
        match self {
            Index(u) => u
        }
    }
}

impl Deref for Index {
    type Target = usize;
    fn deref(&self) -> &Self::Target { 
        match self {
            Index(u) => u
        }
    }
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = **self;
        inner.fmt(f)
    }
}

impl Add<usize> for Index {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        (*self + rhs).into()
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Level(usize);

unsafe impl Send for Level { }
unsafe impl Sync for Level { }
impl Unpin for Level { }

impl From<usize> for Level {
    fn from(u: usize) -> Level { Level(u) }
}

impl AsRef<usize> for Level {
    fn as_ref(&self) -> &usize {
        match self {
            Level(u) => u
        }
    }
}

impl AsMut<usize> for Level {
    fn as_mut(&mut self) -> &mut usize {
        match self {
            Level(u) => u
        }
    }
}

impl Deref for Level {
    type Target = usize;
    fn deref(&self) -> &Self::Target { 
        match self {
            Level(u) => u
        }
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let inner = **self;
        inner.fmt(f)
    }
}

impl Add<usize> for Level {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        (*self + rhs).into()
    }
}

impl Level {
    pub fn to_index(self, env: Level) -> Index {
        (*env - *self - 1).into()
    }
}


