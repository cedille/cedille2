
use std::{ops, fmt};

use derive_more::{From, AsRef, AsMut, Deref, Display};
use internment::LocalIntern;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Display, Default)]
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

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id {
    pub namespace: Vec<Symbol>,
    pub name: Symbol,
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Erased,
    Free
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sort {
    Term,
    Type,
    Kind
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, From, AsRef, AsMut, Deref, Display)]
pub struct Index(usize);

impl ops::Add<usize> for Index {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        (*self + rhs).into()
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, From, AsRef, AsMut, Deref, Display)]
pub struct Level(usize);

impl ops::Add<usize> for Level {
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

pub struct ConsVec<T>(im_rc::Vector<T>);

impl<T: Clone> ConsVec<T> {
    pub fn new() -> ConsVec<T> {
        ConsVec(im_rc::Vector::new())
    }
}

impl<T> ops::Deref for ConsVec<T> {
    type Target = im_rc::Vector<T>;
    fn deref(&self) -> &Self::Target { &self.0 }
}

impl<T> ops::DerefMut for ConsVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl<T: Clone> Clone for ConsVec<T> {
    fn clone(&self) -> Self { Self(self.0.clone()) }
}

impl<T: fmt::Debug + Clone> fmt::Debug for ConsVec<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ConsVec").field(&self.0).finish()
    }
}
