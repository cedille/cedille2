
use std::{ops, fmt, mem};

use derive_more::{From, AsRef, AsMut, Deref, Display};
use internment::LocalIntern;
use tinyvec::{TinyVec, tiny_vec};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Display)]
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

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id {
    pub namespace: Vec<Symbol>,
    pub name: Symbol,
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
pub enum ApplyType {
    Free,
    TermErased,
    TypeErased
}

impl ApplyType {
    pub fn to_mode(self) -> Mode {
        match self {
            ApplyType::Free => Mode::Free,
            ApplyType::TermErased => Mode::Erased,
            ApplyType::TypeErased => Mode::Erased,
        }
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Mode {
    Erased,
    Free
}

impl Mode {
    pub fn to_apply_type(self, sort: &Sort) -> ApplyType {
        if *sort == Sort::Term { 
            match self {
                Mode::Free => ApplyType::Free,
                Mode::Erased => ApplyType::TermErased
            }
        }
        else { ApplyType::TypeErased }
    }
}

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sort {
    Term,
    Type,
    Kind
}

impl Sort {
    pub fn promote(self) -> Sort {
        match self {
            Sort::Term => Sort::Type,
            Sort::Type => Sort::Kind,
            Sort::Kind => Sort::Kind,
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, From, AsRef, AsMut, Deref)]
pub struct Index(usize);

impl ops::Add<usize> for Index {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        (*self + rhs).into()
    }
}

impl Index {
    pub fn to_level(self, env: usize) -> Level {
        (env - *self - 1).into()
    }
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "i{}", **self)
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
    pub fn to_index(self, env: usize) -> Index {
        (env - *self - 1).into()
    }
}

fn reverse<T: Default>(vec: TinyVec<[T; 4]>) -> TinyVec<[T; 4]> {
    let mut vec = vec;
    let len = vec.len();
    let (left, right) = vec.split_at_mut(len/2);
    let offset = if len % 2 == 0 { 1 } else { 0 };
    for i in 0..(len/2) {
        mem::swap(&mut left[i], &mut right[len/2 - i - offset]);
    }
    vec
}

pub enum Frame<C, I, R> {
    Recurse(I),
    RecurseWith(Box<dyn FnOnce(C, R) -> (R, I)>),
    Finish(Box<dyn FnOnce(C, R) -> R>),
    None
}

impl<C, I, R> Default for Frame<C, I, R> {
    fn default() -> Self { Frame::None }
}

impl<C, I: fmt::Debug, R> fmt::Debug for Frame<C, I, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Recurse(arg0) => f.debug_tuple("Recurse").field(arg0).finish(),
            Self::RecurseWith(..) => f.debug_tuple("RecurseWith(..)").finish(),
            Self::Finish(..) => f.debug_tuple("Finish(..)").finish(),
            Self::None => write!(f, "None")
        }
    }
}

pub fn tail_recurse<C: Copy, I: fmt::Debug, R>(
    mut stack: TinyVec<[Frame<C, I, R>; 4]>
    , mut acc: R
    , rec: fn(C, I) -> TinyVec<[Frame<C, I, R>; 4]>
    , ctx: C)
    -> R
{
    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Recurse(i) => {
                // Recursions are specified in the order they should be executed,
                // so they need to be added to the stack in reverse
                let mut commands = reverse(rec(ctx, i));
                stack.append(&mut commands);
            },
            Frame::RecurseWith(f) => {
                let (new_acc, i) = f(ctx, acc);
                acc = new_acc;
                let mut commands = reverse(rec(ctx, i));
                stack.append(&mut commands);
            }
            Frame::Finish(f) => acc = f(ctx, acc),
            Frame::None => unreachable!()
        }
    }
    acc
}

mod tests {
    use super::*;

    #[test]
    fn reverse_test() {
        let a = tiny_vec![0, 2];
        assert_eq!(tiny_vec![2, 0], reverse(a));
        let b = tiny_vec![1, 2, 3];
        assert_eq!(tiny_vec![3, 2, 1], reverse(b));
    }
}