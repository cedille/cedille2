use std::hash;
use std::fmt;
use std::ops::Deref;
use std::ptr;
use std::borrow::Borrow;
use std::rc::{Rc, Weak};

use ahash::AHashMap;

#[derive(Debug, Clone)]
pub struct Hc<T>(Rc<T>);

impl<T> Hc<T> {
    fn inner(&self) -> &Rc<T> {
        let Hc(inner) = self;
        inner
    }
}

impl<T: Clone> Hc<T> {
    pub fn cloned(&self) -> T {
        let inner = self.inner().clone();
        let other: &T = inner.borrow();
        other.clone()
    }
}

impl<T> PartialEq for Hc<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(self.inner(), other.inner())
    }
}
impl<T> Eq for Hc<T> { }

impl<T: hash::Hash> hash::Hash for Hc<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        ptr::hash(Rc::as_ptr(self.inner()), state);
    }
}

impl<T> Deref for Hc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner()
    }
}

impl<T : fmt::Display> fmt::Display for Hc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Hc(inner) = self;
        inner.fmt(f)
    }
}

impl<T> Hc<T> {
    fn to_weak(&self) -> WeakHc<T> {
        let weak = Rc::downgrade(self.inner());
        WeakHc(weak)
    }
}

#[derive(Debug, Clone)]
struct WeakHc<T>(Weak<T>);

impl<T> WeakHc<T> {
    fn inner(&self) -> &Weak<T> {
        let WeakHc(inner) = self;
        inner
    }

    fn upgrade(&self) -> Option<Hc<T>> {
        self.inner()
            .upgrade()
            .map(Hc)
    }
}

#[derive(Debug)]
pub struct HcFactory<T: hash::Hash + Eq + Clone> {
    table: AHashMap<T, WeakHc<T>>,
}

impl<T: hash::Hash + Eq + Clone> HcFactory<T> {
    pub fn with_capacity(capacity: usize) -> HcFactory<T> {
        HcFactory {
            table: AHashMap::with_capacity(capacity)
        }
    }

    pub fn get(&self, element: &T) -> Option<Hc<T>> {
       self.table
            .get(element)
            .map(|w| w.upgrade())
            .flatten()
    }

    pub fn make(&mut self, element: T) -> Hc<T> {
        if let Some(hc) = self.get(&element) {
            hc
        } else {
            let rc = Rc::new(element.clone());
            let result = Hc(rc);
            self.table.insert(element, result.to_weak());
            result
        }
    }
}
