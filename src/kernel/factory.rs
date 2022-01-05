
use std::ops::Deref;
use std::rc::{Rc, Weak};
use std::cell::{RefCell, RefMut};

use threadstack::*;
use slotmap::{new_key_type, HopSlotMap};

use crate::common::*;
use crate::kernel::value::{Value, LazyValue, EnvEntry, Closure};
use crate::lang::elaborator::References;

new_key_type! { struct FactoryKey; }
declare_thread_stacks!(
    FACTORY: RefCell<HopSlotMap<FactoryKey, Rc<Value>>> = RefCell::new(HopSlotMap::with_capacity_and_key(1024));
);

impl Value {
    pub fn variable(level: impl Into<Level>) -> Handle {
        Value::variable_with_spine(level, ConsVec::new())
    }

    pub fn variable_with_spine(level: impl Into<Level>, spine: ConsVec<EnvEntry>) -> Handle {
        let_ref_thread_stack_value!(factory, FACTORY);
        let mut factory = factory.borrow_mut();
        let value = Rc::new(Value::Variable { level:level.into(), spine });
        let key = factory.insert(value.clone());
        Handle(Rc::downgrade(&value), key.into())
    }

    pub fn reference(id: Id, spine: ConsVec<EnvEntry>, unfolded: Option<LazyValue>) -> Handle {
        let_ref_thread_stack_value!(factory, FACTORY);
        let mut factory = factory.borrow_mut();
        let value = Rc::new(Value::Reference { id, spine, unfolded });
        let key = factory.insert(value.clone());
        Handle(Rc::downgrade(&value), key.into())
    }

    pub fn lambda(mode: Mode, name: Symbol, closure: Closure) -> Handle {
        let_ref_thread_stack_value!(factory, FACTORY);
        let mut factory = factory.borrow_mut();
        let value = Rc::new(Value::Lambda { mode, name, closure });
        let key = factory.insert(value.clone());
        Handle(Rc::downgrade(&value), key.into())
    }

    pub fn pi(mode: Mode, name: Symbol, domain: impl Into<Handle>, closure: Closure) -> Handle {
        todo!()
    }

    pub fn intersect_type(name: Symbol, first: impl Into<Handle>, second: Closure) -> Handle {
        todo!()
    }

    pub fn equality(left: impl Into<Handle>, right: impl Into<Handle>) -> Handle {
        todo!()
    }

    pub fn star() -> Handle {
        todo!()
    }

    pub fn super_star() -> Handle {
        todo!()
    }
}

/// Used to garbage collect references that only exist in the factories internal data.
#[derive(Debug, Clone)]
struct CollectionHint(FactoryKey);

impl From<FactoryKey> for CollectionHint {
    fn from(key: FactoryKey) -> Self { CollectionHint(key) }
}

impl Drop for CollectionHint {
    fn drop(&mut self) {
        let_ref_thread_stack_value!(factory, FACTORY);
        let mut factory = factory.borrow_mut();
        let key = self.0;
        // First, we get the reference into the internal data.
        // Note that this can't fail.
        // Either there is only one reference left, in which case it must be in the factory, or there are many
        // references left, in which case one of them must be in the factory.
        let ptr = factory.get(key).unwrap();
        let count = Rc::weak_count(ptr) + Rc::strong_count(ptr);
        // If there is only one reference to the internal data, it must be the factories own reference.
        // Thus, it is save to remove this from the factory.
        if count == 1 {
            // After, the internal data itself will be dropped and a cascade of garbage collection will happen.
            factory.remove(key);
        }
    }
}

/// Wrapper for reference counted pointers.
/// Factories need to support cyclic references, so `Rc` is not sufficient on its own.
/// Should be used sparingly and always be short lived.
#[derive(Debug, Clone)]
pub struct StrongHandle(Rc<Value>, CollectionHint);

impl Deref for StrongHandle {
    type Target = Value;
    fn deref(&self) -> &Value { self.0.deref() }
}

/// Wrapper for weak references.
#[derive(Debug, Clone)]
pub struct Handle(Weak<Value>, CollectionHint);

impl Handle {
    pub fn upgrade(handle: &Handle) -> StrongHandle {
        let Handle(ptr, hint) = handle;
        // Upgrading at this point can't fail.
        // Because if a weak handle exists then the associated data must exist in the factory.
        let ptr = Weak::upgrade(ptr).unwrap();
        StrongHandle(ptr, hint.clone())
    }

    pub fn apply(&self, refs: References, arg: EnvEntry) -> Handle {
        let ptr = Handle::upgrade(self);
        ptr.0.apply(refs, arg)
    }
}
