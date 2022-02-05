
use std::rc::Rc;

use crate::common::*;
use crate::kernel::value::{Value, Spine};

#[derive(Debug, Clone)]
pub enum MetaState {
    Unsolved,
    Frozen,
    Solved(Rc<Value>),
}


pub fn solve(env: Level, name: Symbol, spine: Spine, rhs: Rc<Value>) -> Result<(), ()> {
    todo!()
}
