
pub mod symbol;
pub mod debruijn;

use symbol::Symbol;

#[derive(Debug, Hash, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id {
    pub namespace: Vec<Symbol>,
    pub name: Symbol,
}
