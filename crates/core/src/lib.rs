
pub mod co;
pub mod hc;
pub mod utility;
pub mod term;
pub mod value;
pub mod eval;
pub mod unify;
pub mod metavar;
pub mod database;
pub mod parser;
pub mod infer;

pub mod prelude {
    pub use crate::{
        hc::*, 
        utility::*, 
        term::*, 
        value::*, 
        eval::*, 
        unify::*, 
        metavar::*,
        database::*,
        parser,
    };

    pub mod core {
        pub use crate::infer::*;
    }
}
