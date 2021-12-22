
#[macro_use]
extern crate pest_derive;

mod repl;
mod database;
mod common;
mod kernel;
mod lang;

fn main() {
    repl::repl();
}
