
#[macro_use]
extern crate pest_derive;

mod repl;
mod parser;
mod syntax;
mod database;
mod kernel;
mod elaborator;
mod conversion;
mod reduction;

fn main() {
    repl::repl();
}
