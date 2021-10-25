
#[macro_use]
extern crate pest_derive;

mod repl;
mod parser;
mod syntax;
mod database;

fn main() {
    repl::repl();
}
