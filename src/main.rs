
#[macro_use]
extern crate pest_derive;


mod repl;
mod syntax;

fn main() {
    repl::repl();
}
