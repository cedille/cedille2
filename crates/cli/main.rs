
mod repl;

use cedille2_core::checker::check;

fn main() {
    env_logger::init();
    repl::repl();
}
