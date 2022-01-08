
use env_logger::Builder;

fn main() {
    env_logger::init();
    cedille2::repl::repl();
}
