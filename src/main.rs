
fn main() {
    env_logger::init();
    stacker::grow(8*1024*1024, || {
        cedille2::repl::repl();
    });
}
