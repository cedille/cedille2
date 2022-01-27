use std::thread;

fn main() {
    env_logger::init();
    cedille2::repl::repl();
/*     let child = thread::Builder::new().stack_size(1024 * 1024 * 1024).spawn(|| {
        
    }).unwrap();

    child.join().unwrap(); */
}
