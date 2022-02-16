use std::thread;

fn main() {
    env_logger::init();/* 
    let child = thread::Builder::new().stack_size(1024 * 1024 * 1024).spawn(|| { */
        cedille2::repl::repl();
/*     }).unwrap();

    child.join().unwrap(); */
}
