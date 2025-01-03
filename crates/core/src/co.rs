
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Co<T> {
    Yield(T),
    Return(T)
}

#[derive(Debug)]
struct CoFn<S, O> {
    generator: fn(&mut S),
    resultor: fn(&S) -> Co<O>,
    state: S,
}

impl<S, O> CoFn<S, O> {
    pub fn new<I>(
        generator: fn(&mut S),
        initializer: fn(I) -> S,
        resultor: fn(&S) -> Co<O>)
    -> impl Fn(I) -> CoFn<S, O>
    {
        move |x| {
            CoFn {
                generator,
                resultor,
                state: initializer(x),
            }
        }
    }

    pub fn poll(&mut self) -> Co<O> {
        let result = (self.resultor)(&self.state);
        (self.generator)(&mut self.state);
        result
    }
}

mod tests {
    use super::*;

    #[test]
    fn fib() {
        let generator = |(x, y) : &mut (u64, u64)| {
            let temp = *x + *y;
            *y = *x;
            *x = temp;
        };
        let resultor = |(x, _) : &(u64, u64)| { Co::Yield(*x) };
        let initializer = |()| (1, 0);
        let cofn = CoFn::new(generator, initializer, resultor);
        let mut f = cofn(());
        assert_eq!(f.poll(), Co::Yield(1));
        assert_eq!(f.poll(), Co::Yield(1));
        assert_eq!(f.poll(), Co::Yield(2));
        assert_eq!(f.poll(), Co::Yield(3));
        assert_eq!(f.poll(), Co::Yield(5));
        assert_eq!(f.poll(), Co::Yield(8));
        assert_eq!(f.poll(), Co::Yield(13));
        assert_eq!(f.poll(), Co::Yield(21));
    }
}
