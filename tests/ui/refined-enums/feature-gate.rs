//@ edition: future
//@ compile-flags: -Z unstable-options

enum Expr<T> {
    Keep(T) -> Expr<T>,
    //~^ ERROR indexed enum constructor syntax is experimental

}


fn main() {}
