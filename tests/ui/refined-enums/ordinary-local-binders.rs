//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]

enum Expr<T> {
    Pair<A>(A) -> Expr<A>,

}

fn main() {}

