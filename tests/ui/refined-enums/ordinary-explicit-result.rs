//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]

enum Expr<T> {
    Keep(T) -> Expr<T>,
}

fn main() {}

