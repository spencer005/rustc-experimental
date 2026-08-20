//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]
#![allow(dead_code)]

enum Expr<T> {

    Keep(T),
    Int(i32) -> Expr<i32>,
    Pair<A: Clone, B>(Box<Expr<A>>, Box<Expr<B>>) -> Expr<(A, B)>,
    Borrow<'a, U: ?Sized>(&'a U) -> Expr<&'a U>,
    Array<const N: usize>([u8; N]) -> Expr<[u8; N]>,
}

fn main() {}

