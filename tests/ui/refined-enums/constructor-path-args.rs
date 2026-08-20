//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]
#![allow(dead_code)]

enum Pair<T> {
    Pair<A, B>(A, B) -> Pair<(A, B)>,
}

enum Lit<T> {

    Int(i32) -> Lit<i32>,
}

fn main() {
    let _: fn(i32, bool) -> Pair<(i32, bool)> = Pair::<(i32, bool)>::Pair::<i32, bool>;
    let _: fn(i32, bool) -> Pair<(i32, bool)> = Pair::Pair::<i32, bool>;
    let _: fn(i32) -> Lit<i32> = Lit::<i32>::Int;
}
