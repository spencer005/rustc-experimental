//@ edition: future
//@ compile-flags: -Z unstable-options
#![feature(refined_enums)]

pub enum Pair<T> {
    Pair<A, B>(A, B) -> Pair<(A, B)>,
}

pub enum Lit<T> {
    Int(i32) -> Lit<i32>,
}

#[exact_variants]
pub enum Defaulted<T> {
    Keep(T),
}


