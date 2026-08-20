//@ edition: future
//@ compile-flags: -Z unstable-options

#![feature(refined_enums)]

enum Exists<T> {
    Keep(T),
    Pack<U>(U) -> Exists<i32>,
    //~^ ERROR constructor binder `U` is not recoverable from the declared result `Exists<i32>`
}

trait Assoc {
    type Output;
}

enum Projected<T> {

    Keep(T),
    Project<U: Assoc>(U) -> Projected<U::Output>,
    //~^ ERROR constructor binder `U` is not recoverable from the declared result
}

fn main() {}
