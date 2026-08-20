//@ edition: future
//@ compile-flags: -Z unstable-options

#![feature(refined_enums, auto_traits, negative_impls)]

enum State<T> {

    A -> State<i32>,
    B -> State<i32>,
}

auto trait Capability {}

impl Capability for State<i32>::A {}
//~^ ERROR explicit impl of `Capability` for an exact constructor type is not permitted

impl !Capability for State<i32>::B {}
//~^ ERROR explicit impl of `Capability` for an exact constructor type is not permitted

fn main() {}
