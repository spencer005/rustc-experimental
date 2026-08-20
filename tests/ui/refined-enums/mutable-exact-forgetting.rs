//@ edition: future
//@ compile-flags: -Z unstable-options

#![feature(refined_enums)]

enum State<T> {

    A -> State<i32>,
    B -> State<i32>,
}

fn cannot_widen<'a>(state: &'a mut State<i32>::A) -> &'a mut State<i32> {
    state
    //~^ ERROR mismatched types
}

fn main() {}
