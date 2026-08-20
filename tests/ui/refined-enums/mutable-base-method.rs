//@ edition: future
//@ compile-flags: -Z unstable-options

#![feature(refined_enums)]

enum State<T> {
    A -> State<i32>,
    B -> State<i32>,
}

impl State<i32> {
    fn replace_with_b(&mut self) {
        *self = State::B;
    }
}

fn cannot_call_base_mut(state: &mut State<i32>::A) {
    state.replace_with_b();
    //~^ ERROR no method named `replace_with_b` found for mutable reference `&mut State<i32>::A`
}

fn main() {}
