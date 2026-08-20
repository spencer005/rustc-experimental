//@ edition: future
//@ compile-flags: -Z unstable-options
//@ run-pass

#![feature(refined_enums)]

#[exact_variants]
enum State {
    A,
    B,
}

impl State {
    fn value(&self) -> u8 {
        0
    }
}

impl State::A {
    fn value(&self) -> u8 {
        1
    }
}

fn main() {
    let exact = State::A;
    assert_eq!(exact.value(), 1);

    let base: State = State::B;
    assert_eq!(base.value(), 0);
}
