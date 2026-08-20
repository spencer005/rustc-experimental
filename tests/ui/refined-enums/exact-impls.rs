//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]

enum State<T> {

    A -> State<i32>,
    B -> State<i32>,
}

impl<T> State<T> {
    fn base_owned(self) -> Self {
        self
    }

    fn base_shared(&self) -> bool {
        true
    }

    fn base_mut(&mut self, replacement: Self) {
        *self = replacement;
    }
}

trait Marker {
    fn marker(&self) -> i32;
}

impl State<i32>::A {
    fn into_base(self) -> State<i32> {
        self
    }

    fn shared_base(&self) -> &State<i32> {
        self
    }
}

impl Marker for State<i32>::A {
    fn marker(&self) -> i32 {
        1
    }
}

fn call_base_owned(value: State<i32>::A) -> State<i32> {
    value.base_owned()
}

fn call_base_shared(value: &State<i32>::A) -> bool {
    value.base_shared()
}

fn main() {
    let value: State<i32>::A = State::A;
    assert_eq!(value.marker(), 1);
    let _: &State<i32> = value.shared_base();
    let _: State<i32> = value.into_base();
}
