//@ edition: future
//@ compile-flags: -Z unstable-options
//@ run-pass

#![feature(refined_enums)]

#[exact_variants]
enum State {
    Tuple(u16),
    Struct { value: u8 },
}

fn read(value: &State::Struct) -> &u8 {
    &value.value
}

fn main() {
    let tuple = State::Tuple(17);
    assert_eq!(tuple.0, 17);

    let strukt = State::Struct { value: 23 };
    assert_eq!(*read(&strukt), 23);
}
