//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]
#![allow(dead_code)]

#[exact_variants]

enum State<T> {

    Keep(T),
    A -> State<i32>,
    B -> State<i32>,
}

fn conditionally_uninhabited<T>() -> State<T>::A {
    loop {}
}

fn caller_family_is_preserved<T>(state: State<T>::A) -> State<T> {
    state
}

fn default_variant(value: u8) -> State<u8>::Keep {
    State::Keep(value)
}

fn owned_forget() -> State<i32> {
    State::A
}

fn shared_shorter<'long, 'short>(x: &'long State<i32>::A) -> &'short State<i32>
where
    'long: 'short,
{
    x
}

fn mutable_shorter<'long, 'short>(x: &'long mut State<i32>::A) -> &'short mut State<i32>::A
where
    'long: 'short,
{
    x
}

fn sibling_join(flag: bool) -> State<i32> {
    let state = if flag { State::A } else { State::B };
    state
}

fn main() {
    let _: fn(u8) -> State<u8>::Keep = State::<u8>::Keep;
    let _: State<i32>::A = State::A;
}
