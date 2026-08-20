//@ edition: future
//@ compile-flags: -Z unstable-options

#![feature(refined_enums)]
#![deny(improper_ctypes)]

#[repr(C)]
enum State {
    A,
    B,
}

#[repr(transparent)]
struct Wrapped(State::A);

#[repr(C)]
enum Indexed<T> {
    Int(i32) -> Indexed<i32>,
    Bool(bool) -> Indexed<bool>,
}

unsafe extern "C" {
    fn exact(value: State::A);
    //~^ ERROR `extern` block uses type `State::A`, which is not FFI-safe
    fn wrapped(value: Wrapped);
    //~^ ERROR `extern` block uses type `State::A`, which is not FFI-safe
    fn indexed(value: Indexed<i32>);
    //~^ ERROR `extern` block uses type `Indexed<i32>`, which is not FFI-safe
}

fn main() {}
