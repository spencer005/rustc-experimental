//@ edition: future
//@ compile-flags: -Z unstable-options

#[exact_variants]
//~^ ERROR the `exact_variants` attribute is an experimental feature

enum State {
    A,
}

fn main() {}

