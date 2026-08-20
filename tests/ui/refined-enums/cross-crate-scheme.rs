//@ edition: future
//@ compile-flags: -Z unstable-options
//@ aux-build:refined-enum-upstream.rs
//@ check-pass

#![feature(refined_enums)]

extern crate refined_enum_upstream as upstream;

fn main() {
    let _: fn(i32, bool) -> upstream::Pair<(i32, bool)> =
        upstream::Pair::<(i32, bool)>::Pair::<i32, bool>;
    let _: fn(i32) -> upstream::Lit<i32> = upstream::Lit::<i32>::Int;
    let _: fn(u8) -> upstream::Defaulted<u8>::Keep = upstream::Defaulted::<u8>::Keep;
}
