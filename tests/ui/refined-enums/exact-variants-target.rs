//@ edition: future
//@ compile-flags: -Z unstable-options

#![feature(refined_enums)]

#[exact_variants]
//~^ ERROR the `exact_variants` attribute cannot be used on structs
struct NotAnEnum;

fn main() {}
