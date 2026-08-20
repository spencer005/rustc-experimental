//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]
#![allow(dead_code)]

enum Lit<T> {

    Int(i32) -> Lit<i32>,
    Bool(bool) -> Lit<bool>,
}

fn main() {}
