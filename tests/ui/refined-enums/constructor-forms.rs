//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]
#![allow(dead_code)]

enum Forms<T> {

    Unit -> Forms<i32>,
    Tuple(bool) -> Forms<bool>,
    Struct { value: u8 } -> Forms<u8>,
}

fn unit() -> Forms<i32> {
    Forms::Unit
}

fn tuple() -> Forms<bool> {
    Forms::Tuple(true)
}

fn strukt() -> Forms<u8> {
    Forms::Struct { value: 1 }
}

fn main() {}
