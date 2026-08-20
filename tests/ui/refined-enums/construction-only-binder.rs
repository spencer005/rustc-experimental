//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]
#![allow(dead_code)]

trait CanMint {}

enum Token {

    Mint<Cap: CanMint> -> Token,
}

fn main() {}
