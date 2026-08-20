//@ edition: future
//@ compile-flags: -Z unstable-options

#![feature(refined_enums)]

struct Other<T>(T);

enum Expr<T> {
    Wrong<U>(U) -> Other<U>,
    //~^ ERROR constructor result must be an application of its enum family `Expr`

}

fn main() {}