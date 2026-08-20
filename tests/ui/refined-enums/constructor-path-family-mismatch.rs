//@ edition: future
//@ compile-flags: -Z unstable-options

#![feature(refined_enums)]

enum Pair<T> {
    Pair<A, B>(A, B) -> Pair<(A, B)>,
}

enum Lit<T> {

    Int(i32) -> Lit<i32>,
}

fn main() {
    let _ = Pair::<(i32, bool)>::Pair::<bool, i32>;
    //~^ ERROR constructor result is incompatible with the family arguments on this path

    let _ = Lit::<bool>::Int;
    //~^ ERROR constructor result is incompatible with the family arguments on this path
}
