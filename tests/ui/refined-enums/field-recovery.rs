//@ edition: future
//@ compile-flags: -Z unstable-options
//@ run-pass

#![feature(refined_enums)]
#![allow(dead_code)]

use std::mem::size_of;

enum Expr<T> {
    Value<A>(A) -> Expr<Option<A>>,
}

enum Pair<X, Y> {
    Swap<A, B> { first: A, second: B } -> Pair<B, A>,
}

fn main() {
    let value: Expr<Option<u8>> = Expr::Value(7u8);
    assert_eq!(size_of::<Expr<Option<u8>>>(), size_of::<u8>());
    match value {
        Expr::Value(inner) => assert_eq!(inner, 7),
    }

    let pair: Pair<bool, u16> = Pair::Swap::<u16, bool> { first: 9, second: true };
    match pair {
        Pair::Swap { first, second } => {
            assert_eq!(first, 9);
            assert!(second);
        }
    }
}
