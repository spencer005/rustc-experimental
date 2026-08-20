//@ edition: future
//@ compile-flags: -Z unstable-options
//@ run-pass

#![feature(refined_enums)]
#![allow(incomplete_features)]

enum Forms<T> {

    Unit -> Forms<i32>,
    Tuple(bool) -> Forms<bool>,
    Struct { value: u8 } -> Forms<u8>,
}

fn main() {
    let unit: Forms<i32> = Forms::Unit;
    assert!(matches!(unit, Forms::Unit));

    let tuple: Forms<bool> = Forms::Tuple(true);
    match tuple {
        Forms::Tuple(value) => assert!(value),
        _ => panic!(),
    }

    let strukt: Forms<u8> = Forms::Struct { value: 7 };
    match strukt {
        Forms::Struct { value } => assert_eq!(value, 7),
        _ => panic!(),
    }

    let exact = Forms::Struct { value: 9 };
    let shared: &Forms<u8> = &exact;
    match shared {
        Forms::Struct { value } => assert_eq!(*value, 9),
        _ => panic!(),
    }
}
