//@ edition: future
//@ compile-flags: -Z unstable-options
//@ check-pass

#![feature(refined_enums)]
#![allow(dead_code)]

enum Plain<T> {
    Unit,
    Tuple(T),
    Struct { value: T },
}

impl<T> Plain<T> {
    fn replace(&mut self, replacement: Self) {
        *self = replacement;
    }
}

fn contextual_exact() {
    let _: Plain<i32>::Unit = Plain::Unit;
    let _: Plain<i32>::Tuple = Plain::Tuple(1);
    let _: Plain<i32>::Struct = Plain::Struct { value: 1 };
}

fn ordinary_still_widens() {
    let mut value = Plain::Tuple(1);
    value.replace(Plain::Unit);
}

#[exact_variants]
enum State<T> {
    Unit,
    Tuple(T),
    Struct { value: T },
}

impl State<i32>::Unit {
    fn unit_only(self) {}
}

impl State<i32>::Tuple {
    fn tuple_only(self) {}
}

impl State<i32>::Struct {
    fn struct_only(self) {}
}

fn exact_by_default() {
    State::<i32>::Unit.unit_only();
    State::Tuple(1).tuple_only();
    State::Struct { value: 1 }.struct_only();
}

enum Indexed<T> {
    A -> Indexed<i32>,
    B -> Indexed<i32>,
}

impl<T> Indexed<T> {
    fn replace(&mut self, replacement: Self) {
        *self = replacement;
    }
}

fn result_equations_do_not_imply_exactness() {
    let mut value = Indexed::A;
    value.replace(Indexed::B);
}

fn main() {
    contextual_exact();
    ordinary_still_widens();
    exact_by_default();
    result_equations_do_not_imply_exactness();
}
