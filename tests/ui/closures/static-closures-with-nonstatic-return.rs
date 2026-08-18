// A closure whose signature contains a non-`'static` lifetime cannot be `'static`,
// even when it captures no values.

#[allow(dead_code)]
fn foo<'a>() {
    let closure = || -> &'a str { "" };
    assert_static(closure);
    //~^ ERROR lifetime may not live long enough
}

fn assert_static<T: 'static>(_: T) {}

fn main() {}
