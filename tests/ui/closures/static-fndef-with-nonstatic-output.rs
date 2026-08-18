// Function item outlives components include lifetimes used by the instantiated signature.

fn returns<'a>() -> &'a str {
    ""
}

fn require_region<'a, T: 'a>(_: T) {}
fn require_static<T: 'static>(_: T) {}
fn require_for_all<T>(_: T)
where
    for<'a> T: 'a,
{
}

fn check_region<'a, 'b>() {
    require_region::<'a, _>(returns::<'b>);
}

fn check_static<'a>() {
    require_static(returns::<'a>);
    //~^ ERROR lifetime may not live long enough
}

fn check_indirect_static<'a: 'static, 'b>() {
    require_region::<'a, _>(returns::<'b>);
    //~^ ERROR lifetime may not live long enough
}

fn check_for_all<'a>() {
    require_for_all(returns::<'a>);
    //~^ ERROR lifetime may not live long enough
}

fn main() {}
