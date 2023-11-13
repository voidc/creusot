extern crate creusot_contracts;
use creusot_contracts::*;

trait Foo {
    #[ghost]
    #[ensures(false)]
    fn f(&self);
}

#[ghost]
#[ensures(false)]
fn rec<T: Foo>(x: &T) {
    x.f();
}

struct Bar;
impl Foo for Bar {
    #[ghost]
    #[ensures(false)]
    fn f(&self) {
        // this produces invalid MLCFG:
        // this clones the module for rec, substituting with <Bar as Foo>
        // so Foo::f is substitututed with <Bar as Foo>::f
        // however <Bar as Foo>::f is only defined after the clone
        // creating a cyclic dependency
        rec(self);
    }
}

#[ghost]
#[ensures(false)]
fn unsound() {
    Bar.f();
}
