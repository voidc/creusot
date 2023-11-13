extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct SumTo10<T> {
    a: i32,
    b: T,
}

impl Invariant for SumTo10<i32> {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

fn foo() {
    let mut s = SumTo10 { a: 3, b: 7i32 };
    let r = &mut s;
}

#[ensures((^s).a == 0)]
#[ensures((^s).b == (*s).b)]
fn bar<T>(s: &mut SumTo10<T>) {
    *s.a = 0;
}
