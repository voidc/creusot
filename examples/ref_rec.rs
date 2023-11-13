extern crate creusot_contracts;
use creusot_contracts::*;

trait Func {
    #[ghost]
    #[ensures(false)]
    fn call(&self);
}

enum Rec<'a, F: Func> {
    Trivial,
    Ref(Ghost<&'a mut F>),
}

impl<'a, F: Func> Func for Rec<'a, F> {
    #[ghost]
    #[ensures(false)]
    fn call(&self) {
        match self {
            Trivial => {}
            Ref(r) => r.inner().call(),
        }
    }
}

fn unsound() {
    let mut f = Trivial;
    let r = &mut f;
    let rec = Rec { f: gh! { r } };
    *r = rec;
    gh! { f.call() };
}
