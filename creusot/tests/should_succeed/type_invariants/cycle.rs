extern crate creusot_contracts;
use creusot_contracts::{invariant::Invariant, *};

pub struct WithInvariant;

impl Invariant for WithInvariant {
    #[predicate]
    #[creusot::type_invariant]
    fn invariant(self) -> bool {
        self.pred()
    }

    #[law]
    #[ensures(exists<x: Self> x.invariant())]
    fn is_inhabited()
    where
        Self: Sized,
    {
    }
}

impl WithInvariant {
    #[predicate]
    fn pred(self) -> bool {
        true
    }
}

pub fn id(x: WithInvariant) -> WithInvariant {
    x
}
