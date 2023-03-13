use crate::*;

#[rustc_diagnostic_item = "creusot_invariant"]
pub trait Invariant {
    #[predicate]
    #[rustc_diagnostic_item = "creusot_invariant_method"]
    fn invariant(self) -> bool;

    #[law]
    #[ensures(exists<x: Self> x.invariant())]
    fn is_inhabited()
    where
        Self: Sized;
}
