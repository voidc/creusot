extern crate creusot_contracts;
use creusot_contracts::{
    invariant::{inv, Invariant},
    *,
};

struct S {}

impl Invariant for S {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        !inv(self)
    }
}

fn foo(x: S) {
    proof_assert! { false }
}

struct T {}

impl Invariant for T {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! { !exists<x: T> x == self }
    }
}

fn foo2(x: T) {
    proof_assert! { false }
}

struct S3;
impl Invariant for S3 {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! { forall<x: S3> false }
    }
}

fn foo3(x: S3) {
    proof_assert! { false }
}
