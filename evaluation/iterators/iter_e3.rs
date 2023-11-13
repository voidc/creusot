extern crate creusot_contracts;
use creusot_contracts::{
    invariant::{inv, Invariant},
    logic::{Int, Seq},
    *,
};

pub trait Iter {
    #[predicate]
    fn produces(self, x: u32, other: Self) -> bool;

    #[law]
    #[requires(a.produces(x, b))]
    #[requires(a.produces(y, b))]
    #[ensures(x == y)]
    fn produces_inj(a: Self, x: u32, y: u32, b: Self);

    #[ensures(self.produces(result, ^self))]
    fn next(&mut self) -> u32;
}

struct SkipZeros<I: Iter> {
    inner: I,
}

impl<I: Iter> Iter for SkipZeros<I> {
    #[predicate]
    #[open(self)]
    fn produces(self, x: u32, other: Self) -> bool {
        pearlite! {
            x@ != 0 &&
            (exists<hist: Seq<I>> 
                hist.len() > 0 &&
                self.inner == hist[0] &&
                (forall<i: Int> 0 < i && i < hist.len() ==> hist[i-1].produces(0u32, hist[i])) &&
                hist[hist.len()-1].produces(x, other.inner))
        }
    }

    #[law]
    #[open]
    #[requires(a.produces(x, b))]
    #[requires(a.produces(y, b))]
    #[ensures(x == y)]
    fn produces_inj(a: Self, x: u32, y: u32, b: Self) {
        I::produces_inj;
    }

    #[ensures(self.produces(result, ^self))]
    fn next(&mut self) -> u32 {
        let old = gh! { self.inner };
        let mut next = self.inner.next();

        #[invariant(inv(self))]
        #[invariant(exists<hist: Seq<I>>
            hist.len() > 0 &&
            *old == hist[0] &&
            (forall<i: Int> 0 < i && i < hist.len() ==> hist[i-1].produces(0u32, hist[i])) &&
            hist[hist.len()-1].produces(next, self.inner)
        )]
        while next == 0 {
            next = self.inner.next();
        }
        next
    }
}

pub fn client<I: Iter + Clone>(i: I, max: usize) {
    let mut i2 = SkipZeros { inner: i.clone() };
    let mut nz2 = Vec::new();
    let mut is = gh! { Seq::singleton(i2) };

    #[invariant(inv(i2))]
    #[invariant(inv(is))]
    #[invariant(nz2@.len() == produced.len())]
    #[invariant(is.len() == 1 + nz2@.len())]
    #[invariant(is[is.len()-1] == i2)]
    #[invariant(forall<j: Int> 0 < j && j < is.len() ==> is[j-1].produces(nz2[j-1], is[j]))]
    for _ in 0..max {
        nz2.push(i2.next());
        is = gh! { is.push(i2) };
    }

    let mut i1 = i;
    let mut nz1 = Vec::new();
    let mut count = 0;
    #[invariant(nz1@.len() == count@)]
    #[invariant(count <= max)]
    #[invariant(forall<k: Int> 0 <= k && k < count@ ==> nz1[k] == nz2[k])]
    while count < max {
        let x = i1.next();
        if x != 0 {
            proof_assert! { nz2[count@] == x };
            nz1.push(x);
            count += 1;
        }
    }

    proof_assert! { nz1@ == nz2@ };
}
