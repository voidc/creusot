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

/*
struct Fib {
    a: u32,
    b: u32,
    x: Ghost<u32>,
}

impl Invariant for Fib {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! { self.x.inner()@ + self.a@ == self.b@ }
    }
}

impl Iter for Fib {
    #[predicate]
    #[open(self)]
    fn produces(self, x: u32, other: Self) -> bool {
        x == self.b && other.a == self.b && other.b == self.a + self.b
    }

    #[law]
    #[open]
    #[requires(a.produces(x, b))]
    #[requires(a.produces(y, b))]
    #[ensures(x == y)]
    fn produces_inj(a: Self, x: u32, y: u32, b: Self) {}

    #[ensures(self.produces(result, ^self))]
    #[ensures(result@ > 1 ==> exists<f1: Fib, x: u32, f2: Fib> f1.produces(x, f2) && f2.produces(self.a, *self) && x + self.a == result)]
    fn next(&mut self) -> u32 {
        self.x = gh! { self.a };
        let next = self.a + self.b;
        self.a = self.b;
        self.b = next;
        self.a
    }
}

struct SkipZeros<I: Iter> {
    inner: I,
}

impl<I: Iter> Iter for SkipZeros<I> {
    #[predicate]
    #[open(self)]
    fn produces(self, x: u32, other: Self) -> bool {
        pearlite! {
            x@ != 0 && (self.inner.produces(x, other.inner) ||
            exists<s: Seq<I>> s.len() > 0 && self.inner.produces(0u32, s[0]) &&
                (forall<i: Int> 0 < i && i < s.len() ==> s[i-1].produces(0u32, s[i])) &&
                s[s.len()-1].produces(x, other.inner))
        }
    }

    #[law]
    #[open]
    #[requires(a.produces(x, b))]
    #[requires(a.produces(y, b))]
    #[ensures(x == y)]
    fn produces_inj(a: Self, x: u32, y: u32, b: Self) {}

    #[ensures(self.produces(result, ^self))]
    fn next(&mut self) -> u32 {
        let mut next = self.inner.next();
        while next == 0 {
            next = self.inner.next();
        }
        next
    }
}

struct Hist<I: Iter> {
    inner: I,
    hist: Ghost<Seq<(I, u32)>>,
}

impl<I: Iter> Iter for Hist<I> {
    #[predicate]
    #[open(self)]
    fn produces(self, x: u32, other: Self) -> bool {
        self.inner.produces(x, other.inner)
    }

    #[law]
    #[open]
    #[requires(a.produces(x, b))]
    #[requires(a.produces(y, b))]
    #[ensures(x == y)]
    fn produces_inj(a: Self, x: u32, y: u32, b: Self) {}

    #[ensures(self.produces(result, ^self))]
    fn next(&mut self) -> u32 {
        let old = gh! { self.inner };
        let x = self.inner.next();
        self.hist = gh! { self.hist.push((*old, x)) };
        x
    }
}

impl<I: Iter> Invariant for Hist<I> {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            (forall<i: Int> 0 < i && i < self.hist.len() ==> self.hist[i-1].0.produces(self.hist[i-1].1, self.hist[i].0)) &&
            self.hist[self.hist.len()-1].0.produces(self.hist[self.hist.len()-1].1, self.inner)
        }
    }
}
*/

struct SkipZerosHist<I: Iter> {
    inner: I,
    hist: Ghost<Seq<(I, u32)>>,
}

impl<I: Iter> SkipZerosHist<I> {
    pub fn new(inner: I) -> Self {
        SkipZerosHist {
            inner,
            hist: gh! { Seq::EMPTY },
        }
    }
}

impl<I: Iter> Iter for SkipZerosHist<I> {
    #[predicate]
    #[open(self)]
    fn produces(self, x: u32, other: Self) -> bool {
        pearlite! {
            x@ != 0 &&
            other.hist.len() > 0 &&
            self.inner == other.hist[0].0 &&
            (forall<i: Int> 0 <= i && i < other.hist.len()-1 ==> other.hist[i].1 == 0u32) &&
            other.hist[other.hist.len()-1].1 == x
        }
    }

    #[law]
    #[open]
    #[requires(a.produces(x, b))]
    #[requires(a.produces(y, b))]
    #[ensures(x == y)]
    fn produces_inj(a: Self, x: u32, y: u32, b: Self) {}

    #[ensures(self.produces(result, ^self))]
    fn next(&mut self) -> u32 {
        let old = gh! { self.inner };
        let mut next = self.inner.next();
        self.hist = gh! { Seq::singleton((*old, next)) };

        #[invariant(inv(self))]
        #[invariant(self.hist.len() > 0 && self.hist[0].0 == *old)]
        #[invariant(forall<i: Int> 0 <= i && i < self.hist.len()-1 ==> self.hist[i].1 == 0u32)]
        #[invariant(self.hist[self.hist.len()-1].1 == next)]
        while next == 0 {
            let prev = gh! { self.inner };
            next = self.inner.next();
            self.hist = gh! { self.hist.push((*prev, next)) };
        }
        next
    }
}

impl<I: Iter> Invariant for SkipZerosHist<I> {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            self.hist.len() > 0 ==>
            (forall<i: Int> 0 < i && i < self.hist.len() ==> self.hist[i-1].0.produces(self.hist[i-1].1, self.hist[i].0)) &&
            self.hist[self.hist.len()-1].0.produces(self.hist[self.hist.len()-1].1, self.inner)
        }
    }
}

pub fn client<I: Iter + Clone>(i: I, max: usize) {
    let mut i2 = SkipZerosHist::new(i.clone());
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
