extern crate creusot_contracts;
use creusot_contracts::{
    invariant::Invariant,
    logic::{Int, Seq},
    *,
};

pub trait Gen {
    #[predicate]
    fn trans(self, x: u32, other: Self) -> bool;

    #[ensures(self.trans(result, ^self))]
    fn step(&mut self) -> u32;
}

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

impl Gen for Fib {
    #[predicate]
    #[open(self)]
    fn trans(self, x: u32, other: Self) -> bool {
        x == self.b && other.a == self.b && other.b == self.a + self.b
    }

    #[ensures(self.trans(result, ^self))]
    #[ensures(result@ > 1 ==> exists<f1: Fib, x: u32, f2: Fib> f1.trans(x, f2) && f2.trans(self.a, *self) && x + self.a == result)]
    fn step(&mut self) -> u32 {
        self.x = gh! { self.a };
        let next = self.a + self.b;
        self.a = self.b;
        self.b = next;
        self.a
    }
}

struct SkipZeros<G: Gen> {
    inner: G,
}

impl<G: Gen> Gen for SkipZeros<G> {
    #[predicate]
    #[open(self)]
    fn trans(self, x: u32, other: Self) -> bool {
        pearlite! {
            x@ != 0 && (self.inner.trans(x, other.inner) ||
            exists<s: Seq<G>> s.len() > 0 && self.inner.trans(0u32, s[0]) &&
                (forall<i: Int> 0 < i && i < s.len() ==> s[i-1].trans(0u32, s[i])) &&
                s[s.len()-1].trans(x, other.inner))
        }
    }

    #[ensures(self.trans(result, ^self))]
    fn step(&mut self) -> u32 {
        let mut next = self.inner.step();
        while next == 0 {
            next = self.inner.step();
        }
        next
    }
}

struct Hist<G: Gen> {
    inner: G,
    hist: Ghost<Seq<(G, u32)>>,
}

impl<G: Gen> Gen for Hist<G> {
    #[predicate]
    #[open(self)]
    fn trans(self, x: u32, other: Self) -> bool {
        self.inner.trans(x, other.inner)
    }

    #[ensures(self.trans(result, ^self))]
    fn step(&mut self) -> u32 {
        let old = gh! { self.inner };
        let x = self.inner.step();
        self.hist = gh! { self.hist.push((*old, x)) };
        x
    }
}

impl<G: Gen> Invariant for Hist<G> {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            (forall<i: Int> 0 < i && i < self.hist.len() ==> self.hist[i-1].0.trans(self.hist[i-1].1, self.hist[i].0)) &&
            self.hist[self.hist.len()-1].0.trans(self.hist[self.hist.len()-1].1, self.inner)
        }
    }
}
