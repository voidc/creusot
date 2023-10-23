extern crate creusot_contracts;
use creusot_contracts::{
    logic::{Int, Seq},
    *,
};

#[logic]
#[open]
#[variant(s.len())]
pub fn sum(s: Seq<i32>) -> Int {
    pearlite! {
        if s.len() == 0 {
            0
        } else {
            s[0]@ + sum(s.tail())
        }
    }
}

pub trait Gen {
    #[predicate]
    #[ensures(result ==> sum(visited) < i32::MAX@)]
    fn produces(self, visited: Seq<i32>, _o: Self) -> bool;

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self);

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<i32>, b: Self, bc: Seq<i32>, c: Self);

    #[ensures((*self).produces(Seq::singleton(result), ^self))]
    fn next(&mut self) -> i32;
}

#[ensures(exists<s: Seq<i32>> s.len() == n@ && g.produces(s, ^g) && result@ == sum(s))]
pub fn sum_n<G: Gen>(g: &mut G, n: usize) -> i32 {
    let old_g = gh! { g };
    let mut r = 0;
    let mut i = 0;
    #[invariant(exists<s: Seq<i32>> s.len() == i@ && old_g.produces(s, *g) && r@ == sum(s))]
    while i < n {
        r += g.next();
        i += 1;
    }
    r
}

#[ensures(exists<s: Seq<i32>> s.len() == n@ && g.produces(s, ^g) && result@ == sum(s))]
pub fn sum_n_elim<G: Gen>(g: &mut G, n: usize) -> i32 {
    let old_g = gh! { g };
    let mut r = 0;
    let mut i = 0;
    let mut s = gh! { Seq::EMPTY };
    #[invariant(s.len() == i@ && old_g.produces(*s, *g) && r@ == sum(*s))]
    while i < n {
        let x = g.next();
        s = gh! { s.push(x) };
        r += x;
        i += 1;
    }
    r
}

pub trait Func {
    #[predicate]
    #[ensures(forall<y2: i32> self.has(x, y) && self.has(x, y2) ==> y == y2)]
    fn has(&self, x: i32, y: i32) -> bool;

    #[ensures(self.has(x, result))]
    fn f(&self, x: i32) -> i32;
}

#[requires(x_min <= x_max)]
#[ensures(
    exists<xs: Seq<i32>> result@ == xs.len() &&
        (forall<i: Int, j: Int> 0 <= i && i < j && j < xs.len() ==> xs[i] < xs[j]) &&
        (forall<x: i32> (x_min <= x && x < x_max && f.has(x, 0i32)) == xs.contains(x))
)]
pub fn count_zero<F: Func>(f: F, x_min: i32, x_max: i32) -> usize {
    let mut count = 0;
    let mut zeros = gh! { Seq::EMPTY };
    let mut x = x_min;

    #[invariant(count@ == zeros.len())]
    #[invariant(forall<i: Int, j: Int> 0 <= i && i < j && j < zeros.len() ==> zeros[i] < zeros[j])]
    #[invariant(forall<x2: i32> (x_min <= x2 && x2 < x && f.has(x2, 0i32)) == zeros.contains(x2))]
    #[invariant(count@ <= x@-x_min@ && x_min <= x && x <= x_max)]
    while x < x_max {
        if f.f(x) == 0 {
            count += 1;
            zeros = gh! { zeros.push(x) };
        }
        x += 1;
    }

    count
}

#[requires(x_min <= x_max)]
#[ensures(
    exists<xs: Seq<i32>> result@ == xs.len() &&
        (forall<i: Int, j: Int> 0 <= i && i < j && j < xs.len() ==> xs[i] < xs[j]) &&
        (forall<x: i32> (x_min <= x && x < x_max && f.has(x, 0i32)) == xs.contains(x))
)]
pub fn count_zero2<F: Func>(f: F, x_min: i32, x_max: i32) -> usize {
    let mut count = 0;
    let mut x = x_min;

    #[invariant(
        exists<xs: Seq<i32>> count@ == xs.len() &&
            (forall<i: Int, j: Int> 0 <= i && i < j && j < xs.len() ==> xs[i] < xs[j]) &&
            (forall<x2: i32> (x_min <= x2 && x2 < x && f.has(x2, 0i32)) == xs.contains(x2))
    )]
    #[invariant(count@ <= x@-x_min@ && x_min <= x && x <= x_max)]
    while x < x_max {
        if f.f(x) == 0 {
            count += 1;
        }
        x += 1;
    }

    count
}
