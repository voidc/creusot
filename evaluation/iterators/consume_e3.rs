extern crate creusot_contracts;
use creusot_contracts::{logic::Int, std::iter::*, invariant::inv, *};

#[requires(n@ >= 0)]
#[ensures(result == n)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    let mut it = (0..n).into_iter();
    let iter_old = gh! { it };
    #[invariant(inv(it))]
    #[invariant(exists<produced: Seq<isize>>
        iter_old.produces(produced, it) && i@ == produced.len() && i <= n)]
    loop {
        match it.next() {
            Some(x) => {
                i += 1
            }
            None => break,
        }
    }
    i
}

#[ensures((^v)@.len() == v@.len())]
#[ensures(forall<i : _> 0 <= i && i < v@.len() ==> (^v)[i]@ == 0)]
pub fn all_zero(v: &mut Vec<usize>) {
    let mut it = v.iter_mut().into_iter();
    let iter_old = gh! { it };
    #[invariant(inv(it))]
    #[invariant(exists<produced: Seq<&mut usize>>
        iter_old.produces(produced, it) &&
        forall<i : Int> 0 <= i && i < produced.len() ==> (^produced[i])@ == 0)]
    loop {
        match it.next() {
            Some(x) => {
                *x = 0;
            }
            None => break,
        }
    }
}

// enumerate, zip (my_reverse)