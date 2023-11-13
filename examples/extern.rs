extern crate creusot_contracts;
use creusot_contracts::{vec, *};

pub fn test() {
    let mut v = vec![1, 2, 2, 3];
    v.dedup();
    proof_assert! { v@.len() == 3 };
}
