extern crate creusot_contracts;
use creusot_contracts::*;

fn append_zero(v: &mut Vec<u8>) {
    let old_v = gh! { v@ }; // take a snapshot
    v.push(0);
    proof_assert! { v@.subsequence(0, old_v.len()) == old_v.subsequence(0, old_v.len()) };
}
