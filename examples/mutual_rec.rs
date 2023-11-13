extern crate creusot_contracts;
use creusot_contracts::*;

#[ghost]
#[ensures(false)]
fn unsound1() {
    unsound2()
}

#[ghost]
#[ensures(false)]
fn unsound2() {
    unsound1()
}
