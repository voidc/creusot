extern crate creusot_contracts;
use creusot_contracts::*;

// Why3 syntax error
enum Unsound {}

struct Inf(Box<Inf>);

#[trusted]
impl creusot_contracts::WellFounded for Inf {}

#[ghost]
#[ensures(false)]
fn unsound1(x: Unsound) {
    match x {}
}

#[ghost]
#[ensures(false)]
#[variant(x)]
fn unsound2(x: Inf) {
    unsound2(*x.0)
}
