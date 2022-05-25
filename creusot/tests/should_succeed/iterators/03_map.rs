#![feature(unboxed_closures)]
extern crate creusot_contracts;

use creusot_contracts::{*, std::*};

mod common;
use common::*;

struct Map<I, F> {
    iter: I,
    func: F,
}

impl<I: Iterator, B, F: FnMut(I::Item) -> B> Iterator for Map<I, F>
where
    F: FnMutSpec<I::Item>,
    F: FnOnce<I::Item, Output = B>,
{
    type Item = B;

    #[predicate]
    fn completed(self) -> bool {
        self.iter.completed()
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            exists<is : Seq<I::Item>, fs : Seq<&mut F>>
                   self.iter.produces(is, succ.iter )
                && is.len() == fs.len()
                && fs.len() == visited.len()
                && (forall<i : Int> 1 <= i && i < fs.len() ==>  ^fs[i - 1] == * fs[i])
                && (visited.len() > 0 ==> (
                        * fs[0] == self.func
                    &&  ^ fs[visited.len() - 1] == succ.func))
                && forall<i : Int>
                    0 <= i && i < visited.len() ==>
                    fs[i].postcondition_mut(is[i], visited[i])
        }
    }

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(v) => Some((self.func)(v)),
            None => None,
        }
    }
}
