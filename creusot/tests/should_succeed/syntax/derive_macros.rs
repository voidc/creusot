extern crate creusot_contracts;
use creusot_contracts::{
    derive::{Clone, PartialEq},
    *,
};

#[derive(Clone, PartialEq)]
pub struct Product<A, B> {
    a: A,
    b: B,
}

impl<A, B> Model for Product<A, B>
where
    A: Model,
    B: Model,
{
    type ModelTy = Product<A::ModelTy, B::ModelTy>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        Product { a: self.a.model(), b: self.b.model() }
    }
}

#[derive(Clone, PartialEq)]
pub enum Sum<A, B> {
    A(A),
    B(B),
}

impl<A: Model, B: Model> Model for Sum<A, B> {
    type ModelTy = Sum<A::ModelTy, B::ModelTy>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        match self {
            Sum::A(a) => Sum::A(a.model()),
            Sum::B(b) => Sum::B(b.model()),
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Term {
    Variable(bool),
    Plus(Box<Term>, Box<Term>),
    Eq(Box<Term>, Box<Term>),
    Conj(Box<Term>, Box<Term>),
    // TODO: complete others
}

// // impl PartialEq for Term {
// //     fn eq(&self, rhs: &Self) -> bool {
// //         match (self, rhs) {
// //             (Term::Variable(a_1), Term::Variable(a_2)) => a_1.eq(a_2),
// //             (Term::Plus(a_1, b_1), Term::Plus(a_2, b_2)) => a_1.eq(a_2) && b_1.eq(b_2),
// //             (Term::Eq(a_1, b_1), Term::Eq(a_2, b_2)) => a_1.eq(a_2)  && b_1.eq(b_2),
// //             (Term::Conj(a_1, b_1), Term::Conj(a_2, b_2)) => a_1.eq(a_2)  && b_1.eq(b_2),
// //             _ => false,
// //         }
// //     }
// // }

impl creusot_contracts::Model for Term {
    type ModelTy = Self;

    #[logic]
    fn model(self) -> Self {
        self
    }
}

// #[derive(PartialEq, Eq, Hash)]
// pub enum Value {
//     Bool(bool),
//     Rat(bool),
// }

// impl creusot_contracts::Model for Value {
//     type ModelTy = Self;

//     #[logic]
//     fn model(self) -> Self {
//         self
//     }
// }