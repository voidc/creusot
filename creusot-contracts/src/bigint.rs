use crate as creusot_contracts;
use crate::*;
use ::std::ops::*;
use num_bigint::BigInt;

impl crate::Model for num_bigint::BigInt {
    type ModelTy = crate::Int;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        pearlite! { absurd }
    }
}

extern_spec! {
    mod num_bigint {
        impl From<i32> for BigInt {
            #[ensures(@result == @i)]
            fn from(i: i32) -> BigInt;
        }

        impl PartialEq<BigInt> for BigInt {
            #[ensures(result == (@self== @rhs))]
            fn eq(&self, rhs: &BigInt) -> bool;
        }

        impl Add<BigInt> for BigInt {
            #[ensures(@result == @self + @rhs)]
            fn add(self, rhs: BigInt) -> BigInt;
        }


        impl Sub<BigInt> for BigInt {
            #[ensures(@result == @self - @rhs)]
            fn sub(self, rhs: BigInt) -> BigInt;
        }

        impl Mul<BigInt> for BigInt {
            #[ensures(@result == @self * @rhs)]
            fn mul(self, rhs: BigInt) -> BigInt;
        }

        impl Div<BigInt> for BigInt {
            #[requires(@rhs != 0)]
            #[ensures(@result == @self / @rhs)]
            fn div(self, rhs: BigInt) -> BigInt;
        }

        impl Clone for BigInt {
            #[ensures(result == *self)]
            fn clone(&self) -> BigInt;
        }
    }
}
