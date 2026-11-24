#![allow(incomplete_features, dead_code)]
#![feature(generic_const_exprs)]
pub trait Width<const N: usize> { const VALUE: usize; }
pub fn symbolic<T: Width<N>, const N: usize>(x: [u8; T::VALUE]) -> [u8; T::VALUE] { x }
pub fn plus_one<const N: usize>(x: [u8; N + 1]) -> [u8; N + 1] { x }
fn main() {}
