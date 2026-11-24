#![allow(dead_code)]
pub trait Capacity { fn marker() -> u8; }
const ONE: usize = 1;
const TWO: usize = 2;
impl<T> Capacity for [T; ONE] { fn marker() -> u8 { 11 } }
impl<T> Capacity for [T; TWO] { fn marker() -> u8 { 22 } }
fn main() { assert_eq!(<[u8; 1]>::marker(), 11); assert_eq!(<[u8; 2]>::marker(), 22); }
