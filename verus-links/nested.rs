#[cfg(verus_only)]
use vstd::prelude::*;

#[cfg_attr(verus_only, verus_verify)]
pub struct Pair { pub left: u32, pub right: u32 }

#[cfg_attr(verus_only, verus_verify)]
pub struct Outer { pub pair: Pair, pub sentinel: u32 }

#[cfg_attr(verus_only, verus_spec(
    ensures final(p).pair.left == old(p).pair.right,
            final(p).pair.right == old(p).pair.left,
            final(p).sentinel == old(p).sentinel,
))]
pub fn swap(p: &mut Outer) {
    let a = &mut p.pair.left;
    let b = &mut p.pair.right;
    let saved = *a;
    *a = *b;
    *b = saved;
}

#[cfg_attr(verus_only, verus_spec(r =>
    ensures *r == old(p).pair.left,
            final(p).pair.left == *final(r),
            final(p).pair.right == old(p).pair.right,
            final(p).sentinel == old(p).sentinel,
))]
pub fn left_mut(p: &mut Outer) -> &mut u32 {
    &mut p.pair.left
}

#[cfg_attr(verus_only, verus_spec(
    ensures final(p).pair.left == second,
            final(p).pair.right == old(p).pair.right,
            final(p).sentinel == old(p).sentinel,
))]
pub fn write_twice(p: &mut Outer, first: u32, second: u32) {
    let r = left_mut(p);
    *r = first;
    *r = second;
}
