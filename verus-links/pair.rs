#[cfg(verus_only)]
use vstd::prelude::*;

#[cfg_attr(verus_only, verus_verify)]
pub struct Pair {
    pub left: u32,
    pub right: u32,
}

#[cfg_attr(verus_only, verus_spec(
    ensures final(p).left == old(p).right, final(p).right == old(p).right,
))]
pub fn copy_right(p: &mut Pair) {
    p.left = p.right;
}

#[cfg_attr(verus_only, verus_spec(r =>
    ensures *r == old(p).left, final(p).left == *final(r), final(p).right == old(p).right,
))]
pub fn left_mut(p: &mut Pair) -> &mut u32 {
    &mut p.left
}

#[cfg_attr(verus_only, verus_spec(
    ensures final(p).left == v, final(p).right == old(p).right,
))]
pub fn write_through(p: &mut Pair, v: u32) {
    *left_mut(p) = v;
}
