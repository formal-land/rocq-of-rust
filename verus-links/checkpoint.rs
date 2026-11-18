#[cfg(verus_only)]
use vstd::prelude::*;
#[cfg_attr(verus_only, verus_spec(ensures *final(p) == x,))]
pub fn set_word(p: &mut u32, x: u32) {
    *p = x;
    #[cfg(verus_only)]
    proof! { assert(*p == x); }
}
