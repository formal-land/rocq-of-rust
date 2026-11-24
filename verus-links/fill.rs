#![cfg_attr(verus_only, feature(proc_macro_hygiene))]

#[cfg(verus_only)]
use vstd::prelude::*;

#[cfg_attr(verus_only, verus_spec(
    requires n <= old(xs)@.len(),
    ensures
        final(xs)@.len() == old(xs)@.len(),
        forall|j: int| 0 <= j < n ==> final(xs)@[j] == value,
        forall|j: int| n <= j < old(xs)@.len() ==> final(xs)@[j] == old(xs)@[j],
))]
pub fn fill_prefix(xs: &mut [u32], n: usize, value: u32) {
    let mut i: usize = 0;
    #[cfg_attr(verus_only, verus_spec(
        invariant
            i <= n <= xs@.len(),
            xs@.len() == old(xs)@.len(),
            forall|j: int| 0 <= j < i ==> xs@[j] == value,
            forall|j: int| i <= j < old(xs)@.len() ==> xs@[j] == old(xs)@[j],
        decreases n - i,
    ))]
    while i < n {
        xs[i] = value;
        i = i + 1;
    }
}
