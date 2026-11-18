pub fn mixed_left(x: u8, n: u32) -> u8 { x << n }
pub fn signed_right(x: i8, n: u16) -> i8 { x >> n }

#[cfg(not(test))]
fn main() {
    assert_eq!(128_u8.checked_shl(1), Some(0));
    assert_eq!(1_u8.checked_shr(8), None);
    for n in [7, 8, 9] {
        assert_eq!(mixed_left(1, n), 1u8.wrapping_shl(n));
        assert_eq!(signed_right(-128, n as u16), (-128i8).wrapping_shr(n));
    }
}
