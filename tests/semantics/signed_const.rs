pub fn signed<const N: i8>() -> i8 { N }
pub fn unsigned<const N: u8>() -> u8 { N }
pub fn negative() -> i8 { signed::<{-1}>() }
pub fn minimum() -> i8 { signed::<{-128}>() }
pub fn maximum_byte() -> u8 { unsigned::<255>() }
#[cfg(not(test))]
fn main() {
    assert_eq!((negative(), minimum(), maximum_byte()), (-1, -128, 255));
}
