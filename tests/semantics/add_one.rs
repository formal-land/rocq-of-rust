pub fn add_one(x: u32) -> u32 {
    x + 1
}

#[cfg(not(test))]
fn main() {
    assert_eq!(add_one(41), 42);
}
