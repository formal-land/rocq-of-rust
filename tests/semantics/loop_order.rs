fn digits() -> u32 {
    let mut result = 0;
    let mut i = 0;
    while i < 3 {
        result = result * 10 + i;
        i += 1;
    }
    result
}

fn main() {
    assert_eq!(digits(), 12);
}
