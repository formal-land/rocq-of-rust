pub fn classify(x: u8) -> u8 {
    match x {
        0..=5 => 1,
        _ => 2,
    }
}
