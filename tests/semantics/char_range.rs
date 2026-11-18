pub fn classify(c: char) -> u8 {
    match c {
        'α'..='γ' => 1,
        'x'..'z' => 2,
        '😺' => 3,
        _ => 0,
    }
}
#[cfg(not(test))]
fn main() {
    assert_eq!(['α', 'γ', 'δ', 'y', 'z', '😺', ' '].map(classify), [1,1,0,2,0,3,0]);
    assert!(!' '.is_ascii_graphic());
}
