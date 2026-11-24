#![allow(unreachable_code)]
pub fn labeled(take: bool) -> u8 {
    if take { 'outer: { break 'outer; } 99 } else { 4 }
}
pub fn value_break(x: &mut u8) -> u8 {
    loop { break { *x = 42; 7 }; }
}
pub fn labeled_continue() {
    'outer: for _ in 0..1 { loop { continue 'outer; } }
}
pub fn unit_break() -> u8 { loop { break; } 9 }
pub fn float_literal() -> f32 { 1.5 }
fn main() {
    let mut x = 0;
    assert_eq!((value_break(&mut x), x), (7, 42));
    assert_eq!((labeled(true), labeled(false), unit_break()), (99, 4, 9));
    labeled_continue();
    assert_eq!(float_literal(), 1.5);
}
