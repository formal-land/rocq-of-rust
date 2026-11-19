pub fn simple_order() -> u8 {
    let mut i = 0u8;
    let mut x = 10u8;
    *{ i += 1; &mut x } = i;
    x
}
pub fn primitive_order() -> u8 {
    let mut i = 0u8;
    let mut x = 10u8;
    *{ i += 1; &mut x } += i;
    x
}
#[cfg(not(test))]
fn main() {
    assert_eq!(simple_order(), 0);
    assert_eq!(primitive_order(), 10);
    assert_eq!(early_rhs(), 5);
    assert_eq!(overload(), 1);
}

#[allow(unreachable_code, unused_assignments)]
pub fn early_rhs() -> u8 {
    let mut i = 5;
    let mut x = 10;
    *{ i += 1; &mut x } = return i;
    x
}
pub struct Counter(u8);
impl std::ops::AddAssign<u8> for Counter {
    fn add_assign(&mut self, v: u8) { self.0 += v; }
}
pub fn overload() -> u8 {
    let mut i = 0;
    let mut x = Counter(0);
    *{ i += 1; &mut x } += i;
    x.0
}
