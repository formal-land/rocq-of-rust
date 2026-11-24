pub fn quotient(x: i8, y: i8) -> i8 { x / y }
pub fn remainder(x: i8, y: i8) -> i8 { x % y }

#[cfg(not(test))]
fn main() {
    assert_eq!((quotient(-7, 3), remainder(-7, 3)), (-2, -1));
    std::panic::set_hook(Box::new(|_| {}));
    for (a, b) in [(7, 0), (i8::MIN, -1)] {
        assert!(std::panic::catch_unwind(|| quotient(a, b)).is_err());
        assert!(std::panic::catch_unwind(|| remainder(a, b)).is_err());
    }
}
