struct Mark<'a>(&'a mut u8);
impl Drop for Mark<'_> { fn drop(&mut self) { *self.0 = 7; } }
fn main() {
    let mut seen = 0;
    let guard = Mark(&mut seen);
    let result = None::<u8>.map(move |n| { drop(guard); n + 1 });
    assert_eq!((result, seen), (None, 7));
    assert_eq!(Some(4).map(|n| n + 1), Some(5));
}
