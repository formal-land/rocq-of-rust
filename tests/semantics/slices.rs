fn main() {
    let empty: &[u8] = &[];
    assert_eq!((empty.len(), empty.is_empty()), (0, true));
    assert_eq!([3_u8, 4].as_slice().len(), 2);
    assert_eq!([(); 3].as_slice().len(), 3);
}
