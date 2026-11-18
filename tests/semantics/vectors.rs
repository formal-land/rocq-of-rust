fn main() {
    let empty: Vec<u8> = Vec::new();
    assert!(empty.is_empty());
    assert_eq!(vec![2u16, 3].len(), 2);
    let zeros = vec![(); 3];
    assert_eq!(zeros.len(), 3);
    assert_eq!(zeros.capacity(), usize::MAX);
}
