pub fn tuple_assignment() -> (u64, u64) {
    let mut lhs = 1_u64;
    let mut carry = 3_u64;

    (lhs, carry) = (4_u64, 5_u64);

    (lhs, carry)
}
