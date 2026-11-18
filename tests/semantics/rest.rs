pub enum Shape { Pair(u8, u8), Empty }
pub struct Point(pub u8, pub u8);
pub fn enum_last(x: Shape) -> u8 { match x { Shape::Pair(.., last) => last, Shape::Empty => 0 } }
pub fn point_last(Point(.., last): Point) -> u8 { last }
pub fn tuple_middle((a, .., c): (u8, u8, u8)) -> u8 { a + c }
pub fn tuple_first((first, ..): (u8, u8)) -> u8 { first }
#[cfg(not(test))]
fn main() {
    assert_eq!(enum_last(Shape::Pair(3,9)), 9);
    assert_eq!(point_last(Point(3,9)), 9);
    assert_eq!(tuple_middle((1,2,4)), 5);
    assert_eq!(tuple_first((4,8)), 4);
}
