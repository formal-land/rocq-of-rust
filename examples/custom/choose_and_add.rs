pub fn choose_u32(take_left: bool, left: u32, right: u32) -> u32 {
    if take_left { left } else { right}
}

pub fn add_pair(pair: (u32, u32)) -> u32 {
    pair.0 + pair.1
}

pub fn choose_and_add(take_left: bool, pair: (u32, u32), offset: u32) -> u32 {
    let selected = choose_u32(take_left, pair.0, pair.1);
    selected + offset
}

