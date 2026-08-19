fn match_value(value: u32) -> u32 {
    match value {
        captured => captured,
    }
}

fn match_ref(value: u32) -> u32 {
    match value {
        ref captured => *captured,
    }
}

fn match_ref_mut(value: &mut u32) -> u32 {
    match *value {
        ref mut captured => {
            *captured += 1;
            *captured
        }
    }
}

fn match_reference(value: &u32) -> u32 {
    match value {
        &captured => captured,
    }
}

fn match_mutable_reference(value: &mut u32) -> u32 {
    match value {
        &mut captured => captured,
    }
}
