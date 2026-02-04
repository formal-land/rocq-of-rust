// Simple saturating counter in Rust
pub struct Counter {
    pub value: u64,
}

const MAX_VALUE: u64 = 1000;

impl Counter {
    pub fn increment(&mut self, amount: u64) {
        if self.value + amount > MAX_VALUE {
            self.value = MAX_VALUE;
        } else {
            self.value += amount;
        }
    }
}
