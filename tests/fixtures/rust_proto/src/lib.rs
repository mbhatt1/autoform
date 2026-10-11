// Tiny pure crate for the Rust/Aeneas differential prototype (docs/rust.md).
pub fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

pub fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

pub fn add_wrapping(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

// Plain `+`: panics on overflow in a debug build, wraps in a release build.
// Aeneas models it as `fail integerOverflow`.
pub fn add_checked(a: u32, b: u32) -> u32 {
    a + b
}

pub fn sub_sat(a: i16, b: i16) -> i16 {
    a.saturating_sub(b)
}

pub fn div_floor_u8(a: u8, b: u8) -> u8 {
    a / b
}
