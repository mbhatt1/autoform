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

// ---- widened oracle encodings: bool, tuples, arrays, shared references ----
pub fn is_even(x: u32) -> bool {
    x % 2 == 0
}

pub fn divmod(a: u32, b: u32) -> (u32, u32) {
    (a / b, a % b)
}

pub fn swap_pair(p: (i8, bool)) -> (bool, i8) {
    (p.1, p.0)
}

pub fn sum3(a: [u8; 3]) -> u16 {
    a[0] as u16 + a[1] as u16 + a[2] as u16
}

pub fn max_ref(a: &i64, b: &i64) -> i64 {
    if *a > *b { *a } else { *b }
}

pub fn sum_to(n: u16) -> u64 {
    let mut s: u64 = 0;
    let mut i: u16 = 0;
    while i < n {
        s += i as u64;
        i += 1;
    }
    s
}

// Recursion: Aeneas emits a partial_fixpoint, which the kernel does not evaluate.
pub fn fact(n: u8) -> u64 {
    if n == 0 { 1 } else { n as u64 * fact(n - 1) }
}

// ---- trait impl on a primitive, and a provided (default) method ----
pub trait Shape {
    fn area(&self) -> u32;
    fn double_area(&self) -> u32 {
        self.area() * 2
    }
}

impl Shape for u16 {
    fn area(&self) -> u32 {
        (*self as u32) * (*self as u32)
    }
}

// ---- things the oracle cannot encode exactly: inconclusive, with a reason ----
pub struct Counter {
    pub n: u32,
}

impl Counter {
    pub fn new(n: u32) -> Counter {
        Counter { n }
    }
    pub fn get(&self) -> u32 {
        self.n
    }
}

pub fn bump(x: &mut u32) {
    *x += 1;
}

pub fn larger<T: PartialOrd + Copy>(a: T, b: T) -> T {
    if a > b { a } else { b }
}

// ---- things Charon/Aeneas do not translate: named holes ----
pub fn halve(x: f64) -> f64 {
    x / 2.0
}

pub fn first_byte(s: &str) -> u8 {
    s.as_bytes()[0]
}

/// # Safety
/// `p` must be valid for a one-byte read.
pub unsafe fn read_raw(p: *const u8) -> u8 {
    unsafe { *p }
}

pub fn count_ones_u32(x: u32) -> u32 {
    x.count_ones()
}
