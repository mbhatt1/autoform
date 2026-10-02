/* Width-typed C integer arithmetic (item O): every case below was a hole or a silent
 * wrong answer while Core computed every C integer operation at 32 bits.
 *
 * Each `case_*` takes no arguments and returns `long long` or `unsigned long long`, so
 * the result reaches the test through a 64-bit ctypes return. Compiled with
 * `cc -O0 -fwrapv`: signed `int` overflow (case_int_mul_wraps) is undefined in ISO C,
 * and `-fwrapv` is the configured policy Core models (`Dialect.toNumConfig .cLike`). */
#include <stddef.h>

/* STRATEGY.md §29 item 5: `100000L * 100000L`. */
long long case_long_mul(void) {
  long a = 100000;
  long b = 100000;
  return a * b;
}

/* The same product at `int` stays 32-bit: 1410065408 under -fwrapv. */
long long case_int_mul_wraps(void) {
  int a = 100000;
  int b = 100000;
  int p = a * b;
  return p;
}

/* `int` operand converted to `long long` before the multiplication (6.3.1.8). */
long long case_mixed_mul(void) {
  long long a = 3000000000LL;
  int b = 2;
  return a * b;
}

/* SQLite `validJulianDay`: `((i64)0x1a640 << 32) | 0x1072fdff`. */
long long case_shift_left_64(void) {
  long long v = ((long long)0x1a640 << 32) | 0x1072fdff;
  return v;
}

/* SQLite `vdbeSorterTreeDepth(INT_MAX)`: at 32 bits `16^8` wraps to 0 and the loop
 * never ends (Core answered outOfFuel). */
long long case_tree_depth(void) {
  int nPMA = 2147483647;
  int nDepth = 0;
  long long nDiv = 16;
  while (nDiv < (long long)nPMA) {
    nDiv = nDiv * 16;
    nDepth++;
  }
  return nDepth;
}

/* Accumulating past 2^31 in a `long`. */
long long case_long_accumulate(void) {
  long s = 0;
  for (int i = 0; i < 3; i++) {
    s += 2000000000;
  }
  return s;
}

/* Unsigned wrap is defined: 0u - 1 is UINT_MAX. */
unsigned long long case_unsigned_underflow(void) {
  unsigned u = 0;
  u = u - 1;
  return u;
}

/* `unsigned u = -1` stores UINT_MAX; widening it keeps that value. */
long long case_unsigned_init_widen(void) {
  unsigned u = -1;
  long long y = u;
  return y;
}

/* u32 addition wraps mod 2^32. */
unsigned long long case_u32_add_wraps(void) {
  unsigned x = 3000000000u;
  return x + x;
}

/* u64 multiplication wraps mod 2^64. */
unsigned long long case_u64_mul_wraps(void) {
  unsigned long long x = 18446744073709551615ULL;
  return x * 2;
}

/* `>>` on unsigned is logical, on signed arithmetic, at the operand's width. */
long long case_shift_right_u32(void) {
  unsigned x = 0x80000000u;
  return x >> 31;
}

long long case_shift_right_i32(void) {
  int y = -8;
  return y >> 1;
}

long long case_shift_right_u64(void) {
  unsigned long long x = 0xF000000000000000ULL;
  return x >> 60;
}

long long case_shift_right_i64(void) {
  long long x = -4294967296LL;
  return x >> 4;
}

/* The usual arithmetic conversions make `-1 < 1u` false. */
long long case_mixed_compare(void) {
  int a = -1;
  unsigned b = 1;
  long long r = 0;
  if (a < b) r = 1;
  return r;
}

/* ... and unsigned division divides UINT_MAX - 1. */
long long case_unsigned_div(void) {
  unsigned a = -2;
  return a / 2;
}

/* Negation and complement at an unsigned width. */
unsigned long long case_unsigned_neg(void) {
  unsigned a = 1;
  return -a;
}

unsigned long long case_u64_not(void) {
  unsigned long long z = 0;
  return ~z;
}

/* A narrow store wraps: `unsigned char` increments from 255 to 0. */
long long case_u8_increment_wraps(void) {
  unsigned char c = 255;
  c++;
  return c;
}

long long case_u8_compound_wraps(void) {
  unsigned char c = 250;
  c += 10;
  return c;
}

/* `size_t` is 64-bit unsigned under LP64. */
long long case_size_t_underflow(void) {
  size_t n = 0;
  n--;
  long long r = 0;
  if (n > 4294967296ULL) r = 1;
  return r;
}

/* Signed 64-bit division truncates. */
long long case_i64_div(void) {
  long long a = -7000000000LL;
  return a / 2;
}

/* Narrowing to `signed char`: implementation-defined, wraps on every target cc runs. */
long long case_narrow_signed_char(void) {
  int x = 300;
  signed char sc = x;
  return sc;
}
