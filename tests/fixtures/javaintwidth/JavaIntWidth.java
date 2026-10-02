// Width-typed Java integer arithmetic (item O). Every `case_*` returns `long`, so the
// value reaches the test unchanged; `main` prints `name value` per line, which
// `tests/test_javaintwidth_java.py` compares with the Core pins in
// `Autoform/JavaIntWidth.lean`.
class JavaIntWidth {
  // STRATEGY.md §29 item 5: Core used to compute this at 32 bits (1410065408).
  static long case_long_mul() { long a = 100000L; long b = 100000L; return a * b; }
  static long case_int_mul_wraps() { int a = 100000; int b = 100000; return a * b; }
  static long case_mixed_mul() { long a = 3000000000L; int b = 2; return a * b; }
  static long case_long_accumulate() {
    long s = 0;
    for (int i = 0; i < 3; i++) { s += 2000000000; }
    return s;
  }
  static long case_int_add_wraps() { int x = 2147483647; x = x + 1; return x; }
  // javasrc2cpg 4.0.606 names `>>>` arithmeticShiftRight and `>>` logicalShiftRight.
  static long case_ushr_int() { int x = -1; return x >>> 28; }
  static long case_shr_int() { int x = -16; return x >> 1; }
  static long case_ushr_long() { long x = -1L; return x >>> 60; }
  static long case_shr_long() { long x = -4294967296L; return x >> 4; }
  static long case_shr_assign() { int x = -16; x >>= 2; return x; }
  // Shift counts are masked to 5 (int) or 6 (long) bits.
  static long case_shl_masked_int() { int x = 1; return x << 33; }
  static long case_shl_long() { long x = 1L; return x << 33; }
  // Compound assignment and increment narrow back to the target type.
  static long case_byte_compound() { byte b = 127; b += 1; return b; }
  static long case_byte_increment() { byte b = 127; b++; return b; }
  static long case_char_increment() { char c = 65535; c++; return c; }
  static long case_int_compound_long() { int x = 1; long big = 4294967296L; x += big; return x; }
  // `MIN / -1` is MIN and `MIN % -1` is 0 in Java.
  static long case_min_div() { int m = -2147483648; return m / -1; }
  static long case_min_rem() { int m = -2147483648; return m % -1; }
  static long case_long_div() { long d = -7000000000L; return d / 2; }
  static long case_long_not() { long z = 0L; return ~z; }
  static long case_int_neg_min() { int y = -2147483648; return -y; }
  static long case_boxed_mul() { Integer a = 100000; Long b = 100000L; return a * b; }

  public static void main(String[] args) {
    System.out.println("case_long_mul " + case_long_mul());
    System.out.println("case_int_mul_wraps " + case_int_mul_wraps());
    System.out.println("case_mixed_mul " + case_mixed_mul());
    System.out.println("case_long_accumulate " + case_long_accumulate());
    System.out.println("case_int_add_wraps " + case_int_add_wraps());
    System.out.println("case_ushr_int " + case_ushr_int());
    System.out.println("case_shr_int " + case_shr_int());
    System.out.println("case_ushr_long " + case_ushr_long());
    System.out.println("case_shr_long " + case_shr_long());
    System.out.println("case_shr_assign " + case_shr_assign());
    System.out.println("case_shl_masked_int " + case_shl_masked_int());
    System.out.println("case_shl_long " + case_shl_long());
    System.out.println("case_byte_compound " + case_byte_compound());
    System.out.println("case_byte_increment " + case_byte_increment());
    System.out.println("case_char_increment " + case_char_increment());
    System.out.println("case_int_compound_long " + case_int_compound_long());
    System.out.println("case_min_div " + case_min_div());
    System.out.println("case_min_rem " + case_min_rem());
    System.out.println("case_long_div " + case_long_div());
    System.out.println("case_long_not " + case_long_not());
    System.out.println("case_int_neg_min " + case_int_neg_min());
    System.out.println("case_boxed_mul " + case_boxed_mul());
  }
}
