/* C conformance fixture: comparison and logical results used as integers.
 *
 * In C, `a < b`, `a == b`, `!a`, `a && b` are `int` 0/1. Core produces `Val.bool` for
 * them and, under `.cLike`, promotes a `bool` to 0/1 wherever it meets a number
 * (Semantics.lean, `Dialect.promotesBool`). Every `case_*` function below is run by
 * `cc` (tests/test_cboolint_cc.py) and by Core (Autoform/CBoolInt.lean), and the two
 * must agree. The first case is the SQLite-sample fixture of docs/scale.md, which
 * returned 3 in Lean and 7 under `cc` before the fix.
 */

int lt_flag(int a, int b) {
  int t = (a < b);
  if (t == 1) return 7;
  return 3;
}

int is_fatal(int rc) { return rc != 0 && rc != 5 && rc != 6; }

int both_ways(int a, int b) { return (a < b) + (b < a); }

int case_lt_flag_true(void) { return lt_flag(3, 12); }
int case_lt_flag_false(void) { return lt_flag(12, 3); }
int case_cmp_eq_one(void) { int a = 3; int b = 12; return (a < b) == 1; }
int case_cmp_plus_cmp(void) { return both_ways(3, 12) + both_ways(5, 5); }
int case_logical_times(void) { int x = is_fatal(4); return x * 10 + is_fatal(5); }
int case_not_plus(void) { int a = 0; return !a + 1; }
int case_neg_cmp(void) { int a = 1; int b = 2; return -(a < b); }
int case_bnot_cmp(void) { int a = 1; int b = 2; return ~(a > b); }
int case_bitand_cmps(void) { int a = 1; int b = 2; return ((a < b) & (b > 0)) + 2; }
int case_xor_cmps(void) { int a = 1; int b = 2; return ((a < b) ^ (b > 0)) + 4; }
int case_shift_cmp(void) { int a = 1; int b = 2; return (a < b) << 3; }
int case_cmp_vs_cmp(void) { int a = 1; int b = 2; return (a < b) > (b < a); }
int case_sum_flags(void) {
  int n = 0;
  int i = 0;
  while (i < 10) {
    n = n + (i % 3 == 0);
    i = i + 1;
  }
  return n;
}
int case_cmp_plus_double(void) {
  int a = 1;
  int b = 2;
  if ((a < b) + 0.5 > 1.0) return 1;
  return 0;
}
int case_direct_return(void) { int a = 1; int b = 2; return a < b; }
