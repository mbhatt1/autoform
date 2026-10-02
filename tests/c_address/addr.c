/* Conformance fixture for the C address model (Autoform/Lang/Core/Address.lean).
 *
 * Every function takes and returns `int`, so scripts/differential.py's C path can call
 * it natively through ctypes and compare against the Lean interpreter. Each one
 * exercises a pointer operation the model answers: same-block ordering and equality
 * (including one past the end), `&p[i]` on a pointer whose provenance the exporter
 * cannot see (loaded from a struct field), and the walk of a buffer up to an end
 * pointer. Inputs outside the array make C's behaviour undefined; the Lean side must
 * then answer with a hole (INCONCLUSIVE), never a value. */

typedef unsigned char u8;

struct Buf { u8 *a; int n; };

/* p < end over a local array: same-block ordering, one-past-the-end allowed. */
int sum_until(int n) {
  int a[8];
  int i, s = 0;
  int *p, *end;
  for (i = 0; i < 8; i++) a[i] = i + 1;
  if (n < 0 || n > 8) return -1;
  p = a;
  end = &a[n];
  while (p < end) { s += *p; p++; }
  return s;
}

static int cmp_ptrs(u8 *x, u8 *y) {
  if (x == y) return 0;
  if (x < y) return -1;
  return 1;
}

/* Pointers whose provenance is a struct field: &b->a[i] is b->a + i. */
static int cmp_field_elems(struct Buf *b, int i, int j) {
  return cmp_ptrs(&b->a[i], &b->a[j]);
}

int field_order(int i, int j) {
  u8 buf[8];
  struct Buf b;
  if (i < 0 || i > 8 || j < 0 || j > 8) return 9;
  b.a = buf;
  b.n = 8;
  return cmp_field_elems(&b, i, j);
}

static int eq_field_elems(struct Buf *b, int i, int j) {
  /* `? 1 : 0`: Core answers a C comparison with a `Val.bool`, which the harness
   * (rightly) does not equate with the `int` C returns -- a pre-existing gap of
   * value-position comparisons, not of the address model. */
  return (&b->a[i] == &b->a[j]) ? 1 : 0;
}

int field_eq(int i, int j) {
  u8 buf[8];
  struct Buf b;
  if (i < 0 || i > 8 || j < 0 || j > 8) return 9;
  b.a = buf;
  b.n = 8;
  return eq_field_elems(&b, i, j);
}

/* Count elements between two pointers into one array by walking. */
static int span(u8 *from, u8 *to) {
  int k = 0;
  while (from < to) { from++; k++; }
  return k;
}

int walk_span(int i, int j) {
  u8 buf[8];
  struct Buf b;
  if (i < 0 || i > 8 || j < 0 || j > 8) return -1;
  b.a = buf;
  return span(&b.a[i], &b.a[j]);
}

/* No guard: for i outside [0, 4] forming &b.a[i] is undefined behaviour, so whatever the
 * native build returns, the Lean side must hole (INCONCLUSIVE), never answer. */
int oob_order(int i) {
  u8 buf[4];
  struct Buf b;
  b.a = buf;
  return cmp_ptrs(&b.a[0], &b.a[i]);
}

/* One past the end of one array against the start of another: C leaves the result
 * unspecified (6.5.9p6), so the Lean side must hole. Within one array it answers. */
int past_end(int k) {
  u8 x[4];
  u8 y[4];
  struct Buf bx, by;
  bx.a = x;
  by.a = y;
  if (k == 0) return (&bx.a[4] == &by.a[0]) ? 1 : 0;
  return (&bx.a[4] == &bx.a[0]) ? 1 : 0;
}

struct CBuf { char *c; };

/* Pointer difference: same array, same stride (6.5.6p9). */
static int char_gap(struct CBuf *b, int i, int j) {
  char *from = &b->c[i];
  char *to = &b->c[j];
  return (int)(to - from);
}

int gap(int i, int j) {
  char buf[8];
  struct CBuf b;
  if (i < 0 || i > 8 || j < 0 || j > 8) return -99;
  b.c = buf;
  return char_gap(&b, i, j);
}

/* Pointer minus integer, stepping back within the array. */
static char *back(char *p, int n) { return p - n; }

int back_eq(int i, int n) {
  char buf[8];
  struct CBuf b;
  if (i < 0 || i > 8 || n < 0 || n > i) return -1;
  b.c = buf;
  return (back(&b.c[i], n) == &b.c[i - n]) ? 1 : 0;
}
