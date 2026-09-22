"""Check source semantics through the existing Joern exporter and real runtimes.

AUTOFORM_TEST_JOERN=1 enables the expensive parse/export/native differential tests.
The kernel reduction checks run whenever Lean is available.
"""
from __future__ import annotations

import json
import math
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]


def run(args, cwd, env, timeout=240):
    p = subprocess.run(list(map(str, args)), cwd=cwd, env=env, text=True,
                       capture_output=True, timeout=timeout)
    assert p.returncode == 0, p.stdout + p.stderr
    return p.stdout


@pytest.fixture(scope="module")
def numeric_env():
    env = {k: os.environ[k] for k in ("PATH", "HOME", "LANG", "LC_ALL", "TMPDIR", "JAVA_HOME")
           if k in os.environ}
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    if not shutil.which("lake", path=env["PATH"]):
        if os.environ.get("AUTOFORM_REQUIRE_LEAN"):
            pytest.fail("Lean is required")
        pytest.skip("Lean is not installed")
    run(["lake", "build", "Autoform.Lang.Core.Semantics"], ROOT, env, timeout=600)
    return env


def test_python_sequence_index_kernel(tmp_path, numeric_env):
    # Derive each answer from CPython, including both signed bounds and indexes
    # far beyond a machine word. These run even when Joern is unavailable.
    code = 'import Autoform.Lang.Core.Semantics\nopen Autoform.Core\n'
    for kind, make in (("list", list), ("tuple", tuple)):
        for size in range(4):
            values = make(10 * (i + 1) for i in range(size))
            encoded = ', '.join(f'.lit (.int {v})' for v in values)
            for index in sorted({-2**80, -size - 1, -size, -1, 0, size - 1, size, 2**80}):
                try:
                    expected = f'.val (.int {values[index]})'
                except IndexError:
                    expected = '.exn (.str "IndexError")'
                code += (
                    f'example : (evalExpr {{ table := [], dialect := .python }} 16 [] [] '
                    f'(.index (.{kind}E [{encoded}]) (.lit (.int ({index}))))).2 '
                    f'= {expected} := by rfl\n')
    path = tmp_path / 'SequenceIndex.lean'
    path.write_text(code)
    run(['lake', 'env', 'lean', path], ROOT, numeric_env)


def test_tuple_from_boxed_container_kernel(tmp_path, numeric_env):
    code = r'''import Autoform.Lang.Core.Semantics
open Autoform.Core
example : (evalExpr { dialect := .python, table := [] } 20 [] []
    (.call "tuple" [.listE [.lit (.int 1), .lit (.int 2)]])).2
    = .val (.tuple [.int 1, .int 2]) := by rfl
example : (evalExpr { dialect := .python, table := [] } 20 [] []
    (.call "tuple" [.dictE [(.lit (.str "a"), .lit (.int 1))]])).2
    = .val (.tuple [.str "a"]) := by rfl
-- Copy the outer sequence, keeping the inner object's identity.
example : (evalExpr { dialect := .python, table := [] } 20 [] []
    (.call "tuple" [.listE [.listE [.lit (.int 1)]]])).2
    = .val (.tuple [.ref 0]) := by rfl
'''
    path = tmp_path / "TupleFromBoxed.lean"
    path.write_text(code)
    run(['lake', 'env', 'lean', path], ROOT, numeric_env)


def test_typed_numeric_kernel(tmp_path, numeric_env):
    # Boundary values and refusal cases. These are kernel proofs, not native_decide.
    code = '''import Autoform.Lang.Core.Semantics
open Autoform.Core
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
set_option cbv.warning false
example : applyBinop .cLike "num:java:i64:+" (.int 2147483647) (.int 1) = .val (.int 2147483648) := by rfl
example : applyBinop .cLike "num:java:i64:+" (.int 9223372036854775807) (.int 1) = .val (.int (-9223372036854775808)) := by rfl
example : applyBinop .cLike "num:java:i32:<<" (.int 1) (.int 32) = .val (.int 1) := by rfl
example : applyBinop .cLike "num:java:i64:<<" (.int 1) (.int 64) = .val (.int 1) := by rfl
example : applyBinop .cLike "num:java:i64:>>>" (.int (-1)) (.int 1) = .val (.int 9223372036854775807) := by rfl
example : applyBinop .cLike "num:java:i64:/" (.int 1) (.int 0) = .exn (.str "ArithmeticException") := by rfl
example : applyBinop .cLike "num:go:i64:+" (.int 9223372036854775807) (.int 1) = .val (.int (-9223372036854775808)) := by rfl
example : applyBinop .cLike "num:go:i64:/" (.int (-9223372036854775808)) (.int (-1)) = .val (.int (-9223372036854775808)) := by rfl
example : applyBinop .cLike "num:go:i64:%" (.int (-9223372036854775808)) (.int (-1)) = .val (.int 0) := by rfl
example : applyBinop .cLike "num:go:u64:<<" (.int 1) (.int 64) = .val (.int 0) := by rfl
example : applyBinop .cLike "num:go:i64:>>" (.int (-1)) (.int 1000000) = .val (.int (-1)) := by rfl
example : applyBinop .cLike "num:go:u64:>>" (.int 18446744073709551615) (.int 1) = .val (.int 9223372036854775807) := by rfl
example : applyBinop .cLike "num:go:i8:<<" (.int 1) (.int (-1)) = .exn (.str "panic:negative shift amount") := by rfl
example : applyBinop .cLike "num:go:i64:/" (.int 1) (.int 0) = .exn (.str "panic:integer divide by zero") := by rfl
example : applyBinop .cLike "num:c:u32:+" (.int 4294967295) (.int 1) = .val (.int 0) := by rfl
example : applyBinop .cLike "num:c:i64:+" (.int 2147483647) (.int 1) = .val (.int 2147483648) := by rfl
example : applyBinop .cLike "num:c:u32:<" (.int (-1)) (.int 1) = .val (.bool false) := by rfl
example : applyBinop .cLike "num:c:i32:+" (.int 2147483647) (.int 1) = .hole "ub:signed integer overflow" := by rfl
example : applyBinop .cLike "num:c:i32:<<" (.int (-1)) (.int 1) = .hole "ub:left shift of a negative value" := by rfl
example : applyBinop .cLike "num:c:i32:<<" (.int 1) (.int 32) = .hole "ub:shift count out of range" := by rfl
example : applyBinop .cLike "num:c:i32:/" (.int 1) (.int 0) = .hole "ub:division by zero" := by rfl
example : applyBinop .javascript "num:js:i32:>>>" (.int (-1)) (.int 0) = .val (.int 4294967295) := by rfl
example : applyBinop .javascript "num:js:i32:>>" (.int (-1)) (.int 0) = .val (.int (-1)) := by rfl
example : applyBinop .javascript "num:js:i32:<<" (.int 1) (.int 32) = .val (.int 1) := by rfl
example : applyBinop .javascript "num:js:i32:|" (.int 9007199254740993) (.int 0) = .val (.int 0) := by rfl
example : applyBinop .javascript "num:js:i32:|" (.float (.nan .binary64)) (.int 0) = .val (.int 0) := by rfl
example : applyBinop .javascript "num:js:i32:&" (.int 0) (.int 123) = .val (.int 0) := by rfl
example : applyBinop .javascript "num:js:i32:^" (.int 123) (.int 0) = .val (.int 123) := by rfl
example : applyBinop .javascript "num:js:i32:|" (.int 1) (.int (-1)) = .val (.int (-1)) := by cbv
example : applyBinop .javascript "num:js:i32:|" (.int (-1)) (.int 2147483647) = .val (.int (-1)) := by cbv
example : applyBinop .cLike "num:go:u64:&" (.int 18446744073709551615) (.int 9223372036854775808) = .val (.int 9223372036854775808) := by cbv
example : applyBinop .cLike "num:java:i64:^" (.int (-1)) (.int 9223372036854775807) = .val (.int (-9223372036854775808)) := by cbv
example : NumConfig.python.bor (-8) 3 = .ok (-5) := by rfl
example : NumConfig.python.band (-1) 18446744073709551616 = .ok 18446744073709551616 := by rfl
example : applyUnop .javascript "num:js:i32:~" (.int 4294967296) = .val (.int (-1)) := by rfl
example : applyUnop .cLike "num:java:i64:-" (.int (-9223372036854775808)) = .val (.int (-9223372036854775808)) := by cbv
example : applyBinop .cLike "num:rust:i32:+" (.int 1) (.int 2) = .hole "binop:num:rust:i32:+" := by rfl
example : applyBinop .cLike "num:c:i128:+" (.int 1) (.int 2) = .hole "binop:num:c:i128:+" := by rfl
example : applyBinop .javascript "num:js:i32:|" (.str "1") (.int 0) = .hole "numeric:operand:num:js:i32:|" := by rfl
example : applyBinop .python "py:/" (.int 3) (.int 2) = .val (.float (Fl.ofBits 4609434218613702656)) := by rfl
example : applyBinop .python "py:/" (.int 0) (.int (-1)) = .val (.float (Fl.ofBits 9223372036854775808)) := by rfl
example : applyBinop .python "py:/" (.int 1) (.int 0) = .exn (.str "ZeroDivisionError") := by rfl
example : applyBinop .python "//" (.int (-3)) (.int 2) = .val (.int (-2)) := by rfl
example : applyBinop .javascript "js:/" (.int 3) (.int 2) = .val (.float (Fl.ofBits 4609434218613702656)) := by rfl
example : applyBinop .javascript "js:%" (.int (-5)) (.int 2) = .val (.float (Fl.ofBits 13830554455654793216)) := by rfl
example : applyBinop .cLike "num:c:i32:+" (.bool true) (.int 2) = .val (.int 3) := by rfl
'''
    path = tmp_path / "NumericChecks.lean"
    path.write_text(code)
    run(["lake", "env", "lean", path], ROOT, numeric_env)


SOURCES = {
    "python": ("PYTHONSRC", "numbers.py", '''def augSelf(a, b):
    a += (a := b)
    return a
def augNested(a, b):
    a += (a := a + b)
    return a
def indexSnapshot(a, b):
    xs = [a, b]
    return xs[(xs := [b, a]) and 0]
class Box:
    def __init__(self, value):
        self.value = value
def augField(a, b):
    left = Box(a)
    right = Box(b)
    saved = left
    left.value += (left := right).value
    return saved.value * 10 + right.value
def indexNegative(a, b):
    return [a, b][-1]
def indexTupleNegative(a, b):
    return (a, b)[-1]
def indexNegativeBoundary(a, b):
    return [a, b][-2]
def indexNegativeError(a, b):
    try:
        return [a, b][-3]
    except IndexError:
        return a + b
def indexHugeNegative(a, b):
    try:
        return (a, b)[-1208925819614629174706176]
    except IndexError:
        return a + b
def compList(a, b):
    xs = [a, b, a + b]
    ys = [x * 2 for x in xs if x > 1]
    return sum(ys) * 10 + len(ys)
def compNoLeak(a, b):
    x = a
    ys = [x + 1 for x in [b, b]]
    return x * 100 + ys[0]
def compDict(a, b):
    d = {k: v for k, v in [(a, b), (b, a)]}
    return d[a] * 10 + d[b]
def genTuple(a, b):
    t = tuple(x + 1 for x in [a, b])
    return t[0] * 100 + t[1]
def genSum(a, b):
    return sum(x * x for x in [a, b, 3])
class Held:
    def __init__(self, v):
        self.v = v
    def __enter__(self):
        return self.v + 1
    def __exit__(self, *exc):
        self.v = 0
        return False
def withStmt(a, b):
    h = Held(a)
    with h as v:
        b = b + v
    return b * 10 + h.v
class EffectBox:
    def __init__(self, v):
        self.v = v
    def bump(self, d):
        self.v = self.v + d
        return self
    def get(self):
        return self.v
    def combine(self, x, y):
        return self.v * 100 + x * 10 + y
def pair(x, y):
    return x * 10 + y
def argOrder(a, b):
    box = EffectBox(a)
    return pair(box.get(), box.bump(b).get())
def kwHoist(a, b):
    box = EffectBox(a)
    return pair(y=box.bump(b).get(), x=box.get())
def ctorHoist(a, b):
    box = EffectBox(a)
    other = EffectBox(box.bump(b).get())
    return other.v * 10 + box.v
def tupleHoist(a, b):
    box = EffectBox(a)
    t = (box.get(), box.bump(b).get(), box.get())
    return t[0] * 100 + t[1] * 10 + t[2]
def inHoist(a, b):
    box = EffectBox(a)
    return 1 if box.get() in [box.bump(b).get()] else 0
def methodHoist(a, b):
    box = EffectBox(a)
    return box.combine(box.get(), box.bump(b).get())
def receiverHoist(a, b):
    box = EffectBox(a)
    other = EffectBox(b)
    return box.combine(box.get(), (box := other).get())
def listHoist(a, b):
    box = EffectBox(a)
    xs = [box.get(), box.bump(b).get(), box.get()]
    return xs[0] * 100 + xs[1] * 10 + xs[2]
def shortHoist(a, b):
    box = EffectBox(a)
    x = a and box.bump(b).get()
    return x * 10 + box.v
def branchHoist(a, b):
    box = EffectBox(a)
    x = box.bump(b).get() if a else box.get()
    return x * 10 + box.v
def assertHoist(a, b):
    box = EffectBox(a)
    try:
        assert box.bump(b).get(), box.bump(100).get()
    except AssertionError:
        return box.v
    return box.v
def forHoist(a, b):
    box = EffectBox(a)
    out = 0
    for x in [box.get(), box.bump(b).get()]:
        out = out * 10 + x
    return out
def sliceHoist(a, b):
    xs = [a, b, a + b]
    other = [b, a, a - b]
    out = xs[0:len(xs := other)]
    return out[0] * 10 + out[1]
def delHoist(a, b):
    xs = [a, b]
    other = [b, a]
    del xs[len(xs := other) - 2]
    return other[0] * 100 + other[1]
def keywordSnapshot(a, b):
    box = EffectBox(a)
    return pair(x=box.get(), y=box.bump(b).get())
def makePair(box):
    box.v = box.v + 1
    return pair
def pairBack(x, y):
    return y * 10 + x
def failFactory():
    raise ValueError
def valueCallOrder(a, b):
    box = EffectBox(a)
    return makePair(box)(box.get(), box.bump(b).get())
def valueCallKeyword(a, b):
    box = EffectBox(a)
    return makePair(box)(x=box.get(), y=box.bump(b).get())
def valueCallCalleeEffect(a, b):
    box = EffectBox(a)
    return makePair(box.bump(b))(box.get(), box.bump(1).get())
def valueCallSnapshot(a, b):
    fs = [pair, pairBack]
    return fs[0](a, (fs := [pairBack, pair]) and b)
def valueCallCalleeFailure(a, b):
    box = EffectBox(a)
    try:
        failFactory()(box.bump(b).get())
    except ValueError:
        return box.v
    return -999
def valueCallArgumentFailure(a, b):
    box = EffectBox(a)
    try:
        makePair(box)(a // 0, box.bump(b).get())
    except ZeroDivisionError:
        return box.v
    return -999
'''),
    "java": ("JAVASRC", "Numbers.java", '''public class Numbers {
  public static long add(long a, long b) { return a + b; }
  public static long div(long a, long b) { return a / b; }
  public static int shift(int a, int b) { return a << b; }
  public static long unsigned(long a, int b) { return a >>> b; }
  public static long inc(long a) { a += 1; return a; }
  public static byte bump(byte a) { a++; return a; }
  public static byte compound(byte a, int b) { a += b; return a; }
  public static long pair(long a, long b) { return 10 * a + b; }
  public static long callPlain(long a, long b) { return pair(a, b); }
  public static long callSnapshot(long a, long b) { return pair(a, a = b); }
  public static long callPost(long a) { return pair(a, a++); }
  public static long callPrefix(long a) { return pair(++a, ++a); }
  public static long callNested(long a) { return pair(pair(a, a++), a); }
  public static long augSelf(long a, long b) { a += (a = b); return a; }
  public static long augValue(long a, long b) { return a += (a = b); }
  public static long augPost(long a) { a += a++; return a; }
  public static long augNested(long a, long b) { return a += (a += b); }
  public static long augShift(long a, long b) { a >>= (a = b); return a; }
  public static long augUnsigned(long a, long b) { a >>>= (a = b); return a; }
  public static long shiftWrapped(long a, long b) { return (a) >> (b + 1); }
  public static long shiftNested(long a, long b) { return (a >> 1) >>> (b >> 1); }
  public static long augNarrow(long a, long b) {
    byte c = (byte)a; c += (c = (byte)b); return c;
  }
  public static long castChar(long a) { return (char)a; }
}'''),
    "go": ("GOLANG", "numbers.go", '''package numbers
func Add(a int64, b int64) int64 { return a + b }
func Div(a int64, b int64) int64 { return a / b }
func Shift(a uint64, b uint) uint64 { return a << b }
func Right(a int64, b uint) int64 { return a >> b }
func Inc(a int64) int64 { a += 1; return a }
func Bump(a int8) int8 { a++; return a }
func Word(a int, b int) int { return a + b }
func ContextShift(n uint) uint32 { return 1 << n }
func Constant() uint64 { return 9223372036854775807 + 1 }
'''),
    "c": ("C", "numbers.c", '''long add(long a, long b) { return a + b; }
unsigned int wrap(unsigned int a, unsigned int b) { return a + b; }
int mixed(int a, unsigned int b) { return a < b; }
unsigned int right(unsigned int a, unsigned int b) { return a >> b; }
unsigned char bump(unsigned char a) { a++; return a; }
long nested(long a, long b) { return (a + b) * b; }
long literal(void) { return 2147483648 + 1; }
long mixedwidth(long a, unsigned int b) { return a + b; }
int promote(unsigned char a, int b) { return a + b; }
unsigned int hexliteral(void) { return 0xffffffff | 0; }
unsigned long long wideshift(void) { return 1ULL << 40; }
int octalcompare(void) { return 037777777777 < 0; }
int remainder_assign(int a, int b) { a %= b; return a; }
int remainder_value(int a, int b) { return a %= b; }
unsigned int compound_bits(unsigned int a, unsigned int b) {
  a &= b; a |= 0x20; a ^= 3; a <<= 2; return a;
}
unsigned char narrow_compound(unsigned char a, int b) { a ^= b; return a; }
int mask_value(int a, int b) { return a |= b; }
int loop_condition(int a) { int n = 0; while ((a &= a - 1) != 0) n++; return n; }
unsigned long long conditional_widen(int a, unsigned int b, int choose) { return choose ? a : b; }
int conditional_nested(unsigned char a) { return a ^ (a & 0x80 ? 0x1d : 0); }
unsigned long long conditional_effect(int a, unsigned int b, int choose) {
  return choose ? (a %= 255) : (b |= 0x80000000U);
}
int conditional_once(int choose) {
  int a = 1, b = 2;
  int x = choose ? a++ : b++;
  return 100 * x + 10 * a + b;
}
unsigned int assignment_narrow(int a) { unsigned char b = a; return b; }
int assignment_value(int a) { unsigned char b; return b = a; }
unsigned int field_narrow(int a) {
  struct Octet { unsigned char value; } b;
  b.value = a; return b.value;
}
unsigned int field_wider(int a) {
  struct Octet { unsigned short value; } b;
  b.value = a; return b.value;
}
unsigned int array_narrow(int a) { unsigned char b[1]; b[0] = a; return b[0]; }
int loop_while(int n) {
  int i = 0, total = 0;
  while (i++ < n) { if (i & 1) continue; total += i; }
  return 100 * i + total;
}
int loop_do(int n) {
  int i = 0, total = 0;
  do { if ((i & 1) == 0) continue; total += i; } while (i++ < n);
  return 100 * i + total;
}
int loop_for(int n) {
  int i = 0, total = 0;
  for (i = 0; (i += 1) <= n; i += 1) { if (i == 1) continue; total += i; }
  return 100 * i + total;
}
int loop_nested(int n) {
  int i = 0, total = 0;
  do {
    int j = 0;
    while (j++ < 2) { if (j == 1) continue; total++; }
    if (i == 1) continue;
    total += 10;
  } while (i++ < n);
  return 100 * i + total;
}
int loop_break(int n) { int i = 0; while (i++ < n) { if (i == 2) break; } return i; }
int loop_do_break(int n) { int i = 0; do { if (n) break; } while (i++ < 0); return i; }
int logical_and(int choose) { int x = 0; int y = choose && ++x; return 10 * x + y; }
int logical_or(int choose) { int x = 0; int y = choose || ++x; return 10 * x + y; }
int logical_once(int a) { int x = a; int y = (x++ > 0) && (++x > 0); return 10 * x + y; }
int logical_nested(int a) { int x = 0; int y = a && (++x || ++x); return 10 * x + y; }
'''),
    "js": ("JAVASCRIPT", "numbers.js", '''function shift(a, b) { return a << b; }
function unsigned(a, b) { return a >>> b; }
function signed(a, b) { return a >> b; }
function bits(a, b) { return a | b; }
function complement(a) { return ~a; }
function signedAssign(a, b) { a >>= b; return a; }
function unsignedAssign(a, b) { a >>>= b; return a; }
function unsignedValue(a, b) { return a >>>= b; }
function andValue(a, b) { let x = 0; const y = a && (x = b); return 10 * x + y; }
function orValue(a, b) { let x = 0; const y = a || (x = b); return 10 * x + y; }
function snapshot(a, b) { return a + (a = b); }
function shiftOnce(a) { return a >> a++; }
function pair(a, b) { return 10 * a + b; }
function callPlain(a, b) { return pair(a, b); }
function callSnapshot(a, b) { return pair(a, a = b); }
function callPost(a) { return pair(a, a++); }
function callPrefix(a) { return pair(++a, ++a); }
function callNested(a) { return pair(pair(a, a++), a); }
function augSelf(a, b) { a += (a = b); return a; }
function augValue(a, b) { return a += (a = b); }
function augPost(a) { a += a++; return a; }
function augNested(a, b) { return a += (a += b); }
function augShift(a, b) { a >>= (a = b); return a; }
function augUnsigned(a, b) { a >>>= (a = b); return a; }
function shiftWrapped(a, b) { return (a) >> (b + 1); }
function shiftNested(a, b) { return (a >> 1) >>> (b >> 1); }
function indexSnapshot(a, b) {
  let xs = [a, b]; return xs[(xs = [b, a]) && 0];
}
function indexString(a, b) {
  let xs = "xy";
  return xs[(xs = "yx") && 0] === "x" ? a : b;
}
'''),
}

CASES = {
    "python": [("augSelf", [9, 3]), ("augSelf", [-9, 3]),
               ("augNested", [9, 3]), ("augNested", [-9, 3]),
               ("indexSnapshot", [1, 2]), ("indexSnapshot", [-3, 7]),
               ("augField", [9, 3]), ("augField", [-9, 3]),
               ("indexNegative", [1, 2]), ("indexNegative", [-3, 7]),
               ("indexTupleNegative", [1, 2]), ("indexTupleNegative", [-3, 7]),
               ("indexNegativeBoundary", [1, 2]), ("indexNegativeBoundary", [-3, 7]),
               ("indexNegativeError", [1, 2]), ("indexNegativeError", [-3, 7]),
               ("indexHugeNegative", [1, 2]), ("indexHugeNegative", [-3, 7]),
               # Comprehensions lower to a boxed list and a `forIn`; the loop variable is
               # rebound to a synthetic name (`compNoLeak` reads the OUTER `x` afterwards).
               # A generator expression consumed at once (`tuple`, `sum`) lowers eagerly.
               ("compList", [9, 3]), ("compList", [-9, 3]),
               ("compNoLeak", [9, 3]), ("compNoLeak", [-9, 3]),
               ("compDict", [9, 3]), ("compDict", [-9, 3]),
               ("genTuple", [9, 3]), ("genTuple", [-9, 3]),
               ("genSum", [9, 3]), ("genSum", [-9, 3]),
               # `with` is the frontend's own `__enter__`/`try`-`finally`-`__exit__` lowering.
               ("withStmt", [9, 3]), ("withStmt", [-9, 3]),
               # Preludes everywhere (§17.R4): an operand whose frontend lowering is an
               # impure block (a method call on a call result) hoists, and the operands
               # evaluated BEFORE it are completed first -- `box.get()` must read the
               # pre-bump value (Language Reference §6.16) in every position: positional
               # argument, keyword argument, constructor argument, tuple display, `in`.
               ("argOrder", [9, 3]), ("argOrder", [-9, 3]),
               ("kwHoist", [9, 3]), ("kwHoist", [-9, 3]),
               ("ctorHoist", [9, 3]), ("ctorHoist", [-9, 3]),
               ("tupleHoist", [9, 3]), ("tupleHoist", [-9, 3]),
               ("inHoist", [9, 3]), ("inHoist", [9, 0]),
               ("methodHoist", [9, 3]), ("methodHoist", [-9, 3]),
               ("receiverHoist", [9, 3]), ("receiverHoist", [-9, 3]),
               ("listHoist", [9, 3]), ("listHoist", [-9, 3]),
               ("shortHoist", [0, 3]), ("shortHoist", [9, 3]),
               ("branchHoist", [0, 3]), ("branchHoist", [9, 3]),
               ("assertHoist", [9, 3]), ("assertHoist", [-3, 3]),
               ("forHoist", [9, 3]), ("forHoist", [-9, 3]),
               ("sliceHoist", [9, 3]), ("sliceHoist", [-9, 3]),
               ("delHoist", [9, 3]), ("delHoist", [-9, 3]),
               ("keywordSnapshot", [9, 3]), ("keywordSnapshot", [-9, 3]),
               ("valueCallOrder", [9, 3]), ("valueCallOrder", [-9, 3]),
               ("valueCallKeyword", [9, 3]), ("valueCallKeyword", [-9, 3]),
               ("valueCallCalleeEffect", [9, 3]), ("valueCallCalleeEffect", [-9, 3]),
               ("valueCallSnapshot", [9, 3]), ("valueCallSnapshot", [-9, 3]),
               ("valueCallCalleeFailure", [9, 3]), ("valueCallCalleeFailure", [-9, 3]),
               ("valueCallArgumentFailure", [9, 3]), ("valueCallArgumentFailure", [-9, 3])],
    "java": [("add", [2147483647, 1]), ("add", [9223372036854775807, 1]),
             ("div", [-9223372036854775808, -1]), ("shift", [1, 32]),
             ("shift", [1, -1]), ("unsigned", [-1, 1]),
             ("inc", [9223372036854775807]), ("bump", [127]), ("compound", [120, 10]),
             ("callPlain", [2, 3]), ("callSnapshot", [1, 7]), ("callSnapshot", [-2, 3]),
             ("callPost", [1]), ("callPost", [-1]), ("callPrefix", [1]),
             ("callNested", [1]), ("callNested", [-1]),
             ("augSelf", [9, 3]), ("augSelf", [9223372036854775807, 1]),
             ("augValue", [9, 3]), ("augValue", [-9, 3]),
             ("augPost", [0]), ("augPost", [-3]),
             ("augNested", [9, 3]), ("augNested", [-9, 3]),
             ("augShift", [-8, 1]), ("augShift", [-8, 65]),
             ("augUnsigned", [-8, 1]), ("augUnsigned", [-8, 65]),
             ("shiftWrapped", [-8, 0]), ("shiftNested", [-8, 4]),
             ("augNarrow", [127, 1]), ("augNarrow", [-128, -1]),
             ("castChar", [-1]), ("castChar", [65536])],
    "go": [("Add", [2147483647, 1]), ("Add", [9223372036854775807, 1]),
           ("Div", [-9223372036854775808, -1]), ("Shift", [1, 64]),
           ("Shift", [1, 63]), ("Right", [-1, 80]),
           ("Inc", [9223372036854775807]), ("Bump", [127]),
           ("ContextShift", [31]), ("ContextShift", [32]), ("Constant", [])],
    "c": [("add", [2147483647, 1]), ("wrap", [4294967295, 1]),
          ("wrap", [2147483647, 1]), ("mixed", [-1, 1]),
          ("right", [4294967295, 31]), ("bump", [255]), ("nested", [2147483647, 2]),
          ("literal", []), ("mixedwidth", [-1, 1]), ("promote", [255, 1]),
          ("hexliteral", []), ("wideshift", []), ("octalcompare", []),
          ("remainder_assign", [-7, 3]), ("remainder_assign", [7, -3]),
          ("remainder_value", [-256, 255]), ("remainder_value", [256, 255]),
          ("compound_bits", [4294967295, 2147483648]), ("compound_bits", [123, 85]),
          ("narrow_compound", [255, 1024]), ("narrow_compound", [255, 511]),
          ("mask_value", [-8, 3]), ("loop_condition", [0]), ("loop_condition", [127]),
          ("conditional_widen", [-1, 1, 1]), ("conditional_widen", [-1, 1, 0]),
          ("conditional_nested", [128]), ("conditional_nested", [127]),
          ("conditional_effect", [-256, 1, 1]), ("conditional_effect", [-256, 1, 0]),
          ("conditional_once", [1]), ("conditional_once", [0]),
          ("assignment_narrow", [-1]), ("assignment_narrow", [256]),
          ("assignment_value", [511]), ("assignment_value", [-2]),
          ("field_narrow", [256]), ("field_narrow", [-1]),
          ("field_wider", [256]), ("field_wider", [-1]),
          ("array_narrow", [511]), ("array_narrow", [-2]),
          ("loop_while", [0]), ("loop_while", [3]), ("loop_do", [0]), ("loop_do", [3]),
          ("loop_for", [0]), ("loop_for", [5]), ("loop_nested", [0]), ("loop_nested", [2]),
          ("loop_break", [0]), ("loop_break", [5]), ("loop_do_break", [0]), ("loop_do_break", [1]),
          ("logical_and", [0]), ("logical_and", [5]), ("logical_or", [0]), ("logical_or", [5]),
          ("logical_once", [0]), ("logical_once", [1]),
          ("logical_nested", [0]), ("logical_nested", [1])],
    "js": [("shift", [1, 32]), ("shift", [2147483647, 1]),
           ("unsigned", [-1, 0]), ("unsigned", [-1, 1]), ("signed", [-1, 1]),
           ("bits", [4294967296, 1]), ("bits", [9007199254740993, 0]),
           ("complement", [4294967296]), ("bits", [3.75, 0]),
           ("shift", [-3.75, 1]), ("bits", [float("nan"), 0]),
           ("bits", [float("inf"), 0]), ("signedAssign", [-1, 1]),
           ("unsignedAssign", [-1, 1]), ("unsignedValue", [-1, 1]),
           ("andValue", [0, 3]), ("andValue", [2, 3]),
           ("orValue", [0, 7]), ("orValue", [5, 7]), ("snapshot", [8, 3]),
           ("shiftOnce", [0]), ("shiftOnce", [1]), ("shiftOnce", [-1]),
           ("callPlain", [2, 3]), ("callSnapshot", [1, 7]), ("callSnapshot", [-2, 3]),
           ("callPost", [1]), ("callPost", [-1]), ("callPrefix", [1]),
           ("callNested", [1]), ("callNested", [-1]),
           ("augSelf", [9, 3]), ("augSelf", [-9, 3]),
           ("augValue", [9, 3]), ("augValue", [-9, 3]),
           ("augPost", [0]), ("augPost", [-3]),
           ("augNested", [9, 3]), ("augNested", [-9, 3]),
           ("augShift", [-8, 1]), ("augShift", [-8, 33]),
           ("augUnsigned", [-8, 1]), ("augUnsigned", [-8, 33]),
           ("shiftWrapped", [-8, 0]), ("shiftNested", [-8, 4])],
}


def native_results(language, work, env):
    _, filename, source = SOURCES[language]
    cases = CASES[language]
    if language == "python":
        runner = work / "runner.py"
        runner.write_text(source + "\n" + "\n".join(
            f"print({name}({','.join(map(str, args))}))" for name, args in cases))
        out = run([sys.executable, runner], work, env)
    elif language == "java":
        expressions = []
        for name, args in cases:
            terms = []
            for i, n in enumerate(args):
                ty = "byte" if name in ("bump", "compound") and i == 0 else (
                    "int" if name in ("shift", "compound") or name == "unsigned" and i == 1 else "long")
                terms.append(f"({ty})({n}L)")
            expressions.append(f"Numbers.{name}({','.join(terms)})")
        runner = work / "Runner.java"
        runner.write_text("public class Runner { public static void main(String[] args) {\n" +
                          "\n".join(f"System.out.println({e});" for e in expressions) + "\n} }")
        run(["javac", "-d", work, work / "src" / filename, runner], work, env)
        out = run(["java", "-cp", work, "Runner"], work, env)
    elif language == "go":
        (work / filename).write_text(source.replace("package numbers", "package main"))
        runner = work / "runner.go"
        runner.write_text('package main\nimport "fmt"\nfunc main() {\n' + "\n".join(
            f"fmt.Println({name}({','.join(map(str, args))}))" for name, args in cases) + "\n}")
        out = run(["go", "run", work / filename, runner], work, {**env, "GOCACHE": str(work / "gocache")})
    elif language == "c":
        runner = work / "runner.c"
        runner.write_text('#include <stdio.h>\n' + source + '\nint main(void) {\n' + "\n".join(
            f'printf("%lld\\n", (long long){name}({",".join(str(n)+"LL" for n in args)}));'
            for name, args in cases) + "\n}")
        run(["cc", "-std=c11", "-O2", runner, "-o", work / "native"], work, env)
        out = run([work / "native"], work, env)
    else:
        runner = work / "runner.js"
        def number(n):
            return "NaN" if math.isnan(n) else "Infinity" if math.isinf(n) else str(n)
        runner.write_text(source + "\n" + "\n".join(
            f"console.log({name}({','.join(map(number, args))}));" for name, args in cases))
        out = run(["node", runner], work, env)
    return [int(s) for s in out.splitlines()]


@pytest.mark.parametrize("language", list(SOURCES))
def test_joern_native_numeric(language, tmp_path, numeric_env):
    if not os.environ.get("AUTOFORM_TEST_JOERN"):
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to parse/export and compare native runtimes")
    joern_home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    if (joern_home / "joern-cli").is_dir():
        joern_home /= "joern-cli"
    required = {"python": [], "java": ["java", "javac"], "go": ["go"], "c": ["cc"], "js": ["node"]}[language]
    for exe in required:
        assert shutil.which(exe, path=numeric_env["PATH"]), f"missing runtime: {exe}"
    assert (joern_home / "joern").is_file(), "set JOERN_HOME to the joern-cli directory"
    src = tmp_path / "src"
    src.mkdir()
    frontend, filename, source = SOURCES[language]
    (src / filename).write_text(source)
    expected = native_results(language, tmp_path, numeric_env)
    assert len(expected) == len(CASES[language])
    run([joern_home / "joern-parse", src, "--language", frontend, "--output", "cpg.bin"],
        tmp_path, numeric_env, timeout=600)
    run([joern_home / "joern", "--script", ROOT / "cartographer/export_ast.sc",
         "--param", "cpgPath=cpg.bin", "--param", "out=ast.json", "--param", "dataModel=lp64"],
        tmp_path, numeric_env, timeout=600)
    functions = json.loads((tmp_path / "ast.json").read_text())
    model = tmp_path / "Model.lean"
    run([sys.executable, ROOT / "cartographer/render_lean.py", tmp_path / "ast.json", model, "Numeric"],
        ROOT, numeric_env)
    calls = []
    for name, args in CASES[language]:
        full = {"python": f"numbers.py:<module>.{name}", "java": f"Numbers.{name}:", "go": f"numbers.{name}",
                "c": name, "js": f"numbers.js::program:{name}"}[language]
        candidates = [f for f in functions if
                      (f["name"].startswith(full) if language == "java" else f["name"] == full)]
        assert len(candidates) == 1, (name, [f["name"] for f in functions])
        f = candidates[0]
        values = [f".float (Fl.ofBits {struct.unpack('>Q', struct.pack('>d', n))[0]})"
                  if isinstance(n, float) else f".int ({n})" for n in args]
        if language == "js":
            assert f["params"] == ["this", "a"] or f["params"] == ["this", "a", "b"]
            values.insert(0, ".unit")
        assert len(values) == len(f["params"])
        calls.append(f"runFunc program 200 {json.dumps(f['name'])} [{', '.join(values)}]")
    # Check native agreement before proof search: a translation error must be
    # reported as its concrete outcome, not hidden behind an expensive failed goal.
    header = model.read_text() + "\nopen Autoform.Core Autoform.Generated.Numeric\n"
    proofs = f"example : {calls[0]} = .val (.int ({expected[0]})) := by rfl\n"
    if language == "c":
        for i, (name, _) in enumerate(CASES[language]):
            if name.startswith(("remainder_", "compound_", "narrow_", "mask_", "loop_", "conditional_",
                                "assignment_", "field_", "array_", "logical_")):
                proofs += f"example : {calls[i]} = .val (.int ({expected[i]})) := by first | rfl | cbv\n"
    if language in ("python", "java", "js"):
        for i, (name, _) in enumerate(CASES[language]):
            if language == "python" or name.startswith(("call", "aug", "index", "cast", "shiftWrapped", "shiftNested")):
                if language == "python":
                    # Kernel computation avoids elaborator unification expanding
                    # the heap/constructor trace. The expected integer still comes
                    # independently from CPython, and every other outcome fails.
                    proofs += (
                        f"example : (match {calls[i]} with\n"
                        f"  | .val (.int n) => n == ({expected[i]} : Int)\n"
                        "  | _ => false) = true := by\n"
                        '  first | decide +kernel | fail "native observation not established"\n')
                    continue
                value = f".int ({expected[i]})"
                if language == "js" and not name.startswith(("augShift", "augUnsigned", "index", "shift")):
                    bits = struct.unpack('>Q', struct.pack('>d', expected[i]))[0]
                    value = f".float (Fl.ofBits {bits})"
                proofs += f"example : {calls[i]} = .val ({value}) := by first | rfl | cbv\n"
    driver = header + "def main : IO Unit := do\n"
    for call in calls:
        driver += f'''  match {call} with
  | .val (.int n) => IO.println n
  | .val (.bool b) => IO.println (if b then 1 else 0)
  | .val (.float n) =>
    if n.fmt == .binary64 then IO.println ("float:" ++ toString n.bits)
    else throw (IO.userError "unexpected floating-point format")
  | other => throw (IO.userError (reprStr other))
'''
    (tmp_path / "Check.lean").write_text(driver)
    actual = run(["lake", "env", "lean", "--run", tmp_path / "Check.lean"], ROOT, numeric_env)
    observed = [struct.unpack('>d', int(s[6:]).to_bytes(8, 'big'))[0]
                if s.startswith('float:') else int(s) for s in actual.splitlines()]
    assert observed == expected
    (tmp_path / "Proofs.lean").write_text(header + proofs)
    # Kernel computation over a boxed-container program is slow under machine load; the
    # receiver-gap test already allows 600 s for the same kind of run.
    run(["lake", "env", "lean", tmp_path / "Proofs.lean"], ROOT, numeric_env, timeout=600)

    # The target model is evidence, not a host-size guess. Removing it refuses
    # target-sized arithmetic while preserving fixed-width Java/Go operations.
    if language in ("c", "java", "go"):
        run([joern_home / "joern", "--script", ROOT / "cartographer/export_ast.sc",
             "--param", "cpgPath=cpg.bin", "--param", "out=unknown.json",
             "--param", "dataModel=unknown"], tmp_path, numeric_env, timeout=600)
        unknown = {f["name"]: f for f in json.loads((tmp_path / "unknown.json").read_text())}
        if language == "c":
            assert unknown["add"]["body"]["e"] == {"k": "hole", "label": "numeric:unknown-type:+"}
            assert unknown["literal"]["body"]["e"] == {"k": "hole", "label": "numeric:unknown-type:+"}
            assert unknown["wrap"]["body"]["e"]["a"]["op"] == "num:c:u32:+"
        elif language == "java":
            assert unknown["Numbers.add:long(long,long)"]["body"]["e"]["op"] == "num:java:i64:+"
        else:
            assert unknown["numbers.Word"]["body"]["e"] == {"k": "hole", "label": "numeric:unknown-type:+"}
            assert unknown["numbers.Add"]["body"]["e"]["op"] == "num:go:i64:+"


@pytest.mark.parametrize("subject", ["indexSnapshot", "indexString"])
def test_js_indexed_native_conformance(subject, tmp_path, numeric_env, monkeypatch):
    # Formerly two strict xfails. `indexSnapshot` needed arrays to be objects with
    # identity -- `__ecma.Array.factory()` is now an empty boxed list and `push` mutates it
    # in place, returning the new length as Node does. `indexString` needed UTF-16 unit
    # indexing, which `String.utf16At` provides for the `.javascript` dialect only.
    monkeypatch.setitem(CASES, "js", [(subject, [1, 2]), (subject, [-3, 7])])
    test_joern_native_numeric("js", tmp_path, numeric_env)


def test_python_negative_shift_raises_valueerror_by_name():
    """A trap's string is read downstream as the raised exception's CLASS NAME.

    `numToE` turns `.trap r` into `.exn (.str r)`, and Python `except` dispatch compares
    that against `Stdlib.excNames`. The shift-count trap carried its prose reason, so
    Core raised `.exn (.str "negative shift count")` where CPython raises `ValueError` --
    no handler could ever match it, and the exporter's dispatch holed instead of
    catching. The table in `Numeric.lean` said `ValueError` all along; the implementation
    did not.
    """
    numeric = (ROOT / 'Autoform/Lang/Core/Numeric.lean').read_text()
    assert 'shiftCountFault := some "ValueError"' in numeric, (
        'the python config must name the exception its shift-count trap raises')
    assert '.trap (c.shiftCountFault.getD "negative shift count")' in numeric
    # Other dialects keep the prose reason: C's negative shift is undefined, not a
    # trap that names an exception, and nothing should start calling it ValueError.
    assert 'shiftCountFault  : Option String := none' in numeric


def test_every_exception_producer_in_core_is_pinned_by_a_theorem():
    """The `control:TRY-exception-representation` guard rests on these.

    Python `except` dispatch compares the pending exception against `excNames` as a
    string. Whether the guard's else-branch is reachable is a question about Core's
    exception producers, and each is now pinned. One of them was genuinely unsafe when
    checked -- the shift-count trap named itself in prose -- so these are theorems rather
    than a comment asserting the obvious.
    """
    stdlib = (ROOT / 'Autoform/Lang/Core/Stdlib.lean').read_text()
    numeric = (ROOT / 'Autoform/Lang/Core/Numeric.lean').read_text()
    assert 'theorem makeException_excSafe' in stdlib
    assert 'theorem raiseValue_excSafe' in stdlib
    assert 'theorem python_shiftCount_trap' in numeric
    # The predicate must stay a statement about `excNames`, not about some other list
    # that could drift away from the one the exporter's dispatch actually compares to.
    assert 'def ExcSafe (v : Val) : Prop := ∃ n, v = .str n ∧ n ∈ excNames' in stdlib


class TestJavaScriptContainers:
    """Source-level pins for the JavaScript array/string support. The end-to-end check is
    `test_js_indexed_native_conformance`, which needs Joern and Node; these hold the shape
    of the implementation in place when that suite is skipped."""

    def test_array_factory_becomes_an_empty_list_literal(self):
        src = (ROOT / 'cartographer/export_ast.sc').read_text()
        assert '"__ecma.Array.factory"' in src
        assert 'ujson.Obj("k" -> "listE", "items" -> ujson.Arr())' in src
        # a factory WITH arguments is a different constructor and must not be swallowed
        assert 'args.isEmpty && kwArgs.isEmpty' in src

    def test_boxing_is_a_named_dialect_predicate(self):
        """The `== .python` gate was widened by naming the property, not by adding
        another disjunct at each of the sites that read it."""
        syntax = (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert 'def boxesContainers : Dialect → Bool' in syntax
        assert '| .python | .javascript => true' in syntax
        assert 'if ctx.dialect.boxesContainers then' in sem

    def test_push_returns_the_new_length(self):
        """The one line that justifies a separate JavaScript method table."""
        stdlib = (ROOT / 'Autoform/Lang/Core/Stdlib.lean').read_text()
        assert 'm (.val (.int vs\'.length)) (.list vs\')' in stdlib
        assert 'theorem knowsMethod_javascript_complete' in stdlib

    def test_utf16_helpers_exist_and_refuse_lone_surrogates(self):
        syntax = (ROOT / 'Autoform/Lang/Core/Syntax.lean').read_text()
        sem = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
        assert 'def _root_.String.utf16Units' in syntax
        assert 'def _root_.String.utf16At' in syntax
        assert 'index:js-lone-surrogate' in sem


def test_try_dispatch_guard_is_gone_and_the_invariant_is_a_theorem():
    """`control:TRY-exception-representation` was a guard standing in for a proof.

    The exporter compared the pending exception against every represented class name and
    holed when it was not one of them, because `Stmt.raise` could raise an arbitrary
    value. `Stmt.raise` now classifies Python values through `pythonRaise`, and
    `ExcSafe.lean` proves by simultaneous induction over the interpreter that under
    `.python` every raised value names a represented class. The guard is removed on the
    strength of that theorem, so both facts are asserted together: if either the guard
    comes back or the theorem disappears, this notices.
    """
    exporter = (ROOT / 'cartographer/export_ast.sc').read_text()
    assert 'control:TRY-exception-representation' not in exporter
    semantics = (ROOT / 'Autoform/Lang/Core/Semantics.lean').read_text()
    assert 'def pythonRaise (extra : List String) (v : Val) : EResult' in semantics
    assert 'match pythonRaise ctx.excClasses v with' in semantics
    excsafe = (ROOT / 'Autoform/Lang/Core/ExcSafe.lean').read_text()
    for name in ('theorem pythonRaise_excSafe', 'theorem evalExpr_exn_excSafe',
                 'theorem execStmt_exn_excSafe'):
        assert name in excsafe, name
    # The proof is only worth the guard's removal if it is a proof.
    assert 'sorry' not in excsafe.replace('-- sorry', '')
    root = (ROOT / 'Autoform.lean').read_text()
    assert 'import Autoform.Lang.Core.ExcSafe' in root
