"""`java.lang.String` in Core (`Stdlib.javaStringMethod`) against the real JVM.

Two checks, both differential:

1. The computation theorems `java_str_*` in `Autoform/Lang/Core/Stdlib.lean` (each closed
   by `rfl`, so the kernel has evaluated it) are parsed here and every one is run on the
   JVM: the value the kernel accepted must be the value Java returns. Needs `javac`/`java`.
2. A generated grid of receivers x methods x arguments (empty, ASCII, Latin-1, CJK, an
   embedded NUL, and two strings with a supplementary character) is evaluated by Lean
   (`lake env lean`, `#eval` of `Stdlib.method .java`) and by the JVM, case for case. A
   BMP case must AGREE; a case whose receiver or string argument leaves the BMP must be a
   hole in Lean, never an answer. Needs the JVM and the built Core (`lake`).

Java 17 locally, 21 in CI; the JVM version is printed in the assertion messages. A missing
toolchain is a named SKIP, never a pass.
"""
import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
STDLIB = ROOT / "Autoform" / "Lang" / "Core" / "Stdlib.lean"
HAVE_JVM = shutil.which("javac") is not None and shutil.which("java") is not None
LAKE = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
CORE_BUILT = (ROOT / ".lake/build/lib/lean/Autoform/Lang/Core/Stdlib.olean").exists()

# ---------------------------------------------------------------- a tiny JVM evaluator
# Each case: (receiver code points, method, args) with args as ("str", codepoints) |
# ("int", n) | ("null",) | ("bool", b). Answers: "int N" | "bool true" | "str <hex units>"
# | "exn SimpleName".

JAVA = r"""
public class JStr {
  static String mk(int[] cps) {
    StringBuilder b = new StringBuilder();
    for (int c : cps) b.appendCodePoint(c);
    return b.toString();
  }
  static String units(String s) {
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < s.length(); i++) { if (i > 0) b.append(','); b.append((int) s.charAt(i)); }
    return b.toString();
  }
  static String show(Object o) {
    if (o instanceof Integer) return "int " + o;
    if (o instanceof Character) return "int " + (int) (Character) o;
    if (o instanceof Boolean) return "bool " + o;
    if (o instanceof String) return "str " + units((String) o);
    return "other";
  }
  interface C { Object run(); }
  static void go(C c) {
    try { System.out.println(show(c.run())); }
    catch (RuntimeException e) { System.out.println("exn " + e.getClass().getSimpleName()); }
  }
  public static void main(String[] a) {
@CASES@
  }
}
"""


def _cps(s):
    return [ord(c) for c in s]


def _java_str(s):
    return "mk(new int[]{%s})" % ",".join(str(c) for c in _cps(s))


def _java_arg(a):
    kind = a[0]
    if kind == "str":
        return _java_str(a[1])
    if kind == "int":
        return "%d" % a[1]
    if kind == "null":
        return "(String) null"
    if kind == "bool":
        return "Boolean.valueOf(%s)" % ("true" if a[1] else "false")
    raise ValueError(a)


def _java_call(recv, method, args):
    r = _java_str(recv)
    if method == "equals":
        a = args[0]
        # `equals(Object)`: box the primitives exactly as a Java caller passing an
        # `int`/`boolean` to an `Object` parameter would (Integer/Boolean).
        arg = {"int": lambda: "Integer.valueOf(%d)" % a[1],
               "null": lambda: "(Object) null"}.get(a[0], lambda: _java_arg(a))()
        return "%s.equals(%s)" % (r, arg)
    if method == "indexOf" and args[0][0] == "int":
        return "%s.indexOf(%d)" % (r, args[0][1])
    return "%s.%s(%s)" % (r, method, ", ".join(_java_arg(a) for a in args))


def run_jvm(cases, tmp_path):
    body = "\n".join("    go(() -> %s);" % _java_call(*c) for c in cases)
    src = tmp_path / "JStr.java"
    src.write_text(JAVA.replace("@CASES@", body))
    r = subprocess.run(["javac", "-nowarn", "-d", str(tmp_path), str(src)],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr[-2000:]
    out = subprocess.run(["java", "-cp", str(tmp_path), "JStr"],
                         capture_output=True, text=True, timeout=120)
    assert out.returncode == 0, out.stderr[-2000:]
    lines = out.stdout.splitlines()
    assert len(lines) == len(cases), (len(lines), len(cases))
    return lines


def jvm_version():
    r = subprocess.run(["java", "-version"], capture_output=True, text=True)
    return (r.stderr or r.stdout).splitlines()[0] if (r.stderr or r.stdout) else "?"


# ------------------------------------------------------------- 1. the theorems vs the JVM

THEOREM = re.compile(
    r'theorem (java_str_\w+) : method \.java \[\] \(\.str "((?:[^"\\]|\\.)*)"\) "(\w+)" '
    r'\[(.*?)\] =\s*some \(\[\], \.pure \((.*?)\)\) := rfl', re.S)


def _lean_arg(text):
    text = text.strip()
    m = re.fullmatch(r'\.str "((?:[^"\\]|\\.)*)"', text)
    if m:
        return ("str", m.group(1))
    m = re.fullmatch(r'\.int \(?(-?\d+)\)?', text)
    if m:
        return ("int", int(m.group(1)))
    if text == ".unit":
        return ("null",)
    raise ValueError(text)


def _lean_expected(text):
    text = " ".join(text.split())
    for pat, fmt in ((r'\.val \(\.int \(?(-?\d+)\)?\)', lambda g: "int %d" % int(g)),
                     (r'\.val \(\.bool (true|false)\)', lambda g: "bool " + g),
                     (r'\.val \(\.str "((?:[^"\\]|\\.)*)"\)',
                      lambda g: "str " + ",".join(str(c) for c in _cps(g))),
                     (r'\.exn \(\.str "(\w+)"\)', lambda g: "exn " + g)):
        m = re.fullmatch(pat, text)
        if m:
            return fmt(m.group(1))
    raise ValueError(text)


def stated_theorems():
    text = STDLIB.read_text(encoding="utf-8")
    out = []
    for name, recv, method, args, expected in THEOREM.findall(text):
        arg_list = [a for a in re.split(r',\s*(?=\.)', args) if a.strip()] if args.strip() else []
        out.append((name, recv, method, [_lean_arg(a) for a in arg_list], _lean_expected(expected)))
    return out


def test_theorem_block_is_parsed():
    thms = stated_theorems()
    names = {t[0] for t in thms}
    # Every positive `java_str_*` theorem of the block is in the parse (the two non-BMP
    # ones state `= none` and are checked by the grid below).
    declared = set(re.findall(r'theorem (java_str_\w+) :', STDLIB.read_text(encoding="utf-8")))
    assert declared - names == {"java_str_nonBmp_length", "java_str_nonBmp_arg"}, declared - names
    assert len(thms) >= 25


@pytest.mark.skipif(not HAVE_JVM, reason="javac/java not on PATH: the JVM differential cannot run")
def test_kernel_checked_answers_are_the_jvm_answers(tmp_path):
    thms = stated_theorems()
    got = run_jvm([(t[1], t[2], t[3]) for t in thms], tmp_path)
    bad = [(t[0], t[4], g) for t, g in zip(thms, got) if t[4] != g]
    assert bad == [], "%s: %r" % (jvm_version(), bad)


# ------------------------------------------------------------------- 2. the generated grid

POOL = ["", "a", "abc", "banana", "héllo", "日本語", "a\u0000b", "AbC",
        "\U0001F600", "a\U0001F600b"]


def _bmp(s):
    return all(ord(c) < 0x10000 for c in s)


def grid():
    cases = []
    for r in POOL:
        n = len(r.encode("utf-16-le")) // 2
        cases += [(r, "length", []), (r, "isEmpty", []), (r, "toString", [])]
        for i in range(-1, n + 2):
            cases.append((r, "charAt", [("int", i)]))
            cases.append((r, "substring", [("int", i)]))
            for j in range(-1, n + 2):
                cases.append((r, "substring", [("int", i), ("int", j)]))
        for t in POOL + ["na", "an", "b", "llo", "本"]:
            for m in ("equals", "indexOf", "startsWith", "endsWith"):
                cases.append((r, m, [("str", t)]))
        for m in ("equals", "indexOf", "startsWith", "endsWith"):
            cases.append((r, m, [("null",)]))
        cases.append((r, "equals", [("int", 97)]))
        cases.append((r, "equals", [("bool", True)]))
        for ch in (97, 0, 233, 0x672c, 0xD800, 0x1F600, -1, 0x110000):
            cases.append((r, "indexOf", [("int", ch)]))
    return cases


def _lean_string(s):
    return "(String.ofList [%s])" % ", ".join("Char.ofNat %d" % c for c in _cps(s))


def _lean_val(a):
    return {"str": lambda: ".str " + _lean_string(a[1]), "int": lambda: ".int (%d)" % a[1],
            "null": lambda: ".unit", "bool": lambda: ".bool %s" % ("true" if a[1] else "false")}[a[0]]()


LEAN_HEAD = """import Autoform.Lang.Core.Stdlib
open Autoform.Core

def showR : Option (Heap × Stdlib.MethodResult) → String
  | none => "HOLE"
  | some (_, .pure (.val (.int i))) => s!"int {i}"
  | some (_, .pure (.val (.bool b))) => s!"bool {b}"
  | some (_, .pure (.val (.str s))) => "str " ++ ",".intercalate (s.toList.map (fun c => toString c.toNat))
  | some (_, .pure (.exn (.str n))) => s!"exn {n}"
  | _ => "other"

"""


def run_lean(cases, tmp_path):
    lines = [LEAN_HEAD]
    for r, m, args in cases:
        lines.append('#eval IO.println (showR (Stdlib.method .java [] (.str %s) "%s" [%s]))'
                     % (_lean_string(r), m, ", ".join("(" + _lean_val(a) + ")" for a in args)))
    src = tmp_path / "JStrGrid.lean"
    src.write_text("\n".join(lines) + "\n")
    out = subprocess.run([LAKE, "env", "lean", str(src)], cwd=str(ROOT),
                         capture_output=True, text=True, timeout=1200)
    assert out.returncode == 0, (out.stdout + out.stderr)[-3000:]
    got = out.stdout.splitlines()
    assert len(got) == len(cases), (len(got), len(cases), out.stdout[-500:])
    return got


@pytest.mark.skipif(not HAVE_JVM, reason="javac/java not on PATH: the JVM differential cannot run")
@pytest.mark.skipif(not CORE_BUILT, reason="Core is not built (.lake/build/.../Stdlib.olean absent): "
                    "run `lake build Autoform.Lang.Core.Stdlib` first")
def test_grid_agrees_with_the_jvm_and_holes_outside_the_bmp(tmp_path):
    cases = grid()
    jvm = run_jvm(cases, tmp_path)
    lean = run_lean(cases, tmp_path)
    agree, holes_bmp, disagree, answered_non_bmp, holes_non_bmp = 0, [], [], [], 0
    for c, j, l in zip(cases, jvm, lean):
        r, m, args = c
        bmp = _bmp(r) and all(_bmp(a[1]) for a in args if a[0] == "str")
        if not bmp:
            if l == "HOLE":
                holes_non_bmp += 1
            else:
                answered_non_bmp.append((c, l, j))
        elif l == "HOLE":
            holes_bmp.append(c)
        elif l == j:
            agree += 1
        else:
            disagree.append((c, l, j))
    msg = "%s: %d agree, %d BMP holes, %d non-BMP holes" % (
        jvm_version(), agree, len(holes_bmp), holes_non_bmp)
    assert disagree == [], msg + " DISAGREE %r" % disagree[:10]
    assert answered_non_bmp == [], msg + " non-BMP answered %r" % answered_non_bmp[:10]
    # Every BMP case of the grid is a modelled shape, so none may hole.
    assert holes_bmp == [], msg + " BMP holes %r" % holes_bmp[:10]
    assert agree >= 900, msg
    print(msg)
