"""Python `str` methods, `in` and `list(iterable)` in Core against CPython.

Three checks, all differential:

1. Every `#guard pyShows ...` (Stdlib.lean) and `#guard inShows ...` (Semantics.lean) line
   is parsed and run on THIS interpreter: the answer the guard states (and that `lake
   build` checked) must be CPython's, and a `hole` guard must name a shape CPython answers
   -- a refusal, never a disagreement. A `.javascript` `inShows` line states Node's answer
   (JavaScript's `in` needs an Object on the right): kernel-checked, but no CPython case.
   Needs nothing but Python.
2. A generated grid of receivers x methods x arguments (ASCII, Latin-1, CJK, a
   non-breaking space, the ASCII separators \\x1c-\\x1f, an emoji) is evaluated by Lean
   (`#eval` of `Stdlib.method .python` / `valIn`) and by CPython, case for case. An answer
   must AGREE; a hole is allowed only where the section note of `pyStringMethod` says so
   (case mapping or default whitespace on a non-ASCII receiver). Needs the built Core.
   `#guard rangeShows ...` (the `for x in range(...)` header) is checked the same way.
3. `examples/python_control/strings.py` through Joern, the exporter and `runFunc`,
   against CPython, including the `except ... as e: e.lower()` payload hole. Needs
   `AUTOFORM_TEST_JOERN=1`.

A missing toolchain is a named SKIP, never a pass.
"""
import ast
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
STDLIB = ROOT / "Autoform" / "Lang" / "Core" / "Stdlib.lean"
SEMANTICS = ROOT / "Autoform" / "Lang" / "Core" / "Semantics.lean"
LAKE = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
CORE_BUILT = (ROOT / ".lake/build/lib/lean/Autoform/Lang/Core/Semantics.olean").exists()


# ----------------------------------------------------------- a parser for Lean `Val` text

def _lean_string(text, i):
    """Decode a Lean string literal starting at text[i] == '"'; return (value, next)."""
    assert text[i] == '"'
    out, i = [], i + 1
    while text[i] != '"':
        c = text[i]
        if c == "\\":
            e = text[i + 1]
            if e == "x":
                out.append(chr(int(text[i + 2:i + 4], 16)))
                i += 4
                continue
            if e == "u" and text[i + 2] == "{":
                j = text.index("}", i)
                out.append(chr(int(text[i + 3:j], 16)))
                i = j + 1
                continue
            if e == "u":
                out.append(chr(int(text[i + 2:i + 6], 16)))
                i += 6
                continue
            out.append({"n": "\n", "t": "\t", "r": "\r", "\\": "\\", '"': '"', "'": "'"}[e])
            i += 2
            continue
        out.append(c)
        i += 1
    return "".join(out), i + 1


class _P:
    def __init__(self, text):
        self.t, self.i = text, 0

    def ws(self):
        while self.i < len(self.t) and self.t[self.i] == " ":
            self.i += 1

    def eat(self, s):
        self.ws()
        assert self.t.startswith(s, self.i), (s, self.t[self.i:])
        self.i += len(s)

    def peek(self, s):
        self.ws()
        return self.t.startswith(s, self.i)

    def val(self):
        self.ws()
        if self.peek("("):
            self.eat("(")
            v = self.val()
            self.eat(")")
            return v
        for kw, f in ((".str ", self._str), (".int ", self._int), (".unit", lambda: None),
                      (".bool ", self._bool), (".list ", lambda: self._seq(list)),
                      (".tuple ", lambda: self._seq(tuple)), (".dict ", self._dict)):
            if self.peek(kw):
                self.eat(kw.strip())
                return f()
        raise ValueError(self.t[self.i:])

    def _str(self):
        self.ws()
        v, self.i = _lean_string(self.t, self.i)
        return v

    def _int(self):
        self.ws()
        m = re.compile(r"\((-?\d+)\)|(-?\d+)").match(self.t, self.i)
        self.i = m.end()
        return int(m.group(1) or m.group(2))

    def _bool(self):
        self.ws()
        for b in ("true", "false"):
            if self.t.startswith(b, self.i):
                self.i += len(b)
                return b == "true"
        raise ValueError

    def vals(self):
        self.eat("[")
        out = []
        while not self.peek("]"):
            out.append(self.val())
            if self.peek(","):
                self.eat(",")
        self.eat("]")
        return out

    def _seq(self, kind):
        return kind(self.vals())

    def _dict(self):
        self.eat("[")
        out = {}
        while not self.peek("]"):
            self.eat("(")
            k = self.val()
            self.eat(",")
            out[k] = self.val()
            self.eat(")")
            if self.peek(","):
                self.eat(",")
        self.eat("]")
        return out

    def string(self):
        return self._str()


def py_shows(recv, method, args):
    """`pyShows`'s rendering of CPython's answer."""
    try:
        return "val " + repr(getattr(recv, method)(*args))
    except Exception as e:  # the exception's class is the observation
        return "exn " + type(e).__name__


def py_in(x, c):
    try:
        return "True" if x in c else "False"
    except Exception as e:
        return "exn " + type(e).__name__


def stated_method_guards():
    out = []
    for line in STDLIB.read_text(encoding="utf-8").splitlines():
        if not line.startswith("#guard pyShows "):
            continue
        p = _P(line[len("#guard pyShows "):])
        recv = p.val()
        method = p.string()
        args = p.vals()
        expected = p.string()
        out.append((line, recv, method, args, expected))
    return out


def stated_in_guards():
    out = []
    for line in SEMANTICS.read_text(encoding="utf-8").splitlines():
        if not line.startswith("#guard inShows "):
            continue
        p = _P(line[len("#guard inShows "):])
        if p.peek(".python"):
            p.eat(".python")
            d = ".python"
        elif p.peek(".javascript"):
            p.eat(".javascript")
            d = ".javascript"
        else:
            raise ValueError(p.t[p.i:])
        x, c = p.val(), p.val()
        p.eat("==")
        out.append((line, d, x, c, p.string()))
    return out


# ------------------------------------------------------------- 1. the guards vs CPython

def test_guard_blocks_are_parsed():
    ms, ins = stated_method_guards(), stated_in_guards()
    names = {m for _, _, m, _, _ in ms}
    assert {"lower", "upper", "strip", "lstrip", "rstrip", "split", "startswith",
            "endswith", "replace", "join"} <= names
    assert len(ms) >= 55 and len(ins) >= 12
    assert {d for _, d, _, _, _ in ins} == {".python", ".javascript"}


def test_kernel_checked_method_guards_are_cpython_answers():
    bad, refused = [], 0
    for line, recv, method, args, expected in stated_method_guards():
        got = py_shows(recv, method, args)
        if expected.startswith("hole "):
            # a refusal must be of a call CPython ANSWERS (otherwise it should raise)
            assert got.startswith("val "), (line, got)
            refused += 1
        elif expected == "none":
            continue
        elif got != expected:
            bad.append((line, got))
    assert bad == [], "%s: %r" % (sys.version.split()[0], bad)
    assert refused >= 4


def stated_range_guards():
    out = []
    for line in STDLIB.read_text(encoding="utf-8").splitlines():
        if not line.startswith("#guard rangeShows "):
            continue
        p = _P(line[len("#guard rangeShows "):])
        args = p.vals()
        p.eat("==")
        out.append((line, args, p.string()))
    return out


def test_range_guards_are_cpython_answers():
    """`<python-range>` (a `for` header's `range(...)`) yields `list(range(*args))`."""
    guards = stated_range_guards()
    assert len(guards) >= 12
    for line, args, want in guards:
        try:
            got = str(list(range(*args)))
        except Exception as e:
            got = "exn " + type(e).__name__
        if want.startswith("hole "):
            assert len(range(*args)) > 100000, line   # refused only for its length
        else:
            assert got == want, (line, got)


def test_str_method_names_are_absent_from_scalars_and_tuples():
    """`Stdlib.missingMethod`: a `str` method name on an int, bool, float, None or tuple is
    CPython's AttributeError -- the names are read from `pyStrMethodNames` itself."""
    text = STDLIB.read_text(encoding="utf-8")
    block = re.search(r"def pyStrMethodNames : List String :=\s*\[(.*?)\]", text, re.S).group(1)
    names = re.findall(r'"(\w+)"', block)
    assert len(names) == 10
    for receiver in (5, True, 1.5, None, ("a",)):
        for name in names:
            assert not hasattr(receiver, name), (receiver, name)
            with pytest.raises(AttributeError):
                getattr(receiver, name)()


def test_kernel_checked_in_guards_are_cpython_answers():
    bad = [(line, py_in(x, c)) for line, d, x, c, want in stated_in_guards()
           if d == ".python" and py_in(x, c) != want]
    assert bad == [], bad


# ------------------------------------------------------------------ 2. the generated grid

POOL = ["", "a", "Hello World", "  a  b\tc  ", "a,b,,c", "hub:US:x", "s3://Over/data",
        "\x1c x\x1f", "..a.b..", "aaaa", "héllo", "日本:語", "a b", "ÀÉ", "x😀y"]
SEPS = ["", ",", ":", " ", "a", "aa", "b,", "語", "😀"]


def _ascii(s):
    return all(ord(c) < 0x80 for c in s)


def grid():
    cases = []
    for r in POOL:
        for m in ("lower", "upper", "strip", "lstrip", "rstrip", "split"):
            cases.append((r, m, []))
        cases.append((r, "split", [None, 1]))
        for t in SEPS:
            cases += [(r, "split", [t]), (r, "split", [t, 1]), (r, "split", [t, 0]),
                      (r, "startswith", [t]), (r, "endswith", [t]),
                      (r, "strip", [t]), (r, "lstrip", [t]), (r, "rstrip", [t]),
                      (r, "replace", [t, "<>"]), (r, "replace", [t, "", 2])]
        cases += [(r, "endswith", [("x", "c", "")]), (r, "join", [["p", "q"]]),
                  (r, "join", [[]]), (r, "join", ["xyz"]), (r, "join", [["p", 1]]),
                  (r, "split", [3]), (r, "strip", [3]), (r, "startswith", [3])]
    return cases


def in_grid():
    cases = []
    for r in POOL:
        for t in SEPS + POOL[:6]:
            cases.append((t, r))
        cases += [(1, r), (r, 5), (r, None), (r, [r, "a"]), (r, {"a": 1}), (r, ("a",))]
    return cases


def _lean_text(s):
    return "(String.ofList [%s])" % ", ".join("Char.ofNat %d" % ord(c) for c in s)


def _lean_val(v):
    if v is None:
        return ".unit"
    if isinstance(v, bool):
        return ".bool %s" % ("true" if v else "false")
    if isinstance(v, int):
        return ".int (%d)" % v
    if isinstance(v, str):
        return ".str " + _lean_text(v)
    if isinstance(v, list):
        return ".list [%s]" % ", ".join("(%s)" % _lean_val(x) for x in v)
    if isinstance(v, tuple):
        return ".tuple [%s]" % ", ".join("(%s)" % _lean_val(x) for x in v)
    if isinstance(v, dict):
        return ".dict [%s]" % ", ".join("((%s), (%s))" % (_lean_val(k), _lean_val(x))
                                         for k, x in v.items())
    raise TypeError(v)


LEAN_HEAD = """import Autoform.Lang.Core.Semantics
open Autoform.Core

def cps (s : String) : String := ",".intercalate (s.toList.map (fun c => toString c.toNat))
def showV : Val → String
  | .str s => "s" ++ cps s
  | .bool b => if b then "True" else "False"
  | .list vs => "[" ++ ";".intercalate (vs.map (fun | .str s => cps s | _ => "?")) ++ "]"
  | _ => "?"
def showM : Option (Heap × Stdlib.MethodResult) → String
  | none => "HOLE"
  | some (_, .pure (.val v)) => showV v
  | some (_, .pure (.exn (.str n))) => "exn " ++ n
  | some (_, .pure (.hole _)) => "HOLE"
  | _ => "other"
def showI : EResult → String
  | .val v => showV v
  | .exn (.str n) => "exn " ++ n
  | .hole _ => "HOLE"
  | _ => "other"
"""


def _cps(s):
    return ",".join(str(ord(c)) for c in s)


def _py_render(fn):
    try:
        v = fn()
    except Exception as e:
        return "exn " + type(e).__name__
    if isinstance(v, bool):
        return "True" if v else "False"
    if isinstance(v, str):
        return "s" + _cps(v)
    if isinstance(v, list):
        return "[" + ";".join(_cps(x) for x in v) + "]"
    return "?"


def run_lean(lines, tmp_path):
    src = tmp_path / "PyStrGrid.lean"
    src.write_text(LEAN_HEAD + "\n".join(lines) + "\n", encoding="utf-8")
    out = subprocess.run([LAKE, "env", "lean", str(src)], cwd=str(ROOT),
                         capture_output=True, text=True, timeout=1200)
    assert out.returncode == 0, (out.stdout + out.stderr)[-3000:]
    got = out.stdout.splitlines()
    assert len(got) == len(lines), (len(got), len(lines), out.stdout[-500:])
    return got


def _allowed_hole(r, m, args):
    """The section note's refusals: case mapping, or default whitespace, past ASCII."""
    if _ascii(r):
        return False
    return m in ("lower", "upper") or (m in ("strip", "lstrip", "rstrip", "split")
                                       and (not args or args[0] is None))


@pytest.mark.skipif(not CORE_BUILT, reason="Core is not built (.lake/build/.../Semantics.olean "
                    "absent): run `lake build Autoform.Lang.Core.Semantics` first")
def test_grid_agrees_with_cpython_and_holes_only_where_named(tmp_path):
    cases, ins = grid(), in_grid()
    lines = ['#eval IO.println (showM (Stdlib.method .python [] (.str %s) "%s" [%s]))'
             % (_lean_text(r), m, ", ".join("(%s)" % _lean_val(a) for a in args))
             for r, m, args in cases]
    lines += ["#eval IO.println (showI (valIn .python (%s) (%s)))" % (_lean_val(x), _lean_val(c))
              for x, c in ins]
    got = run_lean(lines, tmp_path)
    agree, holes, bad_holes, disagree = 0, 0, [], []
    for (r, m, args), lean in zip(cases, got[:len(cases)]):
        py = _py_render(lambda: getattr(r, m)(*args))
        if lean == "HOLE":
            if _allowed_hole(r, m, args):
                holes += 1
            else:
                bad_holes.append((r, m, args, py))
        elif lean == py:
            agree += 1
        else:
            disagree.append((r, m, args, lean, py))
    for (x, c), lean in zip(ins, got[len(cases):]):
        py = _py_render(lambda: x in c)
        if lean == py:
            agree += 1
        else:
            disagree.append(("in", x, c, lean, py))
    msg = "CPython %s: %d agree, %d named holes" % (sys.version.split()[0], agree, holes)
    assert disagree == [], msg + " DISAGREE %r" % disagree[:10]
    assert bad_holes == [], msg + " unexpected holes %r" % bad_holes[:10]
    assert agree >= 1800, msg
    print(msg)


# -------------------------------------------------------- 3. the pipeline, end to end

SOURCE = ROOT / "examples/python_control/strings.py"
SUBJECTS = ("classify", "lead_nodes", "words", "fields", "cleaned", "suffix", "copied",
            "shortfall", "member")
INPUTS = ("s3://data-sources/x", "S3://OVERRIDES/y", "s3://other", "/local/path", "",
          "hub:US", "node:DE:1", "nocolon", "  a b  c ", " x,y ,z", "..banana.x",
          "xyz", "abc", "b")


def _env():
    env = {k: os.environ[k] for k in ("PATH", "HOME", "LANG", "LC_ALL", "TMPDIR", "JAVA_HOME")
           if k in os.environ}
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    return env


def _run(args, cwd, env, timeout=600):
    p = subprocess.run(list(map(str, args)), cwd=cwd, env=env, text=True,
                       capture_output=True, timeout=timeout)
    assert p.returncode == 0, p.stdout[-3000:] + p.stderr[-3000:]
    return p.stdout


def _lean_show_value():
    return '''
partial def showR (h : Heap) : Val → String
  | .int i => toString i
  | .bool b => if b then "True" else "False"
  | .str s => "s" ++ ",".intercalate (s.toList.map (fun c => toString c.toNat))
  | .tuple vs => "(" ++ ";".intercalate (vs.map (showR h)) ++ ")"
  | .list vs => "[" ++ ";".intercalate (vs.map (showR h)) ++ "]"
  | .ref r => match (h.payload r).toVal with
              | some v => showR h v
              | none => "?ref"
  | _ => "?"
'''


def _py_show(v):
    if isinstance(v, bool):
        return "True" if v else "False"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, str):
        return "s" + _cps(v)
    if isinstance(v, tuple):
        return "(" + ";".join(_py_show(x) for x in v) + ")"
    if isinstance(v, list):
        return "[" + ";".join(_py_show(x) for x in v) + "]"
    return "?"


@pytest.fixture(scope="module")
def strings_model(tmp_path_factory):
    if os.environ.get("AUTOFORM_TEST_JOERN") != "1":
        pytest.skip("set AUTOFORM_TEST_JOERN=1 for the Python str-method pipeline")
    env = _env()
    if not shutil.which("lake", path=env["PATH"]):
        pytest.skip("Lean is not installed")
    work = tmp_path_factory.mktemp("python-strings")
    source = work / "source"
    source.mkdir()
    (source / SOURCE.name).write_bytes(SOURCE.read_bytes())
    joern = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    if (joern / "joern-cli").is_dir():
        joern /= "joern-cli"
    _run([joern / "joern-parse", source, "--language", "PYTHONSRC", "--output", "cpg.bin"],
         work, env)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=cpg.bin", "--param", "out=ast.json"], work, env)
    model = work / "Model.lean"
    _run([sys.executable, ROOT / "cartographer/render_lean.py", work / "ast.json", model,
          "Strings"], ROOT, env)
    return work, env, model.read_text() + "\nopen Autoform.Core Autoform.Generated.Strings\n"


def test_pipeline_matches_cpython(strings_model):
    work, env, header = strings_model
    spec = importlib.util.spec_from_file_location("native_strings_fixture", SOURCE)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    cases = []
    for name in SUBJECTS:
        for text in INPUTS:
            try:
                expected = "value:" + _py_show(getattr(module, name)(text))
            except Exception as e:
                expected = "exception:" + type(e).__name__
            cases.append((name, text, expected))
    driver = header + _lean_show_value() + "def main : IO Unit := do\n"
    for name, text, _ in cases:
        call = ('(let ctx : Ctx := { dialect := program.dialect, table := program.table };'
                ' match ctx.resolve "strings.py:<module>.%s" with'
                ' | some fn => applyFunc ctx 4000 [] fn none [.str %s] []'
                ' | none => ([], .hole "entry"))' % (name, _lean_text(text)))
        driver += '''  match %s with
  | (h, .val v) => IO.println ("value:" ++ showR h v)
  | (_, .exn (.str n)) => IO.println ("exception:" ++ n)
  | (_, other) => IO.println ("unexpected:" ++ reprStr other)
''' % call
    (work / "Observe.lean").write_text(driver, encoding="utf-8")
    observed = _run([LAKE, "env", "lean", "--run", work / "Observe.lean"], ROOT, env).splitlines()
    mismatches = [dict(subject=n, argument=t, native=w, model=o)
                  for (n, t, w), o in zip(cases, observed) if w != o]
    (work / "native-comparison.json").write_text(json.dumps(dict(
        cases=len(cases), mismatches=mismatches), indent=2) + "\n")
    assert len(observed) == len(cases)
    assert mismatches == [], json.dumps(mismatches[:10], indent=2)


def test_method_on_exception_binding_is_a_payload_hole(strings_model):
    work, _, _ = strings_model
    funcs = json.loads((work / "ast.json").read_text())
    subject = next(f for f in funcs if f["name"] == "strings.py:<module>.payload_method")
    text = json.dumps(subject["body"])
    # The binding holds the class NAME: `"KeyError".lower()` would answer "keyerror" where
    # CPython raises AttributeError. It must be a named hole, never an `mcall`.
    assert "exception:payload:lower" in text or "control:TRY-handler-binding" in text, text
    assert '"m": "lower"' not in text
