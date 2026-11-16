"""`list(...)` in Core against CPython.

A differential check, in the style of tests/test_python_str_methods.py: every
`#guard listShows ...` line (Stdlib.lean) is parsed and run on THIS interpreter. The
answer the guard states (and that `lake build` checked) must be CPython's; a `none`
guard -- the caller's `call:list` hole -- must be a shape CPython answers
deterministically, so the refusal is counted ignorance, never a hidden disagreement.

The four plain non-iterables (`int`, `bool`, `float`, `None`) are CPython's `TypeError`
("'int' object is not iterable"), which is what the `list` builtin raises; what the
model cannot classify -- an instance, which may define `__iter__`; a function or class
value, whose metaclass may make it iterable -- keeps the hole.

Needs nothing but Python: the Lean side of each guard was checked by `lake build`
before the test ran.
"""
import re
import struct
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STDLIB = ROOT / "Autoform" / "Lang" / "Core" / "Stdlib.lean"

# A `.fn` in a guard names a Python callable the parser must know by name.
FNS = {"len": len}


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
                      (".bool ", self._bool), (".float ", self._float),
                      (".list ", lambda: self._seq(list)),
                      (".tuple ", lambda: self._seq(tuple)),
                      (".fn ", self._fn), (".ref ", self._ref)):
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

    def _float(self):
        # `.float (Fl.ofBits 0x...)`: the bit pattern of a double, the encoding
        # `differential.py` emits (struct.pack('<Q', ...) round trip).
        self.ws()
        assert self.t.startswith("(Fl.ofBits ", self.i), self.t[self.i:]
        self.i += len("(Fl.ofBits ")
        m = re.compile(r"(0[xX][0-9a-fA-F]+|\d+)").match(self.t, self.i)
        self.i = m.end()
        self.eat(")")
        return struct.unpack("<d", struct.pack("<Q", int(m.group(1), 0)))[0]

    def _fn(self):
        self.ws()
        name, self.i = _lean_string(self.t, self.i)
        return FNS[name]

    def _ref(self):
        self._int()   # the address is irrelevant: an ordinary instance
        return object()

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

    def string(self):
        return self._str()


def py_list(x):
    """`listShows`'s rendering of CPython's answer."""
    try:
        return "val " + repr(list(x))
    except Exception as e:  # the exception's class is the observation
        return "exn " + type(e).__name__


def stated_list_guards():
    out = []
    for line in STDLIB.read_text(encoding="utf-8").splitlines():
        if not line.startswith("#guard listShows "):
            continue
        p = _P(line[len("#guard listShows "):])
        x = p.val()
        out.append((line, x, p.string()))
    return out


# --------------------------------------------------------------- the guards vs CPython

def test_guard_block_is_parsed():
    guards = stated_list_guards()
    assert len(guards) >= 9
    # the four plain non-iterables each have their own guard
    kinds = {type(x) for _, x, _ in guards}
    assert kinds >= {int, bool, float, type(None)}


def test_kernel_checked_list_guards_are_cpython_answers():
    bad, refused = [], 0
    for line, x, expected in stated_list_guards():
        got = py_list(x)
        if expected == "none":
            # a refusal must be of a call CPython answers deterministically: here, a
            # function or instance that cannot be iterated raises TypeError
            assert got == "exn TypeError", (line, got)
            refused += 1
        elif got != expected:
            bad.append((line, got))
    assert bad == [], "%s: %r" % (sys.version.split()[0], bad)
    assert refused >= 2
