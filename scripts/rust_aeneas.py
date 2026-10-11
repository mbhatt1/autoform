#!/usr/bin/env python3
"""rust_aeneas.py -- the Rust path: Charon + Aeneas model, ledger, differential oracle and
kernel-checked case theorems for one Cargo library crate. See docs/rust.md.

No Rust parser is written here. Every fact about the crate comes from a tool that owns it:

  public API     `cargo rustdoc --output-format json` (rustc's own view of what is public)
  model          Charon (LLBC) then Aeneas (Lean), the pinned pair in rust-pins.json
  holes          Charon's and Aeneas' own messages, and `#print axioms` on each function's
                 model (a `sorry` Aeneas left, or an external std function it only axiomatized)
  native truth   a generated cargo harness that calls the REAL function (debug profile)
  model truth    `#eval` of the Aeneas function in a SCRATCH Lake project (Lean v4.31.0 +
                 mathlib, never Autoform's own project), and for every agreeing case a theorem
                 `f args = result` that the kernel checks by `rfl` (no native_decide)

Every public function ends in exactly one ledger state: translated (the model is closed:
no sorry, no non-standard axiom) or a NAMED hole whose label quotes the tool. Every
translated function ends in exactly one oracle state: compared, or inconclusive with a
reason. Nothing is dropped without a line saying so.

Assumptions (each recorded in conformance.json under "assumptions"):
  * the harness is built in the DEBUG profile (overflow checks and debug assertions on),
    which is what Aeneas models; `--profile release` is expected to diverge on overflow;
  * any Rust panic corresponds to any Aeneas `fail` (the error kind is recorded, not compared);
  * Aeneas `div` is inconclusive, never agreement;
  * usize/isize are 64-bit (the harness host); the kernel cannot evaluate
    `System.Platform.numBits`, so usize/isize case theorems are expected not to prove.

Usage:
  rust_aeneas.py --crate DIR --module M --lean-project LP [--out DIR] [--profile debug|release]
                 [--seed N] [--cases N] [--random N] [--theorems-per-function N] [--fuel N]
                 [--assure]
Env: AENEAS_HOME = directory holding `aeneas`, `charon`, `charon-driver`, `rust-toolchain`
     (else they are looked up on PATH); AUTOFORM_SANDBOX as for every native run.
Exit: 0 completed, no divergence (with --assure: and no hole, inconclusive or unproved case);
      1 divergence (with --assure: any gap); 2 a tool or prerequisite is missing, or a stage failed.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import random
import re
import select
import shutil
import struct
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ANSI = re.compile(r"\x1b\[[0-9;?]*[A-Za-z]")


def load_pins(root=ROOT):
    with open(os.path.join(root, "rust-pins.json")) as fh:
        return json.load(fh)


class RustPathError(Exception):
    """A named failure of the Rust path. `name` is stable and machine-readable."""

    def __init__(self, name, message, hint=None):
        super().__init__(message)
        self.name, self.message, self.hint = name, message, hint

    def record(self):
        return {"error": self.name, "message": self.message, "hint": self.hint}


# --------------------------------------------------------------------------- tools

def tool(name, env=None):
    env = os.environ if env is None else env
    home = env.get("AENEAS_HOME")
    if home and os.access(os.path.join(home, name), os.X_OK):
        return os.path.join(home, name)
    return shutil.which(name, path=env.get("PATH"))


def pinned_rust_toolchain(env=None, pins=None):
    """The toolchain Charon was built against: AENEAS_HOME/rust-toolchain, else the pin."""
    env = os.environ if env is None else env
    home = env.get("AENEAS_HOME")
    path = os.path.join(home, "rust-toolchain") if home else None
    if path and os.path.isfile(path):
        m = re.search(r'channel\s*=\s*"([^"]+)"', open(path).read())
        if m:
            return m.group(1)
    return (pins or load_pins())["rust_toolchain"]


def missing(env=None):
    """Names of absent prerequisites (cargo, charon, aeneas, lake)."""
    return [n for n in ("cargo", "charon", "aeneas", "lake") if not tool(n, env)]


def run(cmd, timeout=None, **kw):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, **kw)
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout.decode() if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        err = exc.stderr.decode() if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return subprocess.CompletedProcess(cmd, 124, out, err + "\n[timeout after %ss]" % timeout)


def first_line(text):
    for line in (text or "").splitlines():
        if line.strip():
            return line.strip()
    return ""


# --------------------------------------------------------------------------- public API (rustdoc)

def public_functions(doc):
    """Every public function of the crate, from rustdoc JSON, in a stable order.

    Returns (functions, declarations). `declarations` are trait methods WITHOUT a body:
    they are signatures, not functions, and are listed by name instead of counted."""
    index, paths = doc["index"], doc.get("paths", {})
    root = index.get(str(doc.get("root")))
    crate = root.get("name") if root else None
    funcs, decls, seen = [], [], set()

    def path_of(item_id):
        p = paths.get(str(item_id))
        return list(p["path"]) if p else None

    def add(fid, item, kind, **extra):
        seen.add(str(fid))
        f = item["inner"]["function"]
        funcs.append(dict(id=str(fid), name=item["name"], kind=kind, sig=f["sig"],
                          generics=f.get("generics") or {}, header=f.get("header") or {},
                          span=item.get("span"), **extra))

    for iid, item in index.items():
        if item.get("crate_id") != 0:
            continue
        inner = item.get("inner", {})
        if "impl" in inner:
            im = inner["impl"]
            if im.get("is_synthetic") or im.get("blanket_impl") is not None:
                continue
            trait = im.get("trait")
            for mid in im.get("items", []):
                m = index.get(str(mid))
                if not m or "function" not in m.get("inner", {}) or m.get("crate_id") != 0:
                    continue
                if trait is None and m.get("visibility") != "public":
                    seen.add(str(mid))
                    continue
                add(mid, m, "trait_impl" if trait else "inherent", self_ty=im["for"],
                    trait=trait, trait_path=path_of(trait["id"]) if trait else None,
                    impl_generics=im.get("generics") or {})
        elif "trait" in inner:
            tpath = path_of(iid) or [crate, item["name"]]
            for mid in inner["trait"].get("items", []):
                m = index.get(str(mid))
                if not m or "function" not in m.get("inner", {}):
                    continue
                if m["inner"]["function"].get("has_body"):
                    add(mid, m, "trait_default", path=tpath + [m["name"]], trait_path=tpath)
                else:
                    seen.add(str(mid))
                    decls.append("::".join(tpath + [m["name"]]))
    for iid, item in index.items():
        if item.get("crate_id") != 0 or "function" not in item.get("inner", {}) or iid in seen:
            continue
        if item.get("visibility") != "public":
            continue
        p = path_of(iid)
        # A public function rustdoc did not place in `paths` is still counted: it becomes a
        # hole (no Aeneas definition can be matched to it), never a silent omission.
        add(iid, item, "free", path=p or [crate, item["name"]], unlocated=p is None)
    funcs.sort(key=lambda f: (display_name(f, doc), f["id"]))
    return funcs, sorted(decls)


def render_rust_type(t, doc, self_ty=None):
    """A Rust type as source text (for UFCS calls and display). Raises ValueError."""
    if t is None:
        return "()"
    if "primitive" in t:
        return t["primitive"]
    if "tuple" in t:
        items = [render_rust_type(x, doc, self_ty) for x in t["tuple"]]
        return "(" + ", ".join(items) + ("," if len(items) == 1 else "") + ")"
    if "array" in t:
        return "[%s; %s]" % (render_rust_type(t["array"]["type"], doc, self_ty), t["array"]["len"])
    if "slice" in t:
        return "[%s]" % render_rust_type(t["slice"], doc, self_ty)
    if "borrowed_ref" in t:
        r = t["borrowed_ref"]
        return "&" + ("mut " if r.get("is_mutable") else "") + render_rust_type(r["type"], doc, self_ty)
    if "generic" in t:
        if t["generic"] == "Self" and self_ty is not None:
            return render_rust_type(self_ty, doc)
        return t["generic"]
    if "resolved_path" in t:
        rp = t["resolved_path"]
        p = doc.get("paths", {}).get(str(rp.get("id")))
        name = "::".join(p["path"]) if p else rp["path"]
        args = rp.get("args") or {}
        ab = args.get("angle_bracketed") if isinstance(args, dict) else None
        if ab and ab.get("args"):
            parts = []
            for arg in ab["args"]:
                if "type" in arg:
                    parts.append(render_rust_type(arg["type"], doc, self_ty))
                elif "lifetime" in arg:
                    parts.append(arg["lifetime"])
                elif "const" in arg:
                    parts.append(str(arg["const"].get("expr", "_")))
            name += "<" + ", ".join(parts) + ">"
        return name
    raise ValueError("cannot render type %s" % next(iter(t), "?"))


def display_name(f, doc):
    if f["kind"] in ("free", "trait_default"):
        return "::".join(f["path"])
    try:
        selfs = render_rust_type(f["self_ty"], doc)
    except ValueError:
        selfs = "?"
    if f["kind"] == "trait_impl":
        trait = "::".join(f["trait_path"]) if f.get("trait_path") else f["trait"]["path"]
        return "<%s as %s>::%s" % (selfs, trait, f["name"])
    return "<%s>::%s" % (selfs, f["name"])


# --------------------------------------------------------------------------- encodable value types

INT_BITS = {"u8": 8, "u16": 16, "u32": 32, "u64": 64, "u128": 128, "usize": 64,
            "i8": 8, "i16": 16, "i32": 32, "i64": 64, "i128": 128, "isize": 64}
MAX_ARRAY = 16
HOST_BITS = struct.calcsize("P") * 8


def int_range(t):
    b = INT_BITS[t]
    return (0, 2 ** b - 1) if t[0] == "u" else (-2 ** (b - 1), 2 ** (b - 1) - 1)


class Unencodable(Exception):
    pass


def encode_type(t, self_ty=None, position="arg"):
    """rustdoc type -> the harness's exact value type, or Unencodable(reason).

    Encodable means BOTH the Rust literal/`{:?}` output and the Aeneas Lean value are exact:
    integers, bool, tuples and fixed-size arrays of those, and (arguments only) shared
    references to them, which Aeneas models as the value itself."""
    if t is None:
        if position == "ret":
            return ("unit",)
        raise Unencodable("missing type")
    if "primitive" in t:
        p = t["primitive"]
        if p in INT_BITS:
            if p in ("usize", "isize") and HOST_BITS != 64:
                raise Unencodable("%s on a %d-bit host (the oracle assumes 64-bit)" % (p, HOST_BITS))
            return ("int", p)
        if p == "bool":
            return ("bool",)
        if p in ("f32", "f64"):
            raise Unencodable("float type %s: not compared" % p)
        if p in ("str", "char"):
            raise Unencodable("%s type: string/char values are not encoded by the harness" % p)
        raise Unencodable("primitive type %s" % p)
    if "tuple" in t:
        if not t["tuple"]:
            if position == "ret":
                return ("unit",)
            raise Unencodable("unit argument")
        if len(t["tuple"]) == 1:
            raise Unencodable("1-tuple")
        return ("tuple", [encode_type(x, self_ty, "inner") for x in t["tuple"]])
    if "array" in t:
        n = t["array"]["len"]
        if not re.fullmatch(r"\d+", str(n)) or not 1 <= int(n) <= MAX_ARRAY:
            raise Unencodable("array length %s (only literal lengths 1..%d are encoded)" % (n, MAX_ARRAY))
        elem = encode_type(t["array"]["type"], self_ty, "inner")
        if elem[0] not in ("int", "bool"):
            raise Unencodable("array of non-scalar elements")
        return ("array", elem, int(n))
    if "borrowed_ref" in t:
        r = t["borrowed_ref"]
        if r.get("is_mutable"):
            raise Unencodable("mutable reference (&mut): Aeneas returns the updated value; "
                              "the harness does not compare it")
        if position != "arg":
            raise Unencodable("reference in a return or nested position")
        return ("ref", encode_type(r["type"], self_ty, "inner"))
    if "generic" in t:
        if t["generic"] == "Self" and self_ty is not None:
            return encode_type(self_ty, None, position)
        raise Unencodable("generic type parameter %s: no monomorphic instance is chosen" % t["generic"])
    if "slice" in t:
        raise Unencodable("slice type: not encoded")
    if "raw_pointer" in t:
        raise Unencodable("raw pointer")
    if "resolved_path" in t:
        raise Unencodable("type %s (struct/enum/alias): not encoded" % t["resolved_path"]["path"])
    raise Unencodable("type kind %s" % next(iter(t), "?"))


def lean_type(ty):
    k = ty[0]
    if k == "int":
        t = ty[1]
        return "Std." + ("U" if t[0] == "u" else "I") + ("size" if t[1:] == "size" else t[1:])
    if k == "bool":
        return "Bool"
    if k == "unit":
        return "Unit"
    if k == "tuple":
        return "(" + " × ".join(lean_type(x) for x in ty[1]) + ")"
    if k == "array":
        return "(Aeneas.Std.Array %s %d#usize)" % (lean_type(ty[1]), ty[2])
    if k == "ref":
        return lean_type(ty[1])
    raise ValueError(ty)


def lean_lit(ty, v):
    k = ty[0]
    if k == "int":
        if ty[1] in ("usize", "isize"):
            # `n#usize` must prove n <= the PLATFORM-INDEPENDENT bound (2^32-1), so a 64-bit
            # value cannot be written that way. The bit-vector is exact on the 64-bit host the
            # oracle requires (HOST_BITS); the kernel cannot reduce numBits either way.
            return "({ bv := BitVec.%s _ (%d) } : %s)" % ("ofNat" if ty[1] == "usize" else "ofInt", v, lean_type(ty))
        return "((%d)#%s)" % (v, ty[1])
    if k == "bool":
        return "true" if v else "false"
    if k == "unit":
        return "()"
    if k == "tuple":
        return "(" + ", ".join(lean_lit(t, x) for t, x in zip(ty[1], v)) + ")"
    if k == "array":
        return "(Aeneas.Std.Array.make %d#usize [%s])" % (ty[2], ", ".join(lean_lit(ty[1], x) for x in v))
    if k == "ref":
        return lean_lit(ty[1], v)
    raise ValueError(ty)


def rust_lit(ty, v):
    k = ty[0]
    if k == "int":
        return "%d%s" % (v, ty[1])
    if k == "bool":
        return "true" if v else "false"
    if k == "tuple":
        return "(" + ", ".join(rust_lit(t, x) for t, x in zip(ty[1], v)) + ")"
    if k == "array":
        return "[" + ", ".join(rust_lit(ty[1], x) for x in v) + "]"
    if k == "ref":
        return "&" + rust_lit(ty[1], v)
    raise ValueError(ty)


def lean_show(ty, e):
    """Lean expression printing `e : lean_type(ty)` exactly as Rust's `{:?}` prints it."""
    k = ty[0]
    if k == "int":
        return "(toString (%s).val)" % e
    if k == "bool":
        return "(toString %s)" % e
    if k == "unit":
        return '"()"'
    if k == "tuple":
        n = len(ty[1])
        parts = []
        for i, t in enumerate(ty[1]):
            acc = e + ".2" * i + (".1" if i < n - 1 else "")
            parts.append(lean_show(t, "(%s)" % acc))
        return '("(" ++ ' + ' ++ ", " ++ '.join(parts) + ' ++ ")")'
    if k == "array":
        return '("[" ++ ", ".intercalate ((%s).val.map (fun x => %s)) ++ "]")' % (e, lean_show(ty[1], "x"))
    raise ValueError(ty)


def parse_debug(ty, s):
    """Rust `{:?}` text -> Python value, by the declared type. Raises ValueError."""
    s = s.strip()
    k = ty[0]
    if k == "int":
        if not re.fullmatch(r"-?\d+", s):
            raise ValueError("not an integer: %r" % s)
        v = int(s)
        lo, hi = int_range(ty[1])
        if not lo <= v <= hi:
            raise ValueError("out of range for %s: %d" % (ty[1], v))
        return v
    if k == "bool":
        if s not in ("true", "false"):
            raise ValueError("not a bool: %r" % s)
        return s == "true"
    if k == "unit":
        if s != "()":
            raise ValueError("not unit: %r" % s)
        return ()
    if k in ("tuple", "array"):
        open_, close = ("(", ")") if k == "tuple" else ("[", "]")
        if not (s.startswith(open_) and s.endswith(close)):
            raise ValueError("bad %s: %r" % (k, s))
        parts, depth, cur = [], 0, ""
        for ch in s[1:-1]:
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth -= 1
            if ch == "," and depth == 0:
                parts.append(cur)
                cur = ""
            else:
                cur += ch
        if cur.strip():
            parts.append(cur)
        types = ty[1] if k == "tuple" else [ty[1]] * ty[2]
        if len(parts) != len(types):
            raise ValueError("arity mismatch in %r" % s)
        return tuple(parse_debug(t, p) for t, p in zip(types, parts))
    raise ValueError(ty)


def boundary_values(ty):
    k = ty[0]
    if k == "int":
        lo, hi = int_range(ty[1])
        s = {lo, hi, 0, 1, 2, 7, hi - 1, lo + 1, -1, hi // 2, lo // 2, 255, 256, 65535, 65536}
        return sorted(v for v in s if lo <= v <= hi)
    if k == "bool":
        return [False, True]
    if k == "ref":
        return boundary_values(ty[1])
    if k == "tuple":
        prod = list(itertools.product(*[boundary_values(t) for t in ty[1]]))
        return prod if len(prod) <= 64 else prod[::max(1, len(prod) // 64)][:64]
    if k == "array":
        b = boundary_values(ty[1])
        return [tuple([b[0]] * ty[2]), tuple([b[-1]] * ty[2]),
                tuple(b[i % len(b)] for i in range(ty[2])),
                tuple(b[(len(b) - 1 - i) % len(b)] for i in range(ty[2]))]
    raise ValueError(ty)


def random_value(ty, rng):
    k = ty[0]
    if k == "int":
        return rng.randint(*int_range(ty[1]))
    if k == "bool":
        return rng.random() < 0.5
    if k == "ref":
        return random_value(ty[1], rng)
    if k == "tuple":
        return tuple(random_value(t, rng) for t in ty[1])
    if k == "array":
        return tuple(random_value(ty[1], rng) for _ in range(ty[2]))
    raise ValueError(ty)


def cases_for(types, rng, cap=60, nrand=40):
    """Boundary-value product (sampled down to `cap`) plus `nrand` seeded random inputs."""
    if not types:
        return [()]
    comps = [boundary_values(t) for t in types]
    size = 1
    for c in comps:
        size *= len(c)
    if size <= 20000:
        full = list(itertools.product(*comps))
        if len(full) > cap:
            full = rng.sample(full, cap)
    else:
        full = [tuple(rng.choice(c) for c in comps) for _ in range(cap)]
    rand = [tuple(random_value(t, rng) for t in types) for _ in range(nrand)]
    seen, out = set(), []
    for c in full + rand:
        key = repr(c)
        if key not in seen:
            seen.add(key)
            out.append(c)
    return out


# --------------------------------------------------------------------------- Aeneas output

DECL = re.compile(r"^(?:noncomputable\s+|private\s+|protected\s+)*"
                  r"(def|axiom|opaque|structure|inductive|impl_def|abbrev|theorem|instance)\s+(\S+)")


def split_path(path):
    """Split a Rust/Aeneas path on `::` outside of {...}, <...>, [...] and (...)."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(path):
        ch = path[i]
        if ch in "{<[(":
            depth += 1
        elif ch in "}>])":
            depth -= 1
        if depth == 0 and path.startswith("::", i):
            parts.append(cur)
            cur = ""
            i += 2
            continue
        cur += ch
        i += 1
    parts.append(cur)
    return parts


def header_path(doc_first_line):
    """`/-- [a::b]: loop 0:` -> ("a::b", "loop 0"); bracket-matched (paths may hold `[T]`)."""
    s = doc_first_line
    j = s.find("[")
    if j < 0:
        return None, None
    depth, k = 0, j
    while k < len(s):
        if s[k] == "[":
            depth += 1
        elif s[k] == "]":
            depth -= 1
            if depth == 0:
                break
        k += 1
    if depth:
        return None, None
    return s[j + 1:k], s[k + 1:].strip().strip(":").strip()


def parse_aeneas(text):
    """The declarations of an Aeneas-emitted Lean file, with the Rust path each one models."""
    lines = text.splitlines()
    ns = None
    for line in lines:
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            ns = m.group(1)
            break
    decls, i = [], 0
    while i < len(lines):
        if not lines[i].startswith("/--"):
            i += 1
            continue
        start = i
        doc = [lines[i]]
        while "-/" not in lines[i] and i + 1 < len(lines):
            i += 1
            doc.append(lines[i])
        i += 1
        block = []
        while i < len(lines) and not lines[i].startswith("/--") and not re.match(r"^end\s", lines[i]):
            block.append(lines[i])
            i += 1
        decl = None
        for j, line in enumerate(block):
            m = DECL.match(line)
            if m:
                decl = (j, m.group(1), m.group(2))
                break
        if decl is None:
            continue
        j, keyword, name = decl
        attrs = " ".join(block[:j])
        body = "\n".join(block[j:])
        path, suffix = header_path(doc[0])
        decls.append(dict(path=path, suffix=suffix or "", lean=name, keyword=keyword,
                          attrs=attrs, body=body, line=start + 1, end=i,
                          partial_fixpoint=any(b.strip() == "partial_fixpoint" for b in block),
                          sorry=bool(re.search(r"\bsorry\b", body)),
                          reducible=bool(re.search(r"@\[[^\]]*\breducible\b", attrs))))
    return ns, decls


def strip_paths(s):
    return re.sub(r"(?:[A-Za-z_][A-Za-z0-9_]*::)+", "", s)


def norm_ty(s):
    return re.sub(r"[^a-z0-9]", "", strip_paths(s).lower())


def trait_tail(s):
    return re.sub(r"<.*$", "", strip_paths(s)).strip()


def aeneas_key(path):
    """Mapping key of an Aeneas header path (see rust_key)."""
    parts = split_path(path)
    if len(parts) >= 2:
        part = parts[-2]
        if part.startswith("{") and part.endswith("}"):
            inner, method = part[1:-1].strip(), parts[-1]
            m = re.match(r"^impl\s+(.+?)\s+for\s+(.+)$", inner)
            if m:
                return ("timpl", trait_tail(m.group(1)), norm_ty(m.group(2)), method)
            return ("inh", norm_ty(re.sub(r"^impl\s+", "", inner)), method)
    return ("path", path)


def rust_key(f, doc):
    if f["kind"] in ("free", "trait_default"):
        return ("path", "::".join(f["path"]))
    try:
        selfs = render_rust_type(f["self_ty"], doc)
    except ValueError:
        selfs = "?"
    if f["kind"] == "trait_impl":
        tname = f["trait_path"][-1] if f.get("trait_path") else trait_tail(f["trait"]["path"])
        return ("timpl", tname, norm_ty(selfs), f["name"])
    return ("inh", norm_ty(selfs), f["name"])


def map_functions(funcs, decls, doc):
    """Rust public function id -> (the Aeneas declaration modelling it | None, reason)."""
    main = [d for d in decls if d["path"] and not d["suffix"].startswith("loop")
            and d["keyword"] in ("def", "axiom", "opaque", "abbrev")]
    by_key = {}
    for d in main:
        by_key.setdefault(aeneas_key(d["path"]), []).append(d)
    out = {}
    for f in funcs:
        key = rust_key(f, doc)
        cands = by_key.get(key, [])
        if not cands and key[0] in ("timpl", "inh"):
            # Aeneas spells the Self type in full (`NonZero<u8, NonZeroU8Inner>` for the
            # alias `NonZeroU8`): accept a UNIQUE prefix match, never a guess between two.
            cands = [d for k, ds in by_key.items() for d in ds
                     if k[0] == key[0] and k[-1] == key[-1] and k[1:-2] == key[1:-2]
                     and k[-2].startswith(key[-2])]
        if len(cands) == 1:
            out[f["id"]] = (cands[0], None)
        elif not cands:
            out[f["id"]] = (None, "no Aeneas definition matches %s" % (key,))
        else:
            out[f["id"]] = (None, "ambiguous: %d Aeneas definitions match %s"
                                  % (len(cands), [c["lean"] for c in cands]))
    return out


# --------------------------------------------------------------------------- tool logs

def clean_log(text):
    return ANSI.sub("", (text or "").replace("\r", "\n"))


def parse_aeneas_log(text):
    """Aeneas' messages: error blocks, the error each untranslated function got, a crash."""
    text = clean_log(text)
    blocks, cur = [], None
    for line in text.splitlines():
        m = re.match(r"^\[(Error|Warn |Info )\]\s?(.*)$", line)
        if m:
            cur = {"level": m.group(1).strip(), "message": m.group(2).strip(), "lines": []}
            blocks.append(cur)
        elif cur is not None and line.strip():
            cur["lines"].append(line.strip())

    def field(b, name):
        for line in b["lines"]:
            if line.startswith(name + ":"):
                return line.split(":", 1)[1].strip().strip("'")
        return None
    errors = [{"message": b["message"], "source": field(b, "Source"), "pattern": field(b, "Name pattern")}
              for b in blocks if b["level"] == "Error"]
    body_errors = {}
    for b in blocks:
        m = re.match(r"Could not translate the \w+ of (?:the )?(?:function )?'?(.+?) because of previous error",
                     b["message"])
        if m:
            pattern = field(b, "Name pattern") or m.group(1).strip("'")
            source = field(b, "Source")
            msg = next((e["message"] for e in errors if e["source"] and e["source"] == source), None)
            body_errors[pattern] = msg or "unspecified previous error"
    for e in errors:
        if e["pattern"] and e["pattern"] not in body_errors:
            body_errors[e["pattern"]] = e["message"]
    crash = None
    if "Uncaught exception" in text:
        err = next((e["message"] for e in errors), None)
        exc = re.search(r"Uncaught exception:\s*\n\s*(\S.*)", text)
        crash = "%s (%s)" % (err or "internal error", exc.group(1).strip() if exc else "uncaught exception")
    return {"errors": errors, "body_errors": body_errors, "crash": crash}


def parse_charon_log(text):
    """Charon (rustc-style) errors, and the items they name (`Item `x` caused errors`)."""
    text = clean_log(text)
    errors, items, last = [], {}, None
    for line in text.splitlines():
        m = re.match(r"^error(?:\[\w+\])?:\s*(.*)$", line)
        if not m:
            continue
        msg = m.group(1).strip()
        im = re.search(r"`([^`]+)` caused errors", msg)
        if im:
            items[im.group(1)] = last or msg
        else:
            errors.append(msg)
            last = msg
    return {"errors": errors, "items": items}


def norm_message(msg, limit=120):
    msg = re.sub(r"\s+", " ", (msg or "").strip())
    msg = re.sub(r"'[^']*/[^']*'", "<path>", msg)
    return msg[:limit]


CATEGORY_RULES = [
    ("float", r"\bF(?:32|64)\b|\bf(?:32|64)\b|float|Improperly typed constant"),
    ("string", r"\bstr\b|String|\bStr\b|as_bytes|\bchar\b"),
    ("raw-pointer/unsafe", r"raw pointer|raw_pointer|unsafe|RawPtr"),
    ("trait", r"\btrait\b|dyn "),
    ("generic", r"generic|polymorph"),
    ("reference", r"borrow|reference|loan"),
    ("loop/recursion", r"\bloop\b|recurs|fixpoint"),
    ("internal-error", r"Internal error|Uncaught exception|file an issue"),
]


def categorize(labels_text, sig_hint=""):
    """A coarse category for a hole, for reading the ledger. The LABEL is the tool's words;
    this is only our grouping of them (message first, then the function's signature)."""
    for name, rx in CATEGORY_RULES:
        if re.search(rx, labels_text or ""):
            return name
    if "external-axiom" in (labels_text or ""):
        return "external-std"
    for name, rx in CATEGORY_RULES:
        if sig_hint and re.search(rx, sig_hint):
            return name
    return "other"


# --------------------------------------------------------------------------- axioms / ledger

def parse_print_axioms(text):
    """`#print axioms` output -> {decl: [axioms]} (lists may wrap over lines)."""
    out = {}
    flat = re.sub(r"\s+", " ", text or "")
    for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", flat):
        out[m.group(1)] = [x.strip() for x in (m.group(2) or "").split(",") if x.strip()]
    return out


def callee_closure(decls):
    names = {d["lean"] for d in decls}
    graph = {}
    for d in decls:
        toks = set(re.findall(r"[A-Za-z_][\w.']*", d["body"]))
        graph[d["lean"]] = {t for t in toks if t in names and t != d["lean"]}

    def closure(name):
        seen, todo = set(), [name]
        while todo:
            for c in graph.get(todo.pop(), ()):
                if c not in seen:
                    seen.add(c)
                    todo.append(c)
        return seen
    return closure


def fq_name(ns, lean):
    return (ns + "." + lean) if ns else lean


def classify(funcs, mapping, decls, ns, axioms, alog, clog, doc, global_failure=None):
    """Per public function: translated, or holes whose labels come from the tools."""
    by_lean = {d["lean"]: d for d in decls}
    by_fq = {fq_name(ns, d["lean"]): d for d in decls}
    closure = callee_closure(decls)
    result = {}
    for f in funcs:
        name = display_name(f, doc)
        d, why = mapping.get(f["id"], (None, "no Aeneas output"))
        sig_hint = json.dumps(f["sig"]) + (" unsafe" if f["header"].get("is_unsafe") else "")
        rec = {"rust": name, "kind": f["kind"], "lean": None, "holes": [], "detail": None}
        if global_failure:
            rec["holes"] = [global_failure]
            rec["detail"] = global_failure
        elif d is None:
            rust_path = "::".join(f.get("path") or []) or name
            charon_msg = next((m for item, m in clog["items"].items()
                               if item == rust_path or item.endswith("::" + f["name"])), None)
            rec["holes"] = ["charon:error:" + norm_message(charon_msg)] if charon_msg else ["aeneas:no-definition"]
            rec["detail"] = why
        elif d.get("rejected"):
            rec["holes"] = [d["rejected"]]
            rec["detail"] = "Lean rejected the Aeneas declaration %s (or one it needs)" % d["lean"]
        else:
            fq = fq_name(ns, d["lean"])
            rec["lean"] = fq
            labels = []
            if d["keyword"] in ("axiom", "opaque"):
                labels.append("aeneas:opaque:" + (d["path"] or d["lean"]))
            if d["sorry"]:
                labels.append("aeneas:error:" + norm_message(alog["body_errors"].get(d["path"])
                                                             or "sorry in the emitted body"))
            ax = axioms.get(fq)
            if ax is None and not labels:
                labels.append("lean:axioms-unreadable")
            for x in sorted(ax or []):
                if x in STANDARD_AXIOMS:
                    continue
                if x == "sorryAx":
                    if d["sorry"]:
                        continue
                    bad = sorted((by_lean[c]["path"] or c) for c in closure(d["lean"]) if by_lean[c]["sorry"])
                    labels += ["aeneas:calls-untranslated:" + b for b in bad] or ["aeneas:sorry"]
                    continue
                src = by_fq.get(x) or by_lean.get(x)
                labels.append("aeneas:external-axiom:" + ((src and src["path"]) or x))
            seen = []
            for lab in labels:
                if lab not in seen:
                    seen.append(lab)
            rec["holes"] = seen
        rec["status"] = "hole" if rec["holes"] else "translated"
        if rec["holes"]:
            rec["category"] = categorize(" ".join(rec["holes"]), sig_hint)
        result[f["id"]] = rec
    return result


def ledger_json(module, funcs, classes, decls_listing, provenance):
    labels = {}
    for f in funcs:
        for lab in classes[f["id"]]["holes"]:
            labels[lab] = labels.get(lab, 0) + 1
    hole_free = sum(1 for f in funcs if classes[f["id"]]["status"] == "translated")
    categories = {}
    for f in funcs:
        c = classes[f["id"]].get("category")
        if c:
            categories[c] = categories.get(c, 0) + 1
    return {
        "module": module,
        "dialect": "rust-aeneas",
        "producer": "scripts/rust_aeneas.py (rustdoc public API x Charon/Aeneas model x #print axioms)",
        "functions": len(funcs),
        "nodes": None,
        "holes": sum(labels.values()),
        "holeFree": hole_free,
        # A translated function's model is closed (#print axioms: no sorry, no non-standard
        # axiom), so hole-free and call-closed coincide on this path.
        "verifiableCore": hole_free,
        "closedByTranslation": hole_free,
        "closedByContract": 0,
        "contractsUsed": [],
        "dynamicHoleRisk": 0,
        "dynamicHoleRiskNote": "Aeneas `fail` is defined behaviour of the model, not a hole; "
                               "the Rust path has no runtime hole construct",
        "holesByLabel": [{"label": k, "count": v}
                         for k, v in sorted(labels.items(), key=lambda kv: (-kv[1], kv[0]))],
        "holeFunctionsByCategory": dict(sorted(categories.items())),
        "traitMethodDeclarations": decls_listing,
        "functionsDetail": [dict(classes[f["id"]], id=f["id"]) for f in funcs],
        "provenance": provenance,
    }


# --------------------------------------------------------------------------- oracle

def oracle_signature(f):
    """(arg types, return type) if the function can be called and compared exactly, else
    raises Unencodable with the reason."""
    if f["kind"] == "trait_default":
        raise Unencodable("provided trait method: generic over Self")
    if f["header"].get("is_unsafe"):
        raise Unencodable("unsafe fn: the harness does not call it on generated inputs")
    if f["header"].get("is_async"):
        raise Unencodable("async fn")
    params = (f.get("generics") or {}).get("params", []) + (f.get("impl_generics") or {}).get("params", [])
    for gen in params:
        if "lifetime" not in gen.get("kind", {}):
            raise Unencodable("generic parameter %s: no monomorphic instance is chosen" % gen.get("name"))
    self_ty = f.get("self_ty")
    args = [encode_type(t, self_ty, "arg") for _, t in f["sig"]["inputs"]]
    ret = encode_type(f["sig"].get("output"), self_ty, "ret")
    return args, ret


def rust_callee(f, doc):
    if f["kind"] == "free":
        return "::".join(f["path"])
    selfs = render_rust_type(f["self_ty"], doc)
    if f["kind"] == "trait_impl":
        trait = "::".join(f["trait_path"]) if f.get("trait_path") else f["trait"]["path"]
        return "<%s as %s>::%s" % (selfs, trait, f["name"])
    return "<%s>::%s" % (selfs, f["name"])


def harness_source(cases):
    """cases: [(callee, rust arg literals)]. One `{:?}` line per case, each panic caught."""
    arms = ["            %d => run(|| format!(\"{:?}\", %s(%s)))," % (i, callee, ", ".join(args))
            for i, (callee, args) in enumerate(cases)]
    return """#![allow(unused_parens, clippy::all)]
use std::io::Write;
fn run<F: FnOnce() -> String + std::panic::UnwindSafe>(f: F) -> String {
    match std::panic::catch_unwind(f) {
        Ok(s) => format!("ok {}", s),
        Err(_) => "panic".to_string(),
    }
}
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let start: usize = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(0);
    let out = std::io::stdout();
    for i in start..%d {
        let r = match i {
%s
            _ => unreachable!(),
        };
        let mut o = out.lock();
        writeln!(o, "{} {}", i, r).unwrap();
        o.flush().unwrap();
    }
}
""" % (len(cases), "\n".join(arms))


def run_harness(launch_for, n, per_case_timeout=10.0):
    """Run the harness from case 0, restarting after a timeout or an abort.
    -> ({i: "ok ..."|"panic"|None}, {i: note})"""
    results, notes, start = {}, {}, 0
    while start < n:
        proc = launch_for(start).popen(stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True,
                                       start_new_session=True)
        expected, stalled = start, False
        deadline = time.monotonic() + per_case_timeout
        while expected < n:
            left = deadline - time.monotonic()
            if left <= 0:
                stalled = True
                break
            ready, _, _ = select.select([proc.stdout], [], [], left)
            if not ready:
                continue
            line = proc.stdout.readline()
            if not line:
                break
            m = re.match(r"^(\d+) (.*)$", line.rstrip("\n"))
            if m and int(m.group(1)) == expected:
                results[expected] = m.group(2)
                expected += 1
                deadline = time.monotonic() + per_case_timeout
        try:
            os.killpg(proc.pid, 9)
        except (ProcessLookupError, PermissionError):
            proc.kill()
        rc = proc.wait()
        if expected < n:
            notes[expected] = ("native timeout (%.0f s)" % per_case_timeout) if stalled else \
                              ("native process ended (exit %s) before printing this case" % rc)
            results[expected] = None
            expected += 1
        start = expected
    return results, notes


def eval_source(module_import, cases):
    """cases: [(lean fq name, lean arg literals, lean printer lambda)] -> (source, first case line)."""
    lines = ["import %s" % module_import, "import AutoformRust.Eval",
             "open Aeneas Aeneas.Std", "set_option maxRecDepth 100000", "set_option maxErrors 100000"]
    first = len(lines) + 1
    for i, (fq, args, printer) in enumerate(cases):
        lines.append('#eval IO.println ("%d " ++ AutoformRust.rs %s (%s %s))' % (i, printer, fq, " ".join(args)))
    return "\n".join(lines) + "\n", first


def parse_lean_errors(text):
    """`file:line:col: error: msg` (with continuation lines) -> {line: msg}"""
    out, cur = {}, None
    for line in (text or "").splitlines():
        # `lean`: "file:L:C: error: msg"; `lake build`: "error: file:L:C: msg"
        m = re.match(r"^(?:.*?):(\d+):(\d+): (error|warning|info): (.*)$", line)
        m2 = None if m else re.match(r"^(error|warning|info): (?:[^:\s]+):(\d+):(\d+): (.*)$", line)
        if m or m2:
            cur = None
            kind, ln, msg = (m.group(3), int(m.group(1)), m.group(4)) if m else \
                            (m2.group(1), int(m2.group(2)), m2.group(4))
            if kind == "error":
                out.setdefault(ln, msg)
                cur = ln
        elif cur is not None and line.strip() and len(out[cur]) < 300:
            if re.match(r"^(\d+ (ok|fail|div)\b|error|warning|info|Some required|- |✖|⚠|'[^']+' (depends|does not))", line.strip()):
                cur = None
            else:
                out[cur] += " " + line.strip()
    return out


def compare(rust, lean):
    """-> ("agree"|"diverge"|"inconclusive", reason)"""
    if rust is None:
        return "inconclusive", "no native result"
    if lean is None:
        return "inconclusive", "no Lean result"
    if lean == "div":
        return "inconclusive", "Aeneas div (non-termination marker)"
    if rust == "panic":
        return ("agree", None) if lean.startswith("fail ") else ("diverge", None)
    if rust.startswith("ok "):
        return ("agree", None) if lean == rust else ("diverge", None)
    return "inconclusive", "unreadable native line %r" % rust


# --------------------------------------------------------------------------- theorems

STD_UNFOLD = ["Aeneas.Std.UScalar.saturating_add", "Aeneas.Std.UScalar.saturating_sub",
              "Aeneas.Std.IScalar.saturating_add", "Aeneas.Std.IScalar.saturating_sub"]
# Aeneas states integer bounds with `irreducible_def`, which the kernel cannot unfold; its
# own `_def` equations (theorems) put the closed form back.
STD_BOUNDS = ["Aeneas.Std.UScalar.max_def", "Aeneas.Std.IScalar.min_def", "Aeneas.Std.IScalar.max_def",
              "Aeneas.Std.UScalar.size_def", "Aeneas.Std.IScalar.size_def"]


def theorem_source(module_import, unfold, fuel, items, std_refs=()):
    """items: [(theorem name, lhs, rhs)]. Each is proved by unfolding the crate's definitions,
    rewriting `bind`/`loop` to their kernel-evaluable forms (theorems in AutoformRust.Eval),
    unfolding the std functions the model calls, and `rfl`. Every step but `rfl` is a `try`,
    so a step that does not apply cannot break another case. No native_decide, no axiom;
    `#print axioms` after each theorem is read back."""
    simp = ", ".join(list(unfold) + ["AutoformRust.loop_eq_loopK _ %d" % fuel,
                                     "AutoformRust.bind_eq_bindK", "AutoformRust.bindOp_eq_bindK"])
    steps = ["(try simp only [%s])" % simp]
    steps += ["(try unfold %s)" % r for r in std_refs]
    steps += ["(try simp only [%s])" % ", ".join(STD_UNFOLD), "(try simp only [%s])" % ", ".join(STD_BOUNDS), "rfl"]
    lines = ["import %s" % module_import, "import AutoformRust.Eval",
             "open Aeneas Aeneas.Std Result",
             "set_option maxHeartbeats 4000000", "set_option maxRecDepth 100000", "set_option maxErrors 100000",
             "set_option linter.unusedSimpArgs false", "set_option linter.unusedTactic false", "",
             "macro \"rust_case\" : tactic => `(tactic| (%s))" % " <;> ".join(steps), ""]
    spans = {}
    for name, lhs, rhs in items:
        start = len(lines) + 1
        lines.append("theorem %s : %s = %s := by" % (name, lhs, rhs))
        lines.append("  rust_case")
        spans[name] = (start, len(lines))
    lines.append("")
    for name, _, _ in items:
        lines.append("#print axioms %s" % name)
    return "\n".join(lines) + "\n", spans


def std_references(gen_text, decls):
    """`core.num.*` functions the model calls that the Aeneas library (not this file) defines."""
    local = {d["lean"] for d in decls}
    refs = set(re.findall(r"\bcore\.num\.[A-Za-z0-9_]+\.[A-Za-z0-9_]+\b", gen_text))
    return sorted(r for r in refs if r not in local)


def failure_class(msg, fn_decl_partial):
    """A readable class for an unproved case; the raw Lean message is kept beside it."""
    if fn_decl_partial:
        return "recursion: Aeneas partial_fixpoint is not evaluated by the kernel"
    if "loopK" in msg:
        return "loop did not finish within --fuel iterations (or a std loop inside it)"
    if "numBits" in msg or "Usize" in msg or "Isize" in msg or "usize" in msg or "isize" in msg:
        return "usize/isize: System.Platform.numBits is opaque to the kernel"
    if "deterministic timeout" in msg or "heartbeats" in msg:
        return "kernel/elaborator heartbeat limit"
    return "other: " + re.sub(r"\d+", "N", msg)[:100]


def lean_result_lit(ret_ty, rust_line, lean_line):
    """RHS of a case theorem: `ok <native value>`, or the Aeneas `fail <kind>` a panic agreed with."""
    if rust_line.startswith("ok "):
        return "(Aeneas.Std.Result.ok %s : Aeneas.Std.Result %s)" % (
            lean_lit(ret_ty, parse_debug(ret_ty, rust_line[3:])), lean_type(ret_ty))
    kind = lean_line.split(" ", 1)[1]
    if not re.fullmatch(r"\w+", kind):
        raise ValueError("bad fail kind %r" % kind)
    return "(Aeneas.Std.Result.fail .%s : Aeneas.Std.Result %s)" % (kind, lean_type(ret_ty))


def unfoldable(decls, ns):
    """Definitions the case tactic unfolds: the crate's own non-recursive, non-sorry defs.
    (`@[reducible]` ones unfold by themselves; partial_fixpoint ones cannot be unfolded.)"""
    return sorted({fq_name(ns, d["lean"]) for d in decls
                   if d["keyword"] == "def" and not d["partial_fixpoint"] and not d["reducible"] and not d.get("rejected")
                   and not d["sorry"] and d["path"] and not d["path"].startswith(("core::", "alloc::", "std::"))})


# --------------------------------------------------------------------------- provenance

def tree_digest(root, skip=("target", ".git")):
    h = hashlib.sha256()
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in skip)
        for name in sorted(filenames):
            p = os.path.join(dirpath, name)
            h.update(os.path.relpath(p, root).encode() + b"\0")
            with open(p, "rb") as fh:
                h.update(hashlib.sha256(fh.read()).digest())
    return h.hexdigest()


def provenance(env, toolchain, lp, crate_dir, meta, pins, llbc_version=None):
    def ver(cmd, **kw):
        x = run(cmd, timeout=120, **kw)
        return ((x.stdout or "") + (x.stderr or "")).strip()
    charon_v = ver([tool("charon", env), "version"], env=env)
    aeneas_v = ver([tool("aeneas", env), "-version"], env=env)
    rustc = ver(["rustc", "+" + toolchain, "-vV"], env=env).splitlines()
    manifest = {}
    try:
        manifest = {p["name"]: p.get("rev")
                    for p in json.load(open(os.path.join(lp, "lake-manifest.json")))["packages"]}
    except (OSError, ValueError, KeyError):
        pass
    found = {
        "aeneas": aeneas_v,
        "charon": charon_v,
        "charon_llbc_version": llbc_version,
        "aeneas_home": env.get("AENEAS_HOME"),
        "rust_toolchain": toolchain,
        "host_pointer_bits": HOST_BITS,
        "rustc": [l for l in rustc if l.startswith(("rustc ", "commit-hash", "host", "release"))],
        "cargo": ver(["cargo", "+" + toolchain, "-V"], env=env),
        "lean_project": lp,
        "lean_toolchain": open(os.path.join(lp, "lean-toolchain")).read().strip(),
        "lean": ver(["lake", "env", "lean", "--version"], cwd=lp, env=env),
        "lake": ver(["lake", "--version"], cwd=lp, env=env),
        "lake_manifest_revs": manifest,
        "crate": {"name": meta.get("name"), "version": meta.get("version"),
                  "source_tree_sha256": tree_digest(crate_dir)},
    }
    found["pins"] = {k: v for k, v in pins.items() if k not in ("comment", "assets")}
    found["matches_pins"] = {
        "aeneas": pins["aeneas_version"] in aeneas_v,
        "charon": pins["charon_version"] in charon_v and pins["charon_commit"] in charon_v,
        "rust_toolchain": toolchain == pins["rust_toolchain"],
        "lean_toolchain": found["lean_toolchain"] == pins["lean_toolchain"],
        "mathlib": manifest.get("mathlib") == pins.get("mathlib_rev"),
    }
    return found


# --------------------------------------------------------------------------- pipeline

def prune_until_builds(build, text, max_rounds=40):
    """Remove the declarations Lean rejects, and then whatever needed them, until the module
    builds. Nothing is replaced or invented: a rejected declaration is simply absent, and every
    public function it models (or that calls it) becomes a hole naming Lean's error.

    `build(text) -> (ok, output)`. Returns (text, {lean name: label}, rounds)."""
    rejected, rounds = {}, 0
    while True:
        ok, output = build(text)
        if ok:
            return text, rejected, rounds
        rounds += 1
        ns, decls = parse_aeneas(text)
        errs = parse_lean_errors(output)
        hit = {}
        for ln, msg in sorted(errs.items()):
            d = next((d for d in decls if d["line"] <= ln <= d["end"]), None)
            if d is None:
                raise RustPathError("lean-build-failed", "the Aeneas output does not build, and the "
                                    "error at line %d is outside any declaration: %s" % (ln, norm_message(msg, 300)))
            hit.setdefault(d["lean"], (d, msg))
        if not hit or rounds > max_rounds:
            raise RustPathError("lean-build-failed", "the Aeneas output does not build and pruning "
                                "made no progress: " + norm_message(output[-600:], 600))
        lines = text.splitlines()
        drop = set()
        for name, (d, msg) in sorted(hit.items(), key=lambda kv: kv[1][0]["line"]):
            # A declaration that uses one Lean already rejected fails BECAUSE of it (often with
            # a secondary message such as "sorryAx is not a matcher"): name the root cause.
            toks = set(re.findall(r"[A-Za-z_][\w.']*", d["body"]))
            root = next((r for r in rejected if r in toks or fq_name(ns, r) in toks), None)
            if root is None:
                m = re.search(r"Unknown (?:identifier|constant) `?'?([A-Za-z_][\w.']*)", msg)
                if m:
                    root = next((r for r in rejected if m.group(1) in (r, fq_name(ns, r))
                                 or m.group(1).endswith("." + r)), None)
            if root:
                cause = rejected[root][2]
                rejected[name] = ("lean:depends-on-rejected:" + cause, d["path"] or name, cause)
            else:
                cause = "%s: %s" % (d["path"] or name, norm_message(msg))
                rejected[name] = ("lean:rejected:" + cause, d["path"] or name, cause)
            drop.update(range(d["line"] - 1, d["end"]))
        text = "\n".join(l for k, l in enumerate(lines) if k not in drop) + "\n"


LAKE_LIB = ("\n-- autoform: Rust path modules (scripts/rust_aeneas.py)\n"
            "lean_lib «AutoformRust» where\n  globs := #[.andSubmodules `AutoformRust]\n")


def ensure_lean_project(lp):
    if not os.path.isdir(lp) or not os.path.isfile(os.path.join(lp, "lakefile.lean")):
        raise RustPathError("lean-project-missing", "no scratch Aeneas Lake project at %s" % lp,
                            "create it with: bash scripts/rust_setup.sh \"$AENEAS_HOME\" %s" % lp)
    if not os.path.isdir(os.path.join(lp, ".lake", "build", "lib", "lean", "Aeneas")):
        raise RustPathError("lean-project-unbuilt", "the Aeneas Lean library is not built in %s" % lp,
                            "run: (cd %s && lake exe cache get && lake build Aeneas)" % lp)
    lake_file = os.path.join(lp, "lakefile.lean")
    if "lean_lib «AutoformRust»" not in open(lake_file).read():
        with open(lake_file, "a") as fh:
            fh.write(LAKE_LIB)
    os.makedirs(os.path.join(lp, "AutoformRust"), exist_ok=True)
    helper = open(os.path.join(HERE, "rust_eval.lean.tmpl")).read()
    dest = os.path.join(lp, "AutoformRust", "Eval.lean")
    if not os.path.exists(dest) or open(dest).read() != helper:
        with open(dest, "w") as fh:
            fh.write(helper)


def cargo_metadata(crate, env, toolchain):
    r = run(["cargo", "+" + toolchain, "metadata", "--no-deps", "--format-version", "1",
             "--manifest-path", os.path.join(crate, "Cargo.toml")], env=env, timeout=300)
    if r.returncode:
        raise RustPathError("cargo-metadata-failed", "cargo metadata failed: " + first_line(r.stderr))
    data = json.loads(r.stdout)
    want = os.path.realpath(os.path.join(crate, "Cargo.toml"))
    pkg = next((p for p in data["packages"] if os.path.realpath(p["manifest_path"]) == want), None)
    if pkg is None:
        raise RustPathError("not-a-package", "%s is a workspace root, not a package; pass the "
                            "member crate directory" % crate)
    lib = next((t for t in pkg["targets"] if "lib" in t["kind"] or "rlib" in t["kind"]), None)
    if lib is None:
        raise RustPathError("not-a-library", "crate %s has no library target; the Rust path "
                            "models a library's public functions" % pkg["name"])
    return {"name": pkg["name"], "version": pkg["version"], "lib": lib["name"].replace("-", "_"),
            "edition": pkg.get("edition")}


def boxed(cmd, work, env, writable=(), cwd=None):
    import sandbox
    try:
        return sandbox.sandboxed(cmd, cwd=cwd, env=env, work=work, writable=list(writable))
    except sandbox.SandboxUnavailable as exc:
        raise RustPathError("sandbox-unavailable", str(exc),
                            "install the sandbox (docs/trust-model.md) or set AUTOFORM_SANDBOX=off, "
                            "which every artifact then records") from None


def default_module(lib):
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[_\-]", lib) if p)


def main(argv=None):
    ap = argparse.ArgumentParser(description="Rust path: Charon + Aeneas model, ledger, oracle, case theorems")
    ap.add_argument("--crate", required=True)
    ap.add_argument("--module", default=None, help="Lean module name (default: from the crate's lib name)")
    ap.add_argument("--lean-project", default=os.environ.get("AUTOFORM_RUST_LEAN_PROJECT"))
    ap.add_argument("--out", default=".")
    ap.add_argument("--profile", choices=["debug", "release"], default="debug")
    ap.add_argument("--seed", type=int, default=20261010)
    ap.add_argument("--cases", type=int, default=60, help="boundary-product cases per function (default 60)")
    ap.add_argument("--random", type=int, default=40, help="random cases per function (default 40)")
    ap.add_argument("--theorems-per-function", type=int, default=12)
    ap.add_argument("--fuel", type=int, default=4096, help="loop iterations the kernel unrolls (default 4096)")
    ap.add_argument("--assure", action="store_true", help="also write run.json/guarantee.json; exit 1 on any gap")
    ap.add_argument("--keep-work", action="store_true")
    a = ap.parse_args(argv)
    out = os.path.abspath(a.out)
    os.makedirs(out, exist_ok=True)
    # Never leave a previous run's verdict where this run's would be read.
    stale = os.path.join(out, "rust-error.json")
    for name in os.listdir(out):
        if name in ("rust-error.json", "conformance.json", "summary.md", "run.json", "guarantee.json",
                    "rust-provenance.json", "rust-theorems.json", "charon.log", "aeneas.log") or \
                re.fullmatch(r"(ledger-.*\.json|aeneas-.*\.lean|rust-cases-.*\.lean)", name):
            os.remove(os.path.join(out, name))
    try:
        return pipeline(a, out)
    except RustPathError as exc:
        rec = exc.record()
        with open(stale, "w") as fh:
            json.dump(rec, fh, indent=1)
        print("rust_aeneas: %s: %s" % (exc.name, exc.message), file=sys.stderr)
        if exc.hint:
            print("  hint: " + exc.hint, file=sys.stderr)
        if a.assure:
            write_assure(out, a.module or "?", None, None, None, failure=rec)
        return 2


def pipeline(a, out):
    pins = load_pins()
    env = dict(os.environ)
    if env.get("AENEAS_HOME"):
        env["PATH"] = env["AENEAS_HOME"] + os.pathsep + env.get("PATH", "")
    gone = missing(env)
    if gone:
        raise RustPathError("tool-missing", "missing prerequisites: %s" % ", ".join(gone),
                            "see `autoform doctor`; charon and aeneas come from the pinned Aeneas "
                            "release %s (set AENEAS_HOME to its unpacked directory)" % pins["aeneas_release"])
    toolchain = pinned_rust_toolchain(env, pins)
    if run(["rustc", "+" + toolchain, "-V"], env=env, timeout=120).returncode:
        raise RustPathError("rust-toolchain-missing", "rust toolchain %s is not installed" % toolchain,
                            "rustup toolchain install %s --profile minimal -c rustc-dev -c llvm-tools -c rust-src"
                            % toolchain)
    if not a.lean_project:
        raise RustPathError("lean-project-missing", "no scratch Aeneas Lake project given",
                            "pass --lean-project or set AUTOFORM_RUST_LEAN_PROJECT; create one with "
                            "bash scripts/rust_setup.sh \"$AENEAS_HOME\" <dir>")
    lp = os.path.abspath(a.lean_project)
    ensure_lean_project(lp)
    crate_src = os.path.abspath(a.crate)
    if not os.path.isfile(os.path.join(crate_src, "Cargo.toml")):
        raise RustPathError("not-a-crate", "%s has no Cargo.toml" % crate_src)
    meta = cargo_metadata(crate_src, env, toolchain)
    module = a.module or default_module(meta["lib"])
    if not re.fullmatch(r"[A-Z][A-Za-z0-9_]*", module) or module == "Eval" or module.endswith("Cases"):
        raise RustPathError("bad-module", "module %r must be a Lean identifier beginning with an "
                            "uppercase letter, not `Eval` and not ending in `Cases`" % module)
    import fcntl
    lock = open(os.path.join(lp, ".autoform-rust.lock"), "w")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        lock.close()
        raise RustPathError("lean-project-busy", "another Rust run holds %s" % lp) from None
    work = os.path.realpath(tempfile.mkdtemp(prefix="rust_aeneas_"))
    try:
        return run_stages(a, out, pins, env, toolchain, lp, crate_src, meta, module, work)
    finally:
        lock.close()
        if not a.keep_work:
            shutil.rmtree(work, ignore_errors=True)


def run_stages(a, out, pins, env, toolchain, lp, crate_src, meta, module, work):
    t0, stages = time.time(), {}
    crate = os.path.join(work, "crate")
    shutil.copytree(crate_src, crate, ignore=shutil.ignore_patterns("target", ".git"))
    cenv = dict(env, RUSTUP_TOOLCHAIN=toolchain, CARGO_TARGET_DIR=os.path.join(work, "target"))
    cargo_home = os.path.realpath(env.get("CARGO_HOME") or os.path.join(os.path.expanduser("~"), ".cargo"))
    # Network first and outside the sandbox: fetching runs no crate code. Every later step
    # that compiles (build scripts, proc macros) or runs the crate is sandboxed and offline.
    r = run(["cargo", "fetch", "--manifest-path", os.path.join(crate, "Cargo.toml")], env=cenv, timeout=900)
    if r.returncode:
        raise RustPathError("cargo-fetch-failed", "cargo fetch failed: " + first_line(r.stderr))
    stages["fetch"] = {"status": "ok"}
    offline = dict(cenv, CARGO_NET_OFFLINE="true")
    writable = [cargo_home, work]

    # 1. the public API, from rustdoc
    launch = boxed(["cargo", "rustdoc", "-q", "--lib", "--", "-Z", "unstable-options",
                    "--output-format", "json"], work, offline, writable, cwd=crate)
    r = launch.run(capture_output=True, text=True, timeout=1800)
    build_sandbox = launch.record
    doc_path = os.path.join(work, "target", "doc", meta["lib"] + ".json")
    if r.returncode or not os.path.exists(doc_path):
        raise RustPathError("rustdoc-failed", "cargo rustdoc --output-format json failed: "
                            + "\n".join(clean_log(r.stderr).strip().splitlines()[-5:]))
    doc = json.load(open(doc_path))
    funcs, decl_listing = public_functions(doc)
    stages["rustdoc"] = {"status": "ok", "functions": len(funcs), "format_version": doc.get("format_version")}

    # 2. Charon -> LLBC, Aeneas -> Lean
    llbc = os.path.join(work, meta["lib"] + ".llbc")
    launch = boxed([tool("charon", env), "cargo", "--preset=aeneas", "--dest-file", llbc],
                   work, offline, writable, cwd=crate)
    r = launch.run(capture_output=True, text=True, timeout=3600)
    charon_log = (r.stdout or "") + (r.stderr or "")
    with open(os.path.join(out, "charon.log"), "w") as fh:
        fh.write(clean_log(charon_log))
    clog = parse_charon_log(charon_log)
    global_failure, llbc_version = None, None
    if r.returncode or not os.path.exists(llbc):
        msg = clog["errors"][0] if clog["errors"] else first_line(r.stderr) or "exit %d" % r.returncode
        global_failure = "charon:failed:" + norm_message(msg)
        stages["charon"] = {"status": "failed", "detail": msg}
    else:
        stages["charon"] = {"status": "ok", "errors": len(clog["errors"])}
        with open(llbc) as fh:
            m = re.search(r'"charon_version"\s*:\s*"([^"]+)"', fh.read(400))
        llbc_version = m.group(1) if m else None
    leandir = os.path.join(work, "lean")
    os.makedirs(leandir)
    gen_text, ns, decls, alog = "", None, [], parse_aeneas_log("")
    if not global_failure:
        r = run([tool("aeneas", env), "-backend", "lean", llbc, "-dest", leandir], env=env, timeout=3600)
        alog_text = (r.stdout or "") + (r.stderr or "")
        with open(os.path.join(out, "aeneas.log"), "w") as fh:
            fh.write(clean_log(alog_text))
        alog = parse_aeneas_log(alog_text)
        produced = sorted(n for n in os.listdir(leandir) if n.endswith(".lean"))
        if alog["crash"] or not produced:
            global_failure = "aeneas:crash:" + norm_message(alog["crash"] or first_line(clean_log(alog_text)) or "no output")
            stages["aeneas"] = {"status": "failed", "detail": alog["crash"]}
        elif len(produced) != 1:
            raise RustPathError("aeneas-split-output", "Aeneas produced %d Lean files; expected one" % len(produced))
        else:
            gen_text = open(os.path.join(leandir, produced[0])).read()
            ns, decls = parse_aeneas(gen_text)
            stages["aeneas"] = {"status": "ok" if r.returncode == 0 else "partial (exit %d)" % r.returncode,
                                "errors": len(alog["errors"]), "declarations": len(decls)}

    # 3. build the model in the scratch project; read every mapped function's axioms
    axioms, mod_import = {}, "AutoformRust." + module
    mapping = map_functions(funcs, decls, doc) if decls else {}
    rejected = {}
    if not global_failure:
        dest = os.path.join(lp, "AutoformRust", module + ".lean")
        shutil.copy(os.path.join(leandir, produced[0]), os.path.join(out, "aeneas-%s.lean" % module))

        def build(text):
            with open(dest, "w") as fh:
                fh.write(text)
            r = run(["lake", "build", "AutoformRust.Eval", mod_import], cwd=lp, env=env, timeout=7200)
            return r.returncode == 0, (r.stdout or "") + (r.stderr or "")
        built, rejected, rounds = prune_until_builds(build, gen_text)
        stages["lean_build"] = {"status": "ok" if not rejected else "ok after removing %d rejected declarations"
                                % len(rejected), "rounds": rounds,
                                "rejected": {k: v[0] for k, v in sorted(rejected.items())}}
        if rejected:
            with open(os.path.join(out, "aeneas-%s.built.lean" % module), "w") as fh:
                fh.write(built)
        fqs = sorted({fq_name(ns, d["lean"]) for d, _ in mapping.values()
                      if d is not None and d["lean"] not in rejected})
        audit = os.path.join(lp, ".autoform-rust-%s-axioms.lean" % module)
        with open(audit, "w") as fh:
            fh.write("import %s\n" % mod_import + "".join("#print axioms %s\n" % q for q in fqs))
        r = run(["lake", "env", "lean", audit], cwd=lp, env=env, timeout=1800)
        axioms = parse_print_axioms(r.stdout)
        stages["axioms"] = {"status": "ok" if len(axioms) == len(fqs) else "partial",
                            "read": len(axioms), "asked": len(fqs)}
        decls = [d for d in decls if d["lean"] not in rejected] + \
                [dict(d, rejected=rejected[d["lean"]][0]) for d in decls if d["lean"] in rejected]
        mapping = map_functions(funcs, decls, doc)
    classes = classify(funcs, mapping, decls, ns, axioms, alog, clog, doc, global_failure)

    # 4. differential oracle on every translated function the harness can encode exactly
    rng = random.Random(a.seed)
    plan, oracle = [], {}
    for f in funcs:
        if classes[f["id"]]["status"] != "translated":
            continue
        try:
            arg_tys, ret_ty = oracle_signature(f)
            callee = rust_callee(f, doc)
        except (Unencodable, ValueError) as exc:
            oracle[f["id"]] = {"status": "inconclusive", "reason": str(exc)}
            continue
        cs = cases_for(arg_tys, rng, cap=a.cases, nrand=a.random)
        oracle[f["id"]] = {"status": "planned", "cases": len(cs), "agree": 0, "diverge": 0, "inconclusive": 0}
        plan += [(f, arg_tys, ret_ty, callee, v) for v in cs]
    rust_res, rust_notes, lean_res, lean_notes, harness_sandbox = {}, {}, {}, {}, None
    if plan:
        hdir = os.path.join(work, "harness")
        os.makedirs(os.path.join(hdir, "src"))
        prof = ("[profile.dev]\nopt-level = 0\ndebug-assertions = true\noverflow-checks = true\n"
                "[profile.release]\nopt-level = 3\ndebug-assertions = false\noverflow-checks = false\n")
        with open(os.path.join(hdir, "Cargo.toml"), "w") as fh:
            fh.write('[package]\nname = "autoform_rust_harness"\nversion = "0.0.0"\nedition = "2021"\n'
                     '[dependencies]\n%s = { path = %s }\n%s[workspace]\n'
                     % (json.dumps(meta["name"]), json.dumps(crate), prof))
        with open(os.path.join(hdir, "src", "main.rs"), "w") as fh:
            fh.write(harness_source([(callee, [rust_lit(t, x) for t, x in zip(arg_tys, v)])
                                     for _, arg_tys, _, callee, v in plan]))
        henv = dict(offline, CARGO_TARGET_DIR=os.path.join(hdir, "target"))
        launch = boxed(["cargo", "build", "-q"] + (["--release"] if a.profile == "release" else []),
                       work, henv, writable, cwd=hdir)
        r = launch.run(capture_output=True, text=True, timeout=3600)
        if r.returncode:
            raise RustPathError("harness-build-failed", "the cargo harness did not build:\n"
                                + clean_log(r.stderr)[-3000:])
        exe = os.path.join(hdir, "target", "release" if a.profile == "release" else "debug",
                           "autoform_rust_harness")

        def launch_for(start):
            return boxed([exe, str(start)], os.path.join(work, "run"), env, (), cwd=hdir)
        rust_res, rust_notes = run_harness(launch_for, len(plan))
        harness_sandbox = launch_for(0).record
        lcases = [(classes[f["id"]]["lean"], [lean_lit(t, x) for t, x in zip(arg_tys, v)],
                   "(fun (v : %s) => %s)" % (lean_type(ret_ty), lean_show(ret_ty, "v")))
                  for f, arg_tys, ret_ty, _, v in plan]
        lean_res, lean_notes = eval_cases(lp, env, mod_import, lcases, plan)

    agree = div = inconc = 0
    detail, inconclusive_detail, per_case = [], {}, []
    for i, (f, arg_tys, ret_ty, callee, v) in enumerate(plan):
        rv, lv = rust_res.get(i), lean_res.get(i)
        verdict, why = compare(rv, lv)
        if verdict == "inconclusive":
            why = rust_notes.get(i) or lean_notes.get(i) or why
        o = oracle[f["id"]]
        if verdict == "agree":
            agree += 1
            o["agree"] += 1
        elif verdict == "diverge":
            div += 1
            o["diverge"] += 1
            detail.append({"function": classes[f["id"]]["rust"],
                           "args": [rust_lit(t, x) for t, x in zip(arg_tys, v)], "rust": rv, "aeneas": lv})
        else:
            inconc += 1
            o["inconclusive"] += 1
            inconclusive_detail[why] = inconclusive_detail.get(why, 0) + 1
        per_case.append((i, verdict))
    for o in oracle.values():
        if o["status"] == "planned":
            if o["agree"] + o["diverge"]:
                o["status"] = "compared"
            else:
                o["status"], o["reason"] = "inconclusive", "no case was adjudicated"

    # 5. kernel-checked case theorems for every compared function
    partial = reaches_partial_fixpoint(decls, ns)
    theorems = prove_cases(a, lp, env, mod_import, module, unfoldable(decls, ns), plan,
                           rust_res, lean_res, per_case, classes, out,
                           std_refs=std_references(gen_text, decls), partial=partial)

    # 6. artifacts
    prov = provenance(env, toolchain, lp, crate_src, meta, pins, llbc_version)
    prov["sandbox"] = {"build": build_sandbox, "harness": harness_sandbox}
    with open(os.path.join(out, "rust-provenance.json"), "w") as fh:
        json.dump(prov, fh, indent=1)
    led = ledger_json(module, funcs, classes, decl_listing,
                      {k: prov[k] for k in ("aeneas", "charon", "rust_toolchain", "lean_toolchain", "crate")})
    for fd in led["functionsDetail"]:
        fd["oracle"] = oracle.get(fd["id"], {"status": "not run", "reason": "not translated (hole)"})
        fd["theorems"] = theorems["by_function"].get(fd["id"])
    with open(os.path.join(out, "ledger-%s.json" % module), "w") as fh:
        json.dump(led, fh, indent=1)
    compared = [fid for fid, o in oracle.items() if o["status"] == "compared"]
    inconclusive_functions = {classes[fid]["rust"]: o.get("reason") for fid, o in oracle.items()
                              if o["status"] == "inconclusive"}
    conformance = {
        "language": "rust", "module": module, "crate": meta["name"], "crate_version": meta["version"],
        "oracle": "native Rust (cargo harness, %s profile) vs Aeneas Lean #eval" % a.profile,
        "profile": a.profile, "seed": a.seed,
        "agree": agree, "total": agree + div, "divergences": div, "inconclusive": inconc,
        "rate": ("%d/%d" % (agree, agree + div)) if agree + div else "n/a",
        "cases": len(plan),
        "functions_total": len(funcs), "functions_hole_free": led["holeFree"],
        "functions_covered": len(compared),
        "coverage": {"population": len(funcs), "population_kind": "public functions (rustdoc)",
                     "hole_free": led["holeFree"], "compared": len(compared), "covered_metric": "compared"},
        "inconclusive_functions": inconclusive_functions,
        "inconclusive_cases_by_reason": inconclusive_detail,
        "divergence_detail": detail,
        "kernel_checked": {k: v for k, v in theorems.items() if k != "by_function"},
        "assumptions": [
            "debug profile: overflow checks and debug assertions on (what Aeneas models); "
            "release wraps and is expected to diverge on overflowing arithmetic",
            "Rust panic <-> Aeneas `fail` of any kind (the kind is stated in the case theorem, "
            "not compared with the panic)",
            "Aeneas `div` is inconclusive, never agreement",
            "usize/isize are 64-bit (the harness host)",
            "encoded values: integers, bool, tuples and fixed-size arrays of them, and shared "
            "references to them as arguments; anything else is inconclusive with a reason",
            "inputs: boundary-value product (cap %d) plus %d seeded random per function" % (a.cases, a.random)],
        "stages": stages,
        "provenance": prov,
        "wall_clock_seconds": round(time.time() - t0, 1),
    }
    with open(os.path.join(out, "conformance.json"), "w") as fh:
        json.dump(conformance, fh, indent=1)
    write_summary(out, module, meta, led, conformance)
    if a.assure:
        write_assure(out, module, led, conformance, theorems)
    for d in detail[:10]:
        print("DIVERGENCE %s(%s): rust=%s aeneas=%s" % (d["function"], ", ".join(d["args"]), d["rust"], d["aeneas"]))
    kc = conformance["kernel_checked"]
    print("rust_aeneas [%s, %s %s]: %d public functions, %d translated, %d hole occurrences under %d labels; "
          "%d compared, %d/%d cases agree, %d divergences, %d inconclusive cases, %d translated functions "
          "inconclusive; %d/%d case theorems proved"
          % (a.profile, meta["name"], meta["version"], len(funcs), led["holeFree"], led["holes"],
             len(led["holesByLabel"]), len(compared), agree, agree + div, div, inconc,
             len(inconclusive_functions), kc["proved"], kc["emitted"]))
    if div:
        return 1
    if a.assure and (led["holes"] or inconc or inconclusive_functions or kc["proved"] < kc["emitted"]):
        return 1
    return 0


def eval_cases(lp, env, mod_import, lcases, plan, timeout=1800):
    src, first = eval_source(mod_import, lcases)
    path = os.path.join(lp, ".autoform-rust-eval.lean")
    with open(path, "w") as fh:
        fh.write(src)
    r = run(["lake", "env", "lean", path], cwd=lp, env=env, timeout=timeout)
    if r.returncode != 124:
        return _read_eval(r, first, len(lcases))
    # One #eval hung (a loop the model does not leave): isolate it, one file per function.
    res, notes, by_fn = {}, {}, {}
    for i, (f, *_rest) in enumerate(plan):
        by_fn.setdefault(f["id"], []).append(i)
    for idx in by_fn.values():
        s, fl = eval_source(mod_import, [lcases[i] for i in idx])
        with open(path, "w") as fh:
            fh.write(s)
        rr = run(["lake", "env", "lean", path], cwd=lp, env=env, timeout=600)
        got, got_notes = _read_eval(rr, fl, len(idx))
        for k, i in enumerate(idx):
            if k in got:
                res[i] = got[k]
            else:
                notes[i] = got_notes.get(k) or ("lean #eval timeout" if rr.returncode == 124 else "no Lean output")
    return res, notes


def _read_eval(r, first, n):
    res, notes = {}, {}
    for line in (r.stdout or "").splitlines():
        m = re.match(r"^(\d+) (ok .*|fail \w+|div)$", line)
        if m:
            res[int(m.group(1))] = m.group(2)
    errs = parse_lean_errors((r.stdout or "") + "\n" + (r.stderr or ""))
    header = next((m for ln, m in sorted(errs.items()) if ln < first), None)
    for ln, msg in errs.items():
        k = ln - first
        if 0 <= k < n and k not in res:
            notes[k] = "lean error: " + norm_message(msg, 200)
    for k in range(n):
        if k not in res and k not in notes:
            notes[k] = ("lean error before the cases: " + norm_message(header, 200)) if header else \
                       ("lean #eval timeout" if r.returncode == 124 else "no Lean output (exit %s)" % r.returncode)
    return res, notes


def reaches_partial_fixpoint(decls, ns):
    """fq names of the declarations whose model reaches a partial_fixpoint (recursion)."""
    closure = callee_closure(decls)
    by_lean = {d["lean"]: d for d in decls}
    out = set()
    for d in decls:
        reach = {d["lean"]} | closure(d["lean"])
        if any(by_lean[c]["partial_fixpoint"] for c in reach):
            out.add(fq_name(ns, d["lean"]))
    return out


def prove_cases(a, lp, env, mod_import, module, unfold, plan, rust_res, lean_res, per_case, classes, out,
                std_refs=(), partial=frozenset()):
    items, owner, budget = [], {}, {}
    for i, verdict in per_case:
        if verdict != "agree":
            continue
        f, arg_tys, ret_ty, _, v = plan[i]
        if budget.get(f["id"], 0) >= a.theorems_per_function:
            continue
        try:
            rhs = lean_result_lit(ret_ty, rust_res[i], lean_res[i])
        except ValueError:
            continue
        budget[f["id"]] = budget.get(f["id"], 0) + 1
        name = "case_%d" % i
        lhs = ("%s %s" % (classes[f["id"]]["lean"], " ".join(lean_lit(t, x) for t, x in zip(arg_tys, v)))).strip()
        items.append((name, lhs, rhs))
        owner[name] = f["id"]
    result = {"emitted": len(items), "proved": 0, "failed": 0, "fuel": a.fuel,
              "per_function_cap": a.theorems_per_function, "failure_reasons": {},
              "file": "rust-cases-%s.lean" % module, "by_function": {}}
    if not items:
        return result
    src, spans = theorem_source(mod_import, unfold, a.fuel, items, std_refs)
    path = os.path.join(lp, "AutoformRust", module + "Cases.lean")
    with open(path, "w") as fh:
        fh.write(src)
    shutil.copy(path, os.path.join(out, result["file"]))
    r = run(["lake", "env", "lean", path], cwd=lp, env=env, timeout=7200)
    errs = parse_lean_errors((r.stdout or "") + "\n" + (r.stderr or ""))
    ax = parse_print_axioms(r.stdout)
    statuses = {}
    for name, (lo, hi) in spans.items():
        bad = [m for ln, m in errs.items() if lo <= ln <= hi]
        axs = ax.get(name)
        if bad:
            statuses[name] = (False, norm_message(bad[0], 160))
        elif r.returncode == 124 and axs is None:
            statuses[name] = (False, "lean timeout")
        elif axs is None:
            statuses[name] = (False, "no #print axioms output")
        elif set(axs) - STANDARD_AXIOMS:
            statuses[name] = (False, "depends on " + ", ".join(sorted(set(axs) - STANDARD_AXIOMS)))
        else:
            statuses[name] = (True, None)
    for name, (ok, why) in statuses.items():
        bf = result["by_function"].setdefault(owner[name], {"emitted": 0, "proved": 0, "failed": []})
        bf["emitted"] += 1
        if ok:
            result["proved"] += 1
            bf["proved"] += 1
        else:
            result["failed"] += 1
            key = failure_class(why, classes[owner[name]]["lean"] in partial)
            result["failure_reasons"][key] = result["failure_reasons"].get(key, 0) + 1
            if len(bf["failed"]) < 3:
                bf["failed"].append({"theorem": name, "reason": why,
                                     "class": failure_class(why, classes[owner[name]]["lean"] in partial)})
    with open(os.path.join(out, "rust-theorems.json"), "w") as fh:
        json.dump({n: {"proved": s[0], "reason": s[1], "function": classes[owner[n]]["rust"],
                       "class": None if s[0] else failure_class(s[1], classes[owner[n]]["lean"] in partial)}
                   for n, s in statuses.items()}, fh, indent=1)
    return result


def write_summary(out, module, meta, led, conf):
    kc = conf["kernel_checked"]
    lines = ["# Rust path: %s %s (module %s)" % (meta["name"], meta["version"], module), "",
             "| | |", "|---|---|",
             "| public functions (rustdoc) | %d |" % led["functions"],
             "| translated (closed Aeneas model) | %d |" % led["holeFree"],
             "| hole occurrences | %d under %d labels |" % (led["holes"], len(led["holesByLabel"])),
             "| compared by the oracle | %d |" % conf["functions_covered"],
             "| cases agree | %d/%d |" % (conf["agree"], conf["total"]),
             "| divergences | %d |" % conf["divergences"],
             "| inconclusive cases | %d |" % conf["inconclusive"],
             "| translated functions inconclusive | %d |" % len(conf["inconclusive_functions"]),
             "| case theorems proved by the kernel | %d/%d |" % (kc["proved"], kc["emitted"]), "",
             "## Holes by label", ""]
    lines += ["* `%s` x %d" % (h["label"], h["count"]) for h in led["holesByLabel"]] or ["none"]
    lines += ["", "## Inconclusive functions", ""]
    lines += ["* `%s`: %s" % kv for kv in sorted(conf["inconclusive_functions"].items())] or ["none"]
    lines += ["", "## Unproved case theorems", ""]
    lines += ["* %s x %d" % kv for kv in sorted(kc.get("failure_reasons", {}).items())] or ["none"]
    lines += ["", "## Divergences", ""]
    lines += ["* `%s(%s)`: rust=%s aeneas=%s" % (d["function"], ", ".join(d["args"]), d["rust"], d["aeneas"])
              for d in conf["divergence_detail"][:50]] or ["none"]
    lines += ["", "Assumptions: " + "; ".join(conf["assumptions"]), ""]
    with open(os.path.join(out, "summary.md"), "w") as fh:
        fh.write("\n".join(lines))


def write_assure(out, module, led, conf, theorems, failure=None):
    if failure:
        run_json = dict(module=module, language="rust", execution_status="failed",
                        verification_complete=False, error=failure)
        guarantee = dict(status="unverified", whole_program_correctness=False, claims=[],
                         reason="Rust path failed: %s" % failure["error"])
    else:
        gaps = {"holes": led["holes"], "divergences": conf["divergences"],
                "inconclusive_cases": conf["inconclusive"],
                "inconclusive_functions": len(conf["inconclusive_functions"]),
                "unproved_case_theorems": theorems["emitted"] - theorems["proved"]}
        complete = not any(gaps.values())
        run_json = dict(module=module, language="rust", execution_status="completed",
                        verification_complete=complete, gaps=gaps)
        guarantee = dict(
            status="verified-cases" if complete else "unverified",
            whole_program_correctness=False,
            claims=[{"kind": "kernel-checked case", "count": theorems["proved"],
                     "statement": "the Aeneas model returns, on the recorded input, what the native "
                                  "Rust function returned (debug profile)"},
                    {"kind": "differential agreement (TEST)", "count": conf["agree"], "of": conf["total"]}],
            reason="Rust faithfulness is tested on sampled inputs and proved only per recorded case; "
                   "no theorem here quantifies over all inputs.")
    with open(os.path.join(out, "run.json"), "w") as fh:
        json.dump(run_json, fh, indent=1)
    with open(os.path.join(out, "guarantee.json"), "w") as fh:
        json.dump(guarantee, fh, indent=1)


if __name__ == "__main__":
    sys.exit(main())
