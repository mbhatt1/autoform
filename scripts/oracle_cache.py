"""Per-function result cache for the differential oracle (`scripts/differential.py`).

A one-function change used to cost a full run: every recorded case of every function
went back through the Lean interpreter. The expensive part of the oracle is exactly that
evaluation, and most of it answers a question whose inputs have not moved. This module
decides, per function, whether the previous answer is still about the same question.

A cached verdict is reused only when EVERYTHING the verdict depends on is byte-identical:

* the function's own AST record (its translation),
* the AST records of every function it can reach -- by name (`fnref`, `callV`, `mcall`
  targets, class mentions) or by dispatch (methods of its own class and base classes, and
  of every class whose objects appear in its cases), closed transitively,
* the module-level records (`<module>` bodies run as initializers; they also carry the
  class declarations), which every function's evaluation starts from,
* the semantics (`Autoform/Lang/Core/**.lean`), the renderer (`cartographer/*.py`),
  this harness, and the Lean toolchain,
* the real runtime's version,
* the case set: the exact (receiver, arguments, outcome, post-heap) tuples recorded now.

The dependency closure over-approximates on purpose: a mention is matched on the
function's short name as well as its qualified name, and a class mention pulls in every
method of that class and its bases. Over-approximating costs a few needless
re-comparisons; under-approximating would report a stale agreement about a callee that
changed, which is the one thing a cache for an oracle must never do.

Entries live under `<repo>/.autoform-work/oracle/<Module>/`, one JSON file per function.
A reused verdict is always reported as cached, with the time it was computed; the
summary never folds it into the count of comparisons made now.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import time
from pathlib import Path

SCHEMA = 1
"""Bump when the entry layout or the verdict semantics change; old entries then miss."""


def canonical(obj) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str)


def digest(obj) -> str:
    return hashlib.sha256(canonical(obj).encode("utf-8")).hexdigest()


def file_digest(path) -> str:
    try:
        return hashlib.sha256(Path(path).read_bytes()).hexdigest()
    except OSError:
        return "<missing>"


def tree_digest(root, pattern) -> str:
    root = Path(root)
    return digest({str(p.relative_to(root)): file_digest(p)
                   for p in sorted(root.rglob(pattern)) if p.is_file()})


def environment_digests(repo, runtime_version: str, semantics_fingerprints: dict) -> dict:
    """Everything a verdict depends on that is not a function or a case."""
    repo = Path(repo)
    return {
        "schema": SCHEMA,
        "semantics": digest(semantics_fingerprints),
        "renderer": tree_digest(repo / "cartographer", "*.py"),
        "harness": digest({p: file_digest(repo / "scripts" / p)
                           for p in ("differential.py", "oracle_cache.py", "native_heap.py",
                                     "generated_module.py")}),
        "toolchain": file_digest(repo / "lean-toolchain"),
        "runtime": runtime_version,
    }


# ------------------------------------------------------------------- dependencies

_PY_NAME = re.compile(r'(?P<file>.+?):<module>(?:\.(?P<qual>.+))?$')


def _qual(name: str):
    m = _PY_NAME.fullmatch(name)
    if m:
        return m.group("qual") or ""
    return name.rsplit("::", 1)[-1]


def is_module_body(name: str) -> bool:
    m = _PY_NAME.fullmatch(name)
    return bool(m) and not m.group("qual")


def strings_in(node) -> set:
    """Every string value reachable in a JSON tree (keys excluded). Iterative: real
    bodies nest thousands deep (see `has_hole` in differential.py)."""
    out, stack = set(), [node]
    while stack:
        x = stack.pop()
        if isinstance(x, str):
            out.add(x)
        elif isinstance(x, dict):
            stack.extend(x.values())
        elif isinstance(x, (list, tuple)):
            stack.extend(x)
    return out


def _class_bases(funcs) -> dict:
    """class name (qualified and short) -> base class names, from `classDeclarations`."""
    bases = {}
    for f in funcs:
        for decl in f.get("classDeclarations") or []:
            if not isinstance(decl, dict) or not isinstance(decl.get("name"), str):
                continue
            bs = [b for b in decl.get("bases") or [] if isinstance(b, str)]
            bases.setdefault(decl["name"], set()).update(bs)
            if isinstance(decl.get("shortName"), str):
                bases.setdefault(decl["shortName"], set()).update(bs)
        for cls, base in (f.get("classBases") or {}).items():
            if isinstance(cls, str) and isinstance(base, str):
                bases.setdefault(cls, set()).add(base)
    return bases


def dependencies(funcs, cases_by_name: dict) -> dict:
    """name -> frozenset of function names whose translation the function's evaluation
    may depend on (itself excluded), transitively closed."""
    names = [f["name"] for f in funcs]
    name_set = set(names)
    by_short, by_qual, methods_of = {}, {}, {}
    for n in names:
        q = _qual(n)
        short = q.rsplit(".", 1)[-1] if q else n
        by_short.setdefault(short, set()).add(n)
        if q:
            by_qual.setdefault(q, set()).add(n)
        if "." in q:
            cls = q.rsplit(".", 1)[0]
            methods_of.setdefault(cls, set()).add(n)
            # the qualified class name as it appears in heap cells
            methods_of.setdefault(n[: len(n) - len(q) + len(cls)], set()).add(n)
    class_bases = _class_bases(funcs)

    def class_closure(cls):
        seen, stack = set(), [cls]
        while stack:
            c = stack.pop()
            if c in seen:
                continue
            seen.add(c)
            for b in class_bases.get(c, ()):
                stack.append(b)
                # `<unresolved-base>file:<module>.Cls:0` carries the name after the tag
                if b.startswith("<unresolved-base>"):
                    stack.append(b[len("<unresolved-base>"):].rsplit(":", 1)[0])
                stack.append(b.rsplit(".", 1)[-1])
        return seen

    def is_dunder(name):
        short = _qual(name).rsplit(".", 1)[-1]
        return short.startswith("__") and short.endswith("__")

    direct = {}
    for f in funcs:
        n = f["name"]
        # What the body can name: strings in the body and in the signature's defaults
        # (`fnref`s). Not the record's metadata (`sourceName`, types, the class
        # declarations), which would make every function mention every method.
        mentions = strings_in(f.get("body")) | strings_in(f.get("pythonSignature"))
        for c in cases_by_name.get(n, ()):
            mentions |= strings_in(c)
        deps = set()
        q = _qual(n)
        classes = set()
        if "." in q:
            classes.add(q.rsplit(".", 1)[0])
        for s in mentions:
            # A named function or method: Core resolves `mcall`/`field` by name, and the
            # receiver's class is unknown here, so every method of that short name.
            if s in name_set:
                deps.add(s)
            deps |= by_short.get(s, set())
            deps |= by_qual.get(s, set())
            if s in methods_of or s in class_bases:
                classes.add(s)
            # a `<module>.Cls.method` reference inside a longer string is not matched
        # Implicit dispatch: subscripts, operators, iteration, construction, attribute
        # access and truthiness reach the dunder methods of the receiver's class and its
        # bases without naming them. Any class the function can hold an object of --
        # its own, one it mentions, one in its cases -- contributes every dunder it
        # declares. Non-dunder methods are only reached by name, which is handled above.
        for cls in list(classes):
            for c in class_closure(cls):
                for m in methods_of.get(c, set()) | methods_of.get(_qual(c), set()):
                    if is_dunder(m):
                        deps.add(m)
        deps.discard(n)
        direct[n] = deps

    closed = {}
    for n in names:
        seen, stack = set(), list(direct.get(n, ()))
        while stack:
            d = stack.pop()
            if d in seen:
                continue
            seen.add(d)
            stack.extend(direct.get(d, ()))
        seen.discard(n)
        closed[n] = frozenset(seen)
    return closed


# --------------------------------------------------------------------- rendering

_DOC = re.compile(r"/-- `([^`]+)`")


def rendered_chunks(paths) -> tuple:
    """Split the rendered module (root and parts, in import order) into one chunk per
    documented `def` -- the renderer writes ``/-- `<name>` ... -/`` above each
    function -- and the rest (header, `program`, `moduleInits`, auxiliary functions).

    Returns ({name: digest of its chunk}, digest of the rest). A function whose chunk
    cannot be found keys on "<not rendered>" and the whole text counts as context, so
    a layout the splitter does not recognise can only over-invalidate, never replay a
    verdict about a definition that was edited."""
    chunks, rest, current = {}, [], None
    for path in paths:
        try:
            lines = Path(path).read_text(encoding="utf-8").splitlines()
        except OSError:
            rest.append("<missing %s>" % path)
            continue
        for i, line in enumerate(lines):
            m = _DOC.match(line)
            if m and i + 1 < len(lines) and lines[i + 1].startswith("def "):
                current = m.group(1)
                chunks.setdefault(current, []).append(line)
                continue
            if current is not None and line and not line[0].isspace() \
                    and not line.startswith("def "):
                current = None
            if current is not None and line.startswith("def ") and chunks[current][-1] \
                    and not _DOC.match(chunks[current][-1]) and not chunks[current][-1][0].isspace():
                current = None
            (rest if current is None else chunks[current]).append(line)
        current = None
    return ({n: digest("\n".join(ls)) for n, ls in chunks.items()}, digest("\n".join(rest)))


# -------------------------------------------------------------------------- keys

def case_digest(case) -> str:
    return digest(case)


PARTS = ("function", "rendering", "dependencies", "module_bodies", "environment", "cases")


def plan(funcs, cases_by_name: dict, env: dict, rendered=None) -> dict:
    """name -> {"key": ..., "parts": {...}, "cases": [case digests]} for every function
    that has at least one case. `parts` names each input so a miss can say why.

    `rendered` is the list of rendered Lean files (`generated_module.model_files`): the
    function's own rendered definition is part of its key, and the module text outside
    the function definitions is part of the module context, so an edit to the `.lean`
    that no AST change explains still invalidates exactly what it touches."""
    fn_digest = {f["name"]: digest(f) for f in funcs}
    chunk_of, lean_context = ({}, "<no rendered module>")
    if rendered:
        chunk_of, lean_context = rendered_chunks(rendered)
        # documented chunks that are not functions (generator resume bodies, module
        # objects) belong to the context: a change there can reach any function
        lean_context = digest([lean_context] + sorted(
            (n, d) for n, d in chunk_of.items() if n not in fn_digest))
    rendering = {n: chunk_of.get(n, "<not rendered>") for n in fn_digest}
    context = digest([sorted((n, d) for n, d in fn_digest.items() if is_module_body(n)),
                      lean_context])
    deps = dependencies(funcs, cases_by_name)
    out = {}
    for n, cases in cases_by_name.items():
        if n not in fn_digest or not cases:
            continue
        case_digests = [case_digest(c) for c in cases]
        parts = {
            "function": fn_digest[n],
            "rendering": rendering[n],
            "dependencies": digest(sorted((d, fn_digest[d], rendering[d])
                                          for d in deps.get(n, ()))),
            "module_bodies": context,
            "environment": digest(env),
            "cases": digest(sorted(case_digests)),
        }
        out[n] = {"key": digest(parts), "parts": parts, "cases": case_digests,
                  "dependency_count": len(deps.get(n, ()))}
    return out


# ------------------------------------------------------------------------- store

_UNSAFE = re.compile(r"[^A-Za-z0-9_.-]+")


def entry_path(root, name: str) -> Path:
    stem = _UNSAFE.sub("_", name)[-72:].strip("_") or "fn"
    return Path(root) / ("%s-%s.json" % (stem, hashlib.sha256(name.encode()).hexdigest()[:12]))


def load(root, name: str):
    try:
        with open(entry_path(root, name), encoding="utf-8") as fh:
            entry = json.load(fh)
    except (OSError, ValueError):
        return None
    if not isinstance(entry, dict) or entry.get("schema") != SCHEMA or entry.get("name") != name:
        return None
    return entry


def lookup(root, name: str, planned: dict):
    """(entry or None, reason). The entry is returned only on a full key match AND a
    verdict for every case digest planned now; otherwise the reason names the first
    input that differs so the run can print why it re-compared."""
    entry = load(root, name)
    if entry is None:
        return None, "no entry"
    if entry.get("key") == planned["key"]:
        verdicts = entry.get("verdicts") or {}
        if all(d in verdicts for d in planned["cases"]):
            return entry, "hit"
        return None, "entry lacks a verdict for a case recorded now"
    old = entry.get("parts") or {}
    for part in PARTS:
        if old.get(part) != planned["parts"].get(part):
            return None, "%s changed" % part
    return None, "key changed"


def store(root, name: str, planned: dict, verdicts: dict, *, module: str, when=None) -> Path:
    """Write the entry atomically. `verdicts` maps case digest -> verdict dict."""
    root = Path(root)
    root.mkdir(parents=True, exist_ok=True)
    when = when or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    entry = {"schema": SCHEMA, "name": name, "module": module, "key": planned["key"],
             "parts": planned["parts"], "computed_at": when,
             "dependency_count": planned.get("dependency_count", 0),
             "verdicts": {d: verdicts[d] for d in planned["cases"]}}
    path = entry_path(root, name)
    tmp = path.with_suffix(".json.tmp.%d" % os.getpid())
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(entry, fh, indent=1, sort_keys=True)
    os.replace(tmp, path)
    return path


def default_root(repo, module: str) -> Path:
    return Path(repo) / ".autoform-work" / "oracle" / module
