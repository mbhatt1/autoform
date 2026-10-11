"""Rank surviving mutants by how often they change the observable result.

Ben-David and Kupferman ("A framework for ranking vacuity results") rank a vacuity
result by how likely the mutated specification is to hold on a random computation.  The
analogue here: for a mutant that SURVIVED the gate, run the original function and the
mutated function through the interpreter on the SAME inputs and report the fraction on
which the observable result differs.

  * low difference rate  -> the mutated function agrees with the original almost
    everywhere, so a theorem that did not notice it is probably not saying much about
    that code: the alarming end.  Zero over the domain is `equivalent-looking`.
  * high difference rate -> the mutant changes behaviour on most inputs and still
    survived: most likely an untested corner, not a vacuous theorem.

This is a ranking aid over a stated, finite domain.  It never changes a verdict or a
score, and a zero rate over a domain does not prove equivalence outside it.

Domain: cases in the `scripts/differential.py` record format
(`{name, heap, self, args}`; `conformance.json` `runtime_cases` qualify as they are),
read from the files named by `--rank-domain`.  A function with no case in any file is
listed by name as not estimable; nothing is synthesised silently.
"""
from __future__ import annotations

import json
import os
import random
import re
import subprocess
import tempfile
import time

DEFAULT_FUEL = 5000
DEFAULT_MAX_SAMPLES = 200
DEFAULT_TIMEOUT = 600
MARK = "@@vac@@"


class Unencodable(Exception):
    pass


def lean_val(v):
    """Lean literal for a differential-format value (kept in step with differential.py)."""
    t = v[0]
    if t == "unit": return "Val.unit"
    if t == "bool": return "Val.bool " + ("true" if v[1] else "false")
    if t == "int": return "Val.int (%d)" % v[1]
    if t == "float": return "Val.float (Fl.ofBits %d)" % v[1]
    if t == "str": return "Val.str " + json.dumps(v[1])
    if t == "ref": return "Val.ref (base + %d)" % v[1]
    if t == "fn": return "Val.fn " + json.dumps(v[1])
    if t in ("list", "tuple"):
        return "Val.%s [%s]" % (t, ", ".join(lean_val(x) for x in v[1]))
    if t == "dict":
        return "Val.dict [%s]" % ", ".join("(%s, %s)" % (lean_val(a), lean_val(b)) for a, b in v[1])
    raise Unencodable(t)


def lean_heap(heap):
    cells = []
    for cell in heap:
        cls, fields = cell[0], cell[1]
        payload = cell[2] if len(cell) == 3 else None
        text = "{ cls := %s, fields := [%s]" % (
            json.dumps(cls), ", ".join("(%s, %s)" % (json.dumps(k), lean_val(v)) for k, v in fields))
        if payload is not None:
            tag, items = payload
            vals = (", ".join("(%s, %s)" % (lean_val(k), lean_val(v)) for k, v in items)
                    if tag == "dict" else ", ".join(lean_val(v) for v in items))
            text += ", payload := .%s [%s]" % (tag, vals)
        cells.append(text + " }")
    return "[" + ", ".join(cells) + "]"


def load_domains(paths):
    """{function name: [case]} from case files; also the per-file case counts."""
    domains, sources = {}, []
    for path in paths:
        with open(path, encoding="utf-8") as stream:
            data = json.load(stream)
        cases = data.get("runtime_cases", data.get("cases")) if isinstance(data, dict) else data
        if not isinstance(cases, list):
            raise ValueError("%s: no `runtime_cases` / `cases` list" % path)
        seen = {}
        for c in cases:
            if "name" not in c or "args" not in c:
                raise ValueError("%s: a case needs `name` and `args`" % path)
            case = {"heap": c.get("heap") or [], "self": c.get("self"), "args": c["args"]}
            key = json.dumps(case, sort_keys=True)
            seen.setdefault(c["name"], {})[key] = case
        for name, by_key in seen.items():
            domains.setdefault(name, {}).update({(os.path.basename(path), k): v
                                                 for k, v in by_key.items()})
        sources.append({"file": os.path.basename(path), "cases": len(cases)})
    return {n: [v for _, v in sorted(d.items(), key=lambda kv: kv[0])]
            for n, d in domains.items()}, sources


def func_name(text):
    m = re.search(r'\bname\s*:=\s*"((?:[^"\\]|\\.)*)"', text)
    return json.loads('"%s"' % m.group(1)) if m else None


def decl_text(lines, decl, mutated_line=None, mutated_new=None):
    """The `def` block's source, without the next declaration's doc comment."""
    block = list(lines[decl.start - 1:decl.end])
    if mutated_line is not None:
        block[mutated_line - decl.start] = mutated_new
    text = "".join(block).rstrip()
    if text.endswith("-/"):
        cut = max(text.rfind("\n/--"), text.rfind("\n/-!"), text.rfind("\n/-"))
        if cut >= 0:
            text = text[:cut].rstrip()
    return text


def harness(module, fuel, has_inits, original, mutant_src, cases):
    """One Lean file: run `original` and the renamed mutant on every case."""
    lean_mod = module.rsplit(".", 1)[-1]
    out = ["import %s" % module, "import Autoform.Lang.Core.Observation",
           "open Autoform.Core Autoform.Generated Autoform.Generated.%s" % lean_mod, "",
           "private def gp : Heap × Ref := initGlobals program %d %s"
           % (fuel, "moduleInits" if has_inits else "([] : List Func)"),
           "private def h0 : Heap := gp.1", "private def base : Nat := h0.length",
           "private def dctx : Ctx := "
           "{ dialect := program.dialect, table := program.table, globals := gp.2, "
           "builtinBases := program.builtinBases, properties := program.properties, "
           "excClasses := program.excClasses, classDecls := program.classDecls }",
           "", mutant_src, "",
           "private structure VCase where", "  slf : Option Val", "  args : List Val",
           "  objs : List Obj", "",
           "private def tag (r : Heap × EResult) : String :=",
           "  match r.2 with | .hole _ => \"H\" | _ => \"V\"", "",
           "private def cases : List VCase := ["]
    rows = []
    for c in cases:
        slf = "none" if c["self"] is None else "(some (%s))" % lean_val(c["self"])
        rows.append("  { slf := %s, args := [%s], objs := %s }"
                    % (slf, ", ".join(lean_val(a) for a in c["args"]), lean_heap(c["heap"])))
    out += [",\n".join(rows), "]", "",
            "private def runWith (f : Func) (c : VCase) : Heap × EResult :=",
            "  applyFunc dctx %d (h0 ++ c.objs) f c.slf c.args []" % fuel, "",
            "#eval cases.zipIdx.forM (fun (c, i) => do",
            "  let a := runWith %s c" % original,
            "  let b := runWith mutantUnderTest c",
            "  IO.println (\"%s\" ++ toString i ++ \"@@\" ++ tag a ++ tag b ++ \"@@\"" % MARK,
            "    ++ (if toString (repr a.2) == toString (repr b.2) && toString (repr a.1) == toString (repr b.1) then \"same\" else \"diff\")))"]
    return "\n".join(out) + "\n"


def parse_output(text, n):
    """{index: 'same'|'diff'|'hole'} for the cases Lean answered."""
    res = {}
    for m in re.finditer(re.escape(MARK) + r"(\d+)@@([HV])([HV])@@(same|diff)", text):
        i, ta, tb, verdict = int(m.group(1)), m.group(2), m.group(3), m.group(4)
        if i < n:
            res[i] = "hole" if "H" in (ta, tb) else verdict
    return res


def run_lean(root, source, timeout, env):
    fd, path = tempfile.mkstemp(suffix=".lean", prefix="vacuity-")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(source)
        try:
            p = subprocess.run(["lake", "env", "lean", path], cwd=root, env=env,
                               capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return None, "timeout after %ds" % timeout
        except OSError as exc:
            return None, str(exc)
        return p.stdout + p.stderr, None
    finally:
        os.remove(path)


def estimate(root, module, fuel, has_inits, original, mutant_src, name, domains, domain_note,
             cap, timeout, env, seed, runner=None):
    """One survivor -> its vacuity fields. Never raises for an unestimable survivor."""
    pool = domains.get(name, [])
    base = {"domain": domain_note, "sample": {"available": len(pool), "cap": cap}}
    if not pool:
        base.update(vacuity="not-estimable", difference_rate=None,
                    reason="no case for function %r in the domain" % name)
        return base
    cases = (pool if len(pool) <= cap
             else [pool[i] for i in sorted(random.Random(seed).sample(range(len(pool)), cap))])
    try:
        src = harness(module, fuel, has_inits, original, mutant_src, cases)
    except Unencodable as exc:
        base.update(vacuity="not-estimable", difference_rate=None,
                    reason="a case value is not encodable: %s" % exc)
        return base
    out, err = (runner or run_lean)(root, src, timeout, env)
    if err:
        base.update(vacuity="not-estimable", difference_rate=None, reason=err)
        return base
    answers = parse_output(out, len(cases))
    same = sum(v == "same" for v in answers.values())
    diff = sum(v == "diff" for v in answers.values())
    hole = sum(v == "hole" for v in answers.values())
    silent = len(cases) - len(answers)
    base["sample"].update(run=len(cases), decided=same + diff, differing=diff,
                          hole=hole, no_answer=silent)
    if not answers or same + diff == 0:
        tail = " | ".join(l for l in out.splitlines() if "error" in l)[:400] or out.strip()[-300:]
        base.update(vacuity="not-estimable", difference_rate=None,
                    reason=("every case reached a model hole or Lean gave no answer"
                            " (%d hole, %d no answer); lean errors: %s" % (hole, silent, tail)))
        return base
    rate = diff / (same + diff)
    base.update(vacuity="equivalent-looking" if diff == 0 else "estimated",
                difference_rate=rate)
    return base


def sort_key(item):
    r = item.get("difference_rate")
    return (1, 0.0) if r is None else (0, r)


def rank(items):
    """Ascending difference rate; not-estimable last. Adds `rank` (1-based, ties share)."""
    ordered = sorted(items, key=sort_key)
    last, pos = None, 0
    for i, it in enumerate(ordered, 1):
        k = sort_key(it)
        if k != last:
            pos, last = i, k
        it["rank"] = pos if it.get("difference_rate") is not None else None
    return ordered


def table(ordered):
    lines = ["=== survivor vacuity ranking (lowest difference rate first = most alarming) ==="]
    for it in ordered:
        r = it.get("difference_rate")
        sm = it.get("sample", {})
        where = "%s L%s [%s]" % (it["decl"], it["line"], it["op"])
        if r is None:
            lines.append("  --  NOT ESTIMABLE  %s: %s" % (where, it.get("reason")))
        else:
            lines.append("  #%d  %6.2f%%  %-18s %s  (%s/%s differ; %s hole; cap %s of %s)"
                         % (it["rank"], 100 * r, it["vacuity"], where, sm.get("differing"),
                            sm.get("decided"), sm.get("hole"), sm.get("cap"), sm.get("available")))
    return "\n".join(lines)


def rename_def(text, name, new="mutantUnderTest"):
    """Rename the declaration (first `def <name>`), keeping it private to the harness."""
    out, n = re.subn(r'^(\s*)(?:private\s+)?def\s+' + re.escape(name) + r'\b',
                     r'\1private def ' + new, text, count=1, flags=re.M)
    if not n:
        raise ValueError("no `def %s` in the declaration text" % name)
    return out
