#!/usr/bin/env python3
"""Execution oracle for the ledger's VERIFIABLE CORE claim.

The ledger reports, for `cachetools`:

    hole-free (upper bd) : 149 / 238 functions
    VERIFIABLE CORE      :  45 / 238 functions   -- hole-free AND call-closed
    dynamic-hole risk    : 971 constructs may hole at runtime (input-dependent)

All three are computed by static analysis of the same AST they describe. STRATEGY.md §17
names that configuration exactly: *a coverage metric computed from the artifact it
describes will flatter itself*, and "hole-free" has already had to be corrected downward
twice for precisely this reason (130 -> 12 for synthetic wrappers; then call-closure,
because an untranslated callee is invisible in the AST). "Call-closed" is correction
number two. There is no argument that it is the last one, and `dynamic-hole risk: 971`
is the ledger itself saying so: those constructs *can* hole, and only execution says
which do.

So this script does not analyse. It **runs** every function in the claimed core through
the Lean `Autoform.Core` interpreter over many inputs, and reports which ones actually
never hole.

Design commitments, all inherited from the project's own rules:

* **Ignorance is never verification.** A function nothing exercised is INCONCLUSIVE, not
  verified. `hole` (we did not translate it), `outOfFuel` (we did not run long enough)
  and a real value/exception are three outcomes, never two. Fuel exhaustion proves
  nothing in either direction and is reported as its own bucket.
* **The oracle must prove it is reading the current artifact** (§19: a stale `.olean`
  answered with the previous semantics and produced 10 fictitious findings). We `lake
  build` the generated module *and* check every `.olean` on the path is newer than its
  source before reporting anything.
* **Evidence is graded by where the input came from.** A hole reached from an argument
  the repository's own test suite actually passed is strong evidence. A hole reached
  from a synthesised input is weaker — the input may be unreachable in real code — so
  the two are counted separately and the headline number is stated both ways.

Usage:
  core_oracle.py <ast.json> <LeanModule> [src-dir] [-n INPUTS] [--tests DIR]
                 [--no-tests] [--fuel N] [--out core-oracle.json]

e.g.  python3.11 scripts/core_oracle.py ast-Cachetools.json Cachetools ~/src/cachetools
"""
import argparse, importlib.util, json, os, random, re, subprocess, sys, time

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DIFFERENTIAL = os.path.join(REPO, "scripts", "differential.py")

random.seed(20260819)          # deterministic: a moving oracle is not an oracle


# ------------------------------------------------------------------ differential reuse
#
# `scripts/differential.py` already knows how to encode Python values into `Val`, build
# receiver heaps and parse Lean's derived `Repr`. That machinery is load-bearing and was
# debugged the hard way (§27: every divergence in that episode was the apparatus). We
# import it rather than re-deriving it, and we do not edit it.

def load_differential():
    spec = importlib.util.spec_from_file_location("autoform_differential", DIFFERENTIAL)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


D = load_differential()
lean_val, lean_heap, show = D.lean_val, D.lean_heap, D.show


# The question here is only *which of the three outcomes* the interpreter produced, so
# we classify the constructor rather than parsing the payload. `differential.py`'s
# `parse_result` decodes `Val`s in order to compare them, and consequently rejects any
# constructor it has no comparison rule for — `Val.clos`, for one. A closure is a
# perfectly good answer; treating it as "no answer" would have manufactured three
# fictitious INCONCLUSIVEs, which is the §27 pattern (the apparatus, not the artifact).

HOLE_RE = re.compile(r'^\s*(?:Autoform\.Core\.)?EResult\.hole\s+"((?:[^"\\]|\\.)*)"')


def outcome_of(line):
    """-> ('hole', label) | ('outOfFuel',) | ('ok', line) | None if unrecognisable."""
    t = line.strip()
    m = HOLE_RE.match(t)
    if m: return ("hole", json.loads('"%s"' % m.group(1)))
    if re.match(r'^\s*(?:Autoform\.Core\.)?EResult\.outOfFuel\b', t): return ("outOfFuel",)
    if re.match(r'^\s*(?:Autoform\.Core\.)?EResult\.(val|exn)\b', t): return ("ok", t)
    return None


# --------------------------------------------------------------- freshness (STRATEGY §19)

def env():
    return dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])


def lake(args, timeout=1800):
    return subprocess.run(["lake"] + args, capture_output=True, text=True,
                          env=env(), cwd=REPO, timeout=timeout)


def build_or_wait(targets, tries=6, wait=60):
    """`lake build`, retried: other agents may be mid-edit in unrelated files.

    §19 is the reason this is not optional. An oracle reading a stale `.olean` answers
    with the *previous* semantics — confidently, specifically wrong. We would rather
    report nothing than report against a cache.
    """
    for i in range(tries):
        r = lake(["build"] + targets)
        if r.returncode == 0:
            return True, ""
        tail = (r.stdout + r.stderr)[-4000:]
        mine = [t for t in targets if t.split(".")[-1] in tail]
        print("lake build failed (attempt %d/%d)%s" %
              (i + 1, tries, "" if mine else " — no error in our targets; "
                                             "likely a concurrent edit elsewhere"))
        if i == tries - 1:
            return False, tail
        time.sleep(wait)
    return False, ""


def mtime_advisory(module):
    """Advisory only: Lake 4.30 decides staleness by content hash, not mtime, so an
    `.olean` older than its source can still be current. Reported, never trusted."""
    srcs = [os.path.join(REPO, "Autoform", "Lang", "Core", "Syntax.lean"),
            os.path.join(REPO, "Autoform", "Lang", "Core", "Semantics.lean"),
            os.path.join(REPO, "Autoform", "Ledger.lean"),
            os.path.join(REPO, "Autoform", "Generated", module + ".lean")]
    out = []
    for src in srcs:
        rel = os.path.relpath(src, REPO)
        cand = [os.path.join(REPO, ".lake", "build", "lib", "lean",
                             rel.replace(".lean", ".olean")),
                os.path.join(REPO, ".lake", "build", "lib",
                             rel.replace(".lean", ".olean"))]
        found = [c for c in cand if os.path.exists(c)]
        if not found:
            out.append((rel, "no .olean found"))
        elif os.path.getmtime(found[0]) < os.path.getmtime(src):
            out.append((rel, ".olean mtime older than source (content hash may still match)"))
    return out


# ------------------------------------------------------------------- the claimed core

CORE_PROBE = """import Autoform.Ledger
import Autoform.Generated.{mod}
open Autoform.Core Autoform.Generated

#eval show IO Unit from do
  for n in program.coreNames do IO.println ("@@core@@" ++ n)
  for f in program.verifiableCore do IO.println ("@@holefree@@" ++ f.name)
  for f in program.funcs do IO.println ("@@fn@@" ++ f.name)
  IO.println ("@@count@@" ++ toString program.funcs.length)
  IO.println ("@@holes@@" ++ toString program.holes.length)
"""


def claimed_core(module, scratch):
    """Ask the ledger itself which functions it claims. Never re-derive it in Python:
    the claim under test must come from the artifact making it."""
    p = os.path.join(scratch, "core_probe.lean")
    open(p, "w").write(CORE_PROBE.format(mod=module))
    r = subprocess.run(["lake", "env", "lean", p], capture_output=True, text=True,
                       env=env(), cwd=REPO, timeout=1800)
    core, holefree, names, total, holes = [], [], [], 0, None
    for l in r.stdout.splitlines():
        if l.startswith("@@core@@"):     core.append(l[8:])
        elif l.startswith("@@holefree@@"): holefree.append(l[12:])
        elif l.startswith("@@fn@@"):     names.append(l[6:])
        elif l.startswith("@@count@@"):  total = int(l[9:])
        elif l.startswith("@@holes@@"):  holes = int(l[9:])
    if not core:
        print("could not read the claimed core from Lean:\n" +
              (r.stdout + r.stderr)[:1500])
    return core, holefree, names, total, holes


# --------------------------------------------------------------------- input synthesis
#
# The claim is "this function never holes". Refuting it needs *inputs*, and the honest
# position is that we cannot know the reachable input set. So: many diverse values,
# every Core `Val` shape the interpreter can be handed, plus receivers built from the
# field names the class's own AST assigns to `self`.

POOL = [("unit",), ("bool", True), ("bool", False),
        ("int", 0), ("int", 1), ("int", -1), ("int", 2), ("int", 7), ("int", -13),
        ("int", 1000000), ("int", 256),
        ("str", ""), ("str", "a"), ("str", "key"), ("str", "0"),
        ("list", []), ("list", [("int", 1), ("int", 2)]), ("list", [("str", "a")]),
        ("tuple", []), ("tuple", [("int", 1), ("str", "a")]),
        ("dict", []), ("dict", [(("str", "a"), ("int", 1))]),
        ("dict", [(("int", 1), ("int", 2))]),
        ("fn", "len")]


def walk(n, out=None):
    """Yield every dict node of an AST body."""
    if out is None: out = []
    if isinstance(n, dict):
        out.append(n)
        for v in n.values(): walk(v, out)
    elif isinstance(n, list):
        for v in n: walk(v, out)
    return out


def count_ast_holes(funcs):
    """Total `hole` nodes in the AST bodies — a body-derived fingerprint that any
    transpiler change moves, unlike the function-name set."""
    n = 0
    for f in funcs:
        for node in walk(f.get("body")):
            # Two node kinds carry holes: `hole` in expression position and `holeS` in
            # statement position. Counting only `hole` undercounted V8Base by 324 and
            # made a matching AST look stale — a fingerprint that cries wolf gets
            # ignored, which is the same failure as one that stays silent.
            if node.get("k") in ("hole", "holeS"): n += 1
    return n


def class_of(name):
    """Owning class of a qualified function name, or None if it is free-standing.

    Python names arrive as `file.py:<module>.Class.meth`; C and C++ names arrive as
    `v8.base.Win32Time.InDST:bool(v8.base.WindowsTimezoneCache*)`, with no `:<module>.`
    anywhere. `synth_cases` already handles both, but `class_fields` matched only the
    Python form and silently returned {} for every C++ class — so every synthetic
    receiver was fieldless, every `self.f` access holed, and the oracle charged the
    module for holes the harness had manufactured. That is §27 exactly (the apparatus,
    not the artifact), and it is why both call sites now share this one function.
    """
    m = re.fullmatch(r'.+?:<module>\.(.+)', name)
    # For C/C++ the return type and parameter list follow a ':' and contain dots of
    # their own (`Get:optional(v8.base.X*)`); splitting the whole string on '.' picked
    # the class out of the *signature*. Cut the signature off first.
    head = m.group(1) if m else name.split(":", 1)[0]
    if "." not in head: return None
    return head.rsplit(".", 1)[0].split(".")[-1]


def class_fields(funcs):
    """class name -> field names, harvested from `self.f = ...` and `self.f` reads.

    A receiver with no fields makes *every* attribute access hole, which would be an
    artefact of the apparatus rather than a property of the function (§27's lesson). We
    give each synthetic receiver the fields its own class touches.
    """
    out = {}
    for f in funcs:
        cls = class_of(f["name"] or "")
        if cls is None: continue
        s = out.setdefault(cls, set())
        for n in walk(f["body"]):
            if n.get("k") == "setField" and (n.get("r") or {}).get("v") == "self":
                s.add(n["f"])
            if n.get("k") == "field" and (n.get("a") or {}).get("v") == "self":
                s.add(n["f"])
    return {k: sorted(v) for k, v in out.items()}


def synth_cases(fentry, n_inputs, fields_of):
    """N synthetic (heap, self, args) tuples for one function."""
    name = fentry["name"]
    cls = class_of(name)
    is_method = cls is not None
    params = list(fentry["params"])
    # Joern keeps `self` out of `params` for methods; `applyFunc` binds it separately.
    flds = fields_of.get(cls, []) if is_method else []
    out = []
    for i in range(n_inputs):
        heap, slf = [], None
        if is_method:
            # Receiver shape matters more than receiver values. A field holding an int
            # where real code holds an object or a dict makes the interpreter hole for
            # a reason that is ours, not the program's (§27: the apparatus is the usual
            # culprit). So the first receivers are deliberately well-shaped — every
            # field a dict, then every field a reference to a sibling object of the same
            # class — and only later ones are random.
            aux = [(cls, [(f, ("dict", [])) for f in flds]),
                   (cls, [(f, ("int", 0)) for f in flds])]
            if i % 6 == 0:
                fv = [(f, ("dict", [])) for f in flds]
            elif i % 6 == 1:
                fv = [(f, ("ref", 1)) for f in flds]
            elif i % 6 == 2:
                fv = [(f, ("list", [])) for f in flds]
            elif i % 6 == 5:
                fv = [(f, random.choice(POOL)) for f in flds][:len(flds) // 2]
            else:
                fv = [(f, random.choice(POOL + [("ref", 1), ("ref", 2)]))
                      for f in flds]
            heap = [(cls, fv)] + aux
            slf = ("ref", 0)
        args = [random.choice(POOL) for _ in params]
        if i == 0:
            args = [("int", 0) for _ in params]
        elif i == 1:
            args = [("str", "k") for _ in params]
        elif i == 2:
            args = [("dict", []) for _ in params]
        out.append({"name": name, "heap": heap, "self": slf, "args": args,
                    "origin": "synthetic"})
    return out


# ------------------------------------------------------------------- test-suite inputs

def testsuite_cases(ast_path, funcs, src_root, wanted, per_fn, tests_override, stats):
    """Real arguments, recorded by tracing the repository's own suite (§3).

    Reuses `differential.py`'s tracer and encoder verbatim. If the suite cannot run
    under this interpreter we say so and fall back to synthetic inputs only — we do not
    quietly report a smaller-but-cleaner picture.
    """
    rel_files = sorted(set(f.get("file", "") for f in funcs))
    src_root = D.resolve_src_root(src_root, rel_files)
    test_dirs = [tests_override] if tests_override else D.find_tests(src_root)
    index = D.build_lineno_index(src_root, rel_files)
    if not test_dirs or not index:
        print("test suite: none usable under %s — synthetic inputs only" % src_root)
        return [], src_root
    print("test suite: %s" % ", ".join(test_dirs))
    recs = D.trace_tests(src_root, test_dirs, index, set(wanted), per_fn, stats)
    for r in recs:
        r["origin"] = "test-suite"
        r.pop("outcome", None)          # we are not comparing values here, only holing
    print("inputs recorded from the test suite: %d" % len(recs))
    return recs, src_root


# ------------------------------------------------------------------------ lean driver

HEADER = """import Autoform.Generated.{mod}
open Autoform.Core Autoform.Generated

private def gp : Heap × Ref := initGlobals program {fuel} {inits}
private def h0 : Heap := gp.1
private def gref : Ref := gp.2
private def base : Nat := h0.length
private def octx : Ctx :=
  {{ dialect := program.dialect, table := program.table, globals := gref }}

private structure OCase where
  idx  : Nat
  objs : List Obj
  fn   : String
  slf  : Option Val
  args : List Val
  chk  : List (Nat × String)

private def orun (c : OCase) : EResult :=
  let h := h0 ++ c.objs
  if (h.get gref).map (·.cls) != some "<globals>" then
    .hole "harness:globals-frame-clobbered"
  else if c.chk.any (fun p => (h.get (base + p.1)).map (·.cls) != some p.2) then
    .hole "harness:receiver-alias"
  else
    match octx.resolve c.fn with
    | none    => .hole s!"entry:{{c.fn}}"
    -- `applyFunc` takes keyword arguments as a sixth explicit parameter. Omitting them
    -- left the application partially applied, so `.2` was a projection on a function and
    -- EVERY case failed to elaborate: the driver then read back no answers, bisected to
    -- singletons, and would have classified the entire claimed core INCONCLUSIVE. Silence
    -- that reads as "nothing refuted" is the failure this repo keeps re-learning; the
    -- kwargs list is passed explicitly here so a future signature change is a type error
    -- rather than a quiet zero.
    | some fn => (applyFunc octx {fuel} h fn c.slf c.args []).2
"""

FOOTER = """
#eval IO.println ("@@meta@@" ++ toString base ++ " " ++ toString gref)
#eval cases.forM (fun c =>
  IO.println ("@@" ++ toString c.idx ++ "@@" ++ (repr (orun c)).pretty (width := 1000000)))
"""


def case_lit(i, c):
    slf = "none" if c["self"] is None else "(some (%s))" % lean_val(c["self"])
    chk = ", ".join('(%d, %s)' % (k, json.dumps(cls))
                    for k, (cls, _) in enumerate(c["heap"]))
    return ("  { idx := %d, objs := %s, fn := %s, slf := %s, args := [%s], chk := [%s] }"
            % (i, lean_heap(c["heap"]), json.dumps(c["name"]), slf,
               ", ".join(lean_val(a) for a in c["args"]), chk))


class Driver:
    def __init__(self, module, fuel, scratch):
        gen = os.path.join(REPO, "Autoform", "Generated", module + ".lean")
        inits = ("moduleInits" if os.path.exists(gen)
                 and "def moduleInits" in open(gen, encoding="utf-8").read()
                 else "([] : List Func)")
        self.header = HEADER.format(mod=module, fuel=fuel, inits=inits).splitlines()
        self.path = os.path.join(scratch, "core_oracle_scratch.lean")
        self.base = 0

    def eval(self, cases, idxs, depth=0):
        """idx -> repr line. Bisects on failure: one bad case must not lose a batch."""
        if not idxs: return {}
        src = self.header + ["private def cases : List OCase := ["] + \
            [",\n".join(case_lit(i, cases[i]) for i in idxs)] + ["]"] + \
            FOOTER.splitlines()
        open(self.path, "w").write("\n".join(src) + "\n")
        try:
            out = subprocess.run(["lake", "env", "lean", self.path], capture_output=True,
                                 text=True, env=env(), cwd=REPO, timeout=1800)
        except subprocess.TimeoutExpired:
            return {}
        got = {}
        for l in out.stdout.splitlines():
            m = re.match(r'@@meta@@(\d+) (\d+)', l)
            if m:
                self.base = int(m.group(1)); continue
            m = re.match(r'@@(\d+)@@(.*)', l)
            if m and int(m.group(1)) in idxs: got[int(m.group(1))] = m.group(2)
        if len(got) < len(idxs) and len(idxs) > 1:
            mid = len(idxs) // 2
            got.update(self.eval(cases, idxs[:mid], depth + 1))
            got.update(self.eval(cases, idxs[mid:], depth + 1))
        elif len(got) < len(idxs) and depth == 0:
            print("  lean answered nothing for a singleton batch: %s"
                  % (out.stdout[:150] + out.stderr[:300]).replace("\n", " ")[:300])
        return got


# ------------------------------------------------------------------------------- main

def pct(a, b):
    return "n/a" if not b else "%d%%" % (100 * a // b)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("ast")
    ap.add_argument("module")
    ap.add_argument("src_root", nargs="?", default=None)
    ap.add_argument("-n", "--inputs", type=int, default=24,
                    help="synthetic inputs per function (default 24)")
    ap.add_argument("--tests", default=None)
    ap.add_argument("--no-tests", action="store_true")
    ap.add_argument("--fuel", type=int, default=5000)
    ap.add_argument("--out", default="core-oracle.json")
    ap.add_argument("--scratch", default="/tmp")
    # Batch size. Each batch costs one `lake env lean` start plus one import of the
    # generated module, which on a 1.7 MB C++ module (V8Base) dominates the per-case
    # interpretation cost by an order of magnitude: at the historical 20 the V8Base run
    # projected to ~11 h. Larger batches amortise that import; a batch that fails is
    # still bisected, so the classification is unchanged, only the wall clock.
    ap.add_argument("--chunk", type=int, default=20,
                    help="cases per Lean invocation (default 20)")
    a = ap.parse_args()

    funcs = json.load(open(a.ast))
    by_name = {f["name"]: f for f in funcs}

    # ---- 1. the artifact must be current before anything it says is evidence (§19)
    ok, tail = build_or_wait(["Autoform.Generated." + a.module, "Autoform.Ledger"])
    if not ok:
        print("ABORT: `lake build` did not succeed. Reporting nothing is the correct\n"
              "outcome: an oracle that reads a stale .olean is worse than no oracle.\n"
              + tail[-1200:])
        return 2
    for rel, why in mtime_advisory(a.module):
        print("note: %s — %s" % (rel, why))

    # ---- 2. the claim under test, read from the artifact that makes it
    core, holefree, lean_names, nfuncs, lean_holes = claimed_core(a.module, a.scratch)
    if not core:
        print("ABORT: no claimed core to test.")
        return 2

    # ---- the §19 gate, done in-band rather than by timestamps: the module Lean just
    # loaded must be the module the AST describes. A stale `.olean` answers with the
    # previous program; comparing the *contents* of both catches that, and unlike an
    # mtime comparison it cannot be fooled by Lake's content-hash rebuild policy.
    ast_names, olean_names = set(by_name), set(lean_names)
    missing = ast_names - olean_names
    if missing:
        print("ABORT: %d functions in %s are absent from the module Lean just loaded. "
              "The .olean does not describe the current AST — exactly STRATEGY.md §19's "
              "stale-cache failure, where the oracle answers with the previous program. "
              "Reporting nothing is the correct outcome."
              % (len(missing), os.path.basename(a.ast)))
        for n in list(missing)[:5]: print("   %s" % n)
        return 2
    extra = olean_names - ast_names
    if extra:
        # The reverse direction is not staleness: the exported AST is filtered (Joern's
        # synthetic `<metaClassAdapter>` wrappers were excluded after §17's first
        # correction), so the module legitimately declares more than the AST lists. We
        # only ever *run* what the ledger claims, so extras are noted, not fatal.
        print("note: the module declares %d functions the AST does not list "
              "(e.g. %s) — filtered synthetic wrappers, not staleness"
              % (len(extra), sorted(extra)[0].split(":<module>.")[-1]))
    # Name-set agreement is necessary but NOT sufficient: a regenerated AST whose
    # *bodies* changed (a hole label resolved, a construct newly translated) has exactly
    # the same names. Reading only names, this gate went quiet on a V8Base AST that was
    # one transpiler commit behind the module — 1731 holes on disk against 1475 in the
    # .olean — which is the same silence-reads-as-success shape §19 is about. Compare a
    # body-derived quantity too: the total hole count, which every transpiler change
    # moves. Not fatal (the AST is used only for parameter shapes and receiver fields;
    # the claim under test and the execution both come from Lean), but never silent.
    ast_holes = count_ast_holes(funcs)
    body_stale = lean_holes is not None and ast_holes != lean_holes
    if body_stale:
        print("WARNING — AST BODIES ARE NOT THE MODULE'S: %s holds %d holes, the loaded "
              "module holds %d. The names match, so this gate would otherwise have "
              "passed in silence. Execution and the claim under test both come from "
              "Lean and are unaffected; the AST here supplies only parameter shapes and "
              "receiver field names, so synthetic inputs may be shaped for a previous "
              "revision. Recorded in the output as ast_body_staleness."
              % (os.path.basename(a.ast), ast_holes, lean_holes))
    elif lean_holes is None:
        print("WARNING: the Lean probe reported no hole count — body-staleness "
              "UNCHECKED, not verified.")
    print("freshness: names OK — every one of %s's %d functions is present in the "
          "loaded .olean; hole counts %s (AST %d, module %s)"
          % (os.path.basename(a.ast), len(ast_names),
             "AGREE" if not body_stale and lean_holes is not None else "DISAGREE"
             if body_stale else "UNCHECKED", ast_holes,
             "?" if lean_holes is None else lean_holes))
    print("ledger claims: %d functions total, %d hole-free, %d VERIFIABLE CORE"
          % (nfuncs, len(holefree), len(core)))
    core_set = set(core)

    # ---- 3. inputs
    fields_of = class_fields(funcs)
    cases = []
    stats = {"skip_varargs": 0, "skip_unencodable_args": 0, "skip_unencodable_ret": 0,
             "skip_no_instance": 0, "test_runs": []}
    src_root = a.src_root
    if src_root and not a.no_tests:
        try:
            recs, src_root = testsuite_cases(a.ast, funcs, src_root, core_set,
                                             max(4, a.inputs // 4), a.tests, stats)
            cases += recs
        except Exception as e:                                   # noqa: BLE001
            print("test-suite tracing unavailable (%r) — synthetic inputs only.\n"
                  "  (cachetools' suite needs python3.11; re-run this script under it.)"
                  % (e,))
    elif not src_root:
        print("no source dir given — synthetic inputs only "
              "(pass the repo root for test-suite-derived arguments)")

    real_names = set(c["name"] for c in cases)
    for n in core:
        f = by_name.get(n)
        if f is None: continue
        cases += synth_cases(f, a.inputs, fields_of)

    # ---- 4. execute
    drv = Driver(a.module, a.fuel, a.scratch)
    got = {}
    CHUNK = max(1, a.chunk)
    order = list(range(len(cases)))
    t0 = time.time()
    for i in range(0, len(order), CHUNK):
        got.update(drv.eval(cases, order[i:i + CHUNK]))
        if i % 200 == 0:
            print("  ran %d/%d cases (%.0fs)" % (min(i + CHUNK, len(order)),
                                                 len(order), time.time() - t0))
    print("executed %d/%d cases; %d got no answer from the interpreter"
          % (len(got), len(cases), len(cases) - len(got)))
    # A harness that answers nothing answers nothing ABOUT NOTHING: every function would
    # land in INCONCLUSIVE and the run would look like "no refutations". That is a broken
    # apparatus, not a result, and it must be loud. (It happened: the driver called
    # `applyFunc` without its kwargs argument and no case elaborated at all.)
    if cases and not got:
        print("ABORT: the interpreter produced no answer for ANY of the %d cases. This "
              "is an apparatus failure, not a verification result — reporting a core of "
              "all-INCONCLUSIVE would read as 'nothing refuted'. Nothing written."
              % len(cases))
        return 2

    # ---- 5. classify. hole / outOfFuel / result are three outcomes, never two.
    per = {n: {"cases": 0, "answered": 0, "ok": 0, "holes": {}, "fuel": 0,
               "no_answer": 0, "hole_examples": [], "real_cases": 0,
               "real_holes": 0, "synth_holes": 0} for n in core}
    for i, c in enumerate(cases):
        p = per.get(c["name"])
        if p is None: continue
        p["cases"] += 1
        if c["origin"] == "test-suite": p["real_cases"] += 1
        line = got.get(i)
        if line is None:
            p["no_answer"] += 1; continue
        r = outcome_of(line)
        if r is None:
            p["no_answer"] += 1; continue
        p["answered"] += 1
        if r[0] == "outOfFuel":
            p["fuel"] += 1                    # proves nothing; its own bucket
        elif r[0] == "hole":
            lab = r[1]
            if lab.startswith("harness:"):    # apparatus, not artifact (§27)
                p["no_answer"] += 1; p["answered"] -= 1; continue
            p["holes"][lab] = p["holes"].get(lab, 0) + 1
            if c["origin"] == "test-suite": p["real_holes"] += 1
            else: p["synth_holes"] += 1
            if len(p["hole_examples"]) < 4:
                p["hole_examples"].append(
                    {"label": lab, "origin": c["origin"],
                     "self": show(c["self"]) if c["self"] else None,
                     "args": "(%s)" % ", ".join(show(x) for x in c["args"])})
        else:
            p["ok"] += 1                      # a genuine value or exception

    verified, holed, holed_real, inconclusive = [], [], [], []
    for n in core:
        p = per[n]
        if p["answered"] == 0 or (p["ok"] == 0 and not p["holes"]):
            inconclusive.append(n)
        elif p["holes"]:
            holed.append(n)
            if p["real_holes"]: holed_real.append(n)
        else:
            verified.append(n)

    # "exercised" means the interpreter produced a real outcome — a value, an exception
    # or a hole. A function that only ever ran out of fuel was not exercised: fuel
    # exhaustion is evidence of nothing.
    exercised = [n for n in core if per[n]["ok"] or per[n]["holes"]]
    # the strictest honest number: never holed AND actually exercised
    corrected = len(verified)
    corrected_real = len([n for n in core if per[n]["real_cases"] > 0
                          and not per[n]["real_holes"] and per[n]["answered"] > 0
                          and per[n]["ok"] > 0])

    labels = {}
    for n in holed:
        for l, k in per[n]["holes"].items(): labels[l] = labels.get(l, 0) + k

    out = {
        "module": a.module, "ast": os.path.abspath(a.ast),
        "ast_body_staleness": {
            "ast_holes": ast_holes, "module_holes": lean_holes,
            "stale": bool(body_stale),
            "note": ("the AST on disk is not the revision the module was rendered from; "
                     "it supplies only parameter shapes and receiver fields here, while "
                     "the claim and the execution come from Lean")
                    if body_stale else "AST and module agree on hole count"},
        "source_root": os.path.abspath(src_root) if src_root else None,
        "fuel": a.fuel, "synthetic_inputs_per_function": a.inputs,
        "claim": {"functions": nfuncs, "hole_free": len(holefree),
                  "verifiable_core_static": len(core)},
        "executed": {"cases": len(cases), "answered": len(got),
                     "core_functions_exercised": len(exercised),
                     "core_functions_with_real_inputs": len(real_names & core_set)},
        "result": {
            "verifiable_core_executed": corrected,
            "verifiable_core_executed_real_inputs_only": corrected_real,
            "holed_on_some_input": len(holed),
            "holed_on_a_real_input": len(holed_real),
            "inconclusive_never_exercised": len(inconclusive)},
        "holed_functions": [
            {"name": n, "cases": per[n]["cases"], "answered": per[n]["answered"],
             "clean": per[n]["ok"], "outOfFuel": per[n]["fuel"],
             "hole_labels": per[n]["holes"], "real_input_holes": per[n]["real_holes"],
             "examples": per[n]["hole_examples"]}
            for n in sorted(holed, key=lambda x: -sum(per[x]["holes"].values()))],
        "verified_functions": [
            {"name": n, "inputs": per[n]["answered"], "real_inputs": per[n]["real_cases"]}
            for n in sorted(verified)],
        "inconclusive_functions": [
            {"name": n, "cases": per[n]["cases"], "no_answer": per[n]["no_answer"],
             "outOfFuel": per[n]["fuel"]} for n in sorted(inconclusive)],
        "hole_labels": dict(sorted(labels.items(), key=lambda kv: -kv[1])),
        "skipped": {k: v for k, v in stats.items() if k.startswith("skip")},
        "unencodable_reasons": stats.get("unencodable_reasons", {}),
    }
    json.dump(out, open(a.out, "w"), indent=1)

    # ------------------------------------------------------------------ summary
    print("""
╭─ core oracle ─ %s — the verifiable core, executed
│ ledger's static claim   : %d / %d functions (%s) hole-free AND call-closed
│ executed                : %d cases over %d claimed-core functions
│ exercised at all        : %d / %d (%s) of the claimed core
│   … with real (test-suite) inputs : %d
├─ outcome ────────────────────────────────────────────────────
│ NEVER HOLED (executed)  : %d / %d (%s of the claim survives)
│ HOLED on some input     : %d   (of which %d on a *real* input)
│ INCONCLUSIVE (unrun)    : %d   — never exercised; not verified, not refuted
├─ hole labels observed at runtime ────────────────────────────""" % (
        a.module, len(core), nfuncs, pct(len(core), nfuncs), len(cases), len(core),
        len(exercised), len(core), pct(len(exercised), len(core)),
        len(real_names & core_set),
        corrected, len(core), pct(corrected, len(core)),
        len(holed), len(holed_real), len(inconclusive)))
    for l, k in sorted(labels.items(), key=lambda kv: -kv[1])[:15]:
        print("│ %4d  %s" % (k, l))
    print("╰───────────────────────────────────────────────────────────────")

    if holed:
        print("\nfunctions that hole at runtime despite being in the claimed core:")
        for n in sorted(holed, key=lambda x: -sum(per[x]["holes"].values()))[:40]:
            ex = per[n]["hole_examples"][0] if per[n]["hole_examples"] else {}
            print("  %-64s %2d/%2d inputs hole  %s"
                  % (n.split(":<module>.")[-1][:64], sum(per[n]["holes"].values()),
                     per[n]["answered"], list(per[n]["holes"])[:3]))
            if ex:
                print("      e.g. self=%s args=%s  [%s]"
                      % (ex.get("self"), ex.get("args"), ex.get("origin")))
    fuelly = [n for n in core if per[n]["fuel"]]
    if fuelly:
        print("\noutOfFuel on some input (evidence of nothing, reported separately): %d"
              % len(fuelly))
    print("""
Read this as: of the %d functions the ledger calls the verifiable core, execution could
reach %s of them, and %d of those never holed over the inputs tried. %s

`core-oracle.json` written to %s.""" % (
        len(core), pct(len(exercised), len(core)), corrected,
        ("The static claim did NOT survive contact with execution: %d claimed-core "
         "functions hole at runtime." % len(holed)) if holed else
        "No claimed-core function holed on any input tried — the claim survived, "
        "for the fraction that ran.",
        os.path.abspath(a.out)))
    return 1 if holed else 0


if __name__ == "__main__":
    sys.exit(main())
