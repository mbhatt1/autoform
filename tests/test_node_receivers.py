"""JavaScript instance methods in the Node oracle, on a receiver the driver builds.

`node_backend` used to refuse every instance method ("receiver fixture required"). It now
calls an instance method of a module-scope class whose constructor takes no arguments on a
fresh object the driver builds with that constructor, as the JVM oracle does for a Java
receiver (`tests/test_java_receivers.py`). The driver reports that object's own enumerable
data properties -- encodable values only -- immediately before the call and again after
it, every array or plain object it (or a module binding the body reads) holds as its own
cell. The case starts Core from exactly that reported state, with the receiver bound as
the `self` the exporter lowers `this` to, and the post-call state is compared as well as
the result. What the reported state cannot carry is a NAMED refusal: a constructor that
throws or needs arguments, a getter or setter, an accessor, symbol or non-enumerable own
property, an inherited getter, setter or data property the body touches, a private (#)
member (not an own property, so not observable), and a value the wire cannot carry.

1. The driver alone (needs Node): the reported state, the post state (a container through
   the cell the pre state named, a container the call creates as a new cell, the receiver
   itself as cell 0), module bindings, and every refusal by its reason.
2. End to end (needs Joern, Node and Lean; `AUTOFORM_TEST_JOERN=1`): the Joern export of
   the fixture is rendered and built, every instance method is COMPARED and AGREES, and a
   deliberately wrong model of a write that returns nothing DIVERGES on the heap
   observation alone.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
GENERATED = ROOT / "Autoform" / "Generated"
HAVE_NODE = bool(shutil.which("node"))

SOURCE = """export class Gauge {
  constructor() { this.n = 2; this.hist = []; this.meta = { unit: "pts" }; }
  add(k) { this.n = this.n + k; this.hist.push(k); return this.n; }
  reset(v) { this.n = v; this.label = "marked"; }
  alias() { this.b = this.meta; return 7; }
  unit() { return this.meta.unit; }
  half() { this.n = this.n * 0.5; return this.n; }
  items() { return this.hist; }
  grow(k) { this.extra = [k]; return this.extra; }
  nest(k) { this.deep = [[k], { v: k }]; return this; }
}
"""
METHODS = ("add", "reset", "alias", "unit", "half", "items", "grow", "nest")

# A module container the receiver also holds (one object, one cell, however reached), a
# module container it does not hold (a cell of its own), a scalar module binding, and a
# receiver that holds itself.
SHARED = ("export const shared = [5];\n"
          "export class Tuck { constructor() { this.xs = shared; }"
          " tuck(a) { shared.push(a); return shared.length; } }\n")
MODLIST = ("export const xs = [1, 2];\n"
           "export class ModList { constructor() { this.n = 1; } m(a) { return xs.length; } }\n")
SCALAR = ("export const K = 3;\n"
          "export class Scal { constructor() { this.n = 1; } gain(a) { return K + a; } }\n"
          "export function plain(a) { return a + 1; }\n")
# Driver only: the exporter does not yet lower `throw new RangeError(..)` without a hole.
THROWER = ("export class Thrower { constructor() { this.n = 1; }"
           " fail() { this.n = 9; throw new RangeError('no'); } }\n")
LOOP = "export class Loop { constructor() { this.me = this; this.box = [this]; } one() { return 1; } }\n"


def _self_field(f):
    return {"k": "ret", "e": {"k": "field", "a": {"k": "name", "v": "self"}, "f": f}}


# One fixture per refusal: (source text, candidate name, params, body, the named reason).
# A body matters only where the backend's static scan reads it (private members, the
# properties read through `this`, a module binding named `self`).
REFUSED = {
    "boom.js": ("export class Boom { constructor() { throw new Error('nope'); } one() { return 1; } }",
                "boom.js::program:Boom:one", ["a"], None,
                "receiver not built: constructor threw Error"),
    "needsarg.js": ("export class NeedsArg { constructor(v) { this.v = v; } one() { return 1; } }",
                    "needsarg.js::program:NeedsArg:one", ["a"], None,
                    "NeedsArg.one is an instance method, but the constructor of NeedsArg needs arguments"),
    "locked.js": ("export class Locked { constructor() {"
                  " Object.defineProperty(this, 'hidden', { value: 5, enumerable: false }); }"
                  " one() { return 1; } }",
                  "locked.js::program:Locked:one", ["a"], None,
                  "receiver property hidden is not enumerable: not observable"),
    "accessor.js": ("export class Accessor { constructor() {"
                    " Object.defineProperty(this, 'ro', { get() { return 1; }, enumerable: true }); }"
                    " one() { return 1; } }",
                    "accessor.js::program:Accessor:one", ["a"], None,
                    "receiver property ro is an accessor property: not observable"),
    "sym.js": ("export class Sym { constructor() { this[Symbol('s')] = 1; } one() { return 1; } }",
               "sym.js::program:Sym:one", ["a"], None,
               "receiver property Symbol(s) is a symbol key: not observable"),
    "holds.js": ("export class Inner { constructor() { this.x = 1; } }\n"
                 "export class Holds { constructor() { this.other = new Inner(); } one() { return 1; } }",
                 "holds.js::program:Holds:one", ["a"], None,
                 "receiver property other: no encoding for a value of type object (Inner)"),
    "fnprop.js": ("export class FnProp { constructor() { this.cb = () => 1; } one() { return 1; } }",
                  "fnprop.js::program:FnProp:one", ["a"], None,
                  "receiver property cb: no encoding for a value of type function"),
    "leak.js": ("export class Leak { constructor() { this.n = 1; } spoil() { this.f = () => 2; return 1; } }",
                "leak.js::program:Leak:spoil", [], None,
                "receiver state after the call: receiver property f: no encoding for a value "
                "of type function"),
    "got.js": ("export class Got { constructor() { this.acc = 1; } get total() { return 5; } }",
               "got.js::program:Got:total", [], None,
               "Got.total is a getter or setter, not a method"),
    "setter.js": ("export class Setter { constructor() { this.acc = 1; } set total(v) { this.acc = v; } }",
                  "setter.js::program:Setter:total", ["v"], None,
                  "Setter.total is a getter or setter, not a method"),
    "proto.js": ("export class Proto { constructor() { this.n = 1; } }\n"
                 "Proto.prototype.data = 3;",
                 "proto.js::program:Proto:data", [], None,
                 "Proto.data is a prototype data property, not a method"),
    "inhget.js": ("export class InhGet { constructor() { this.n = 1; } get g() { return 5; }"
                  " read() { return this.g; } }",
                  "inhget.js::program:InhGet:read", [], _self_field("g"),
                  "receiver property g is an inherited getter or setter: not observable"),
    "inhdata.js": ("export class InhData { constructor() { this.n = 1; } read() { return this.d; } }\n"
                   "InhData.prototype.d = 4;",
                   "inhdata.js::program:InhData:read", [], _self_field("d"),
                   "receiver property d is an inherited prototype data property: not observable"),
    "priv.js": ("export class Priv { #s = 1; constructor() { this.n = 1; } read() { return this.#s; } }",
                "priv.js::program:Priv:read", [], _self_field("#s"),
                "Priv.read reads or writes a private (#) member: the receiver state cannot observe it"),
    # The private member is behind a method call on `this`: the scan follows it.
    "privcall.js": ("export class PrivCall { #z = 1; constructor() { this.n = 1; }"
                    " outer() { return this.inner(); } inner() { return this.#z; } }",
                    "privcall.js::program:PrivCall:outer", [],
                    {"k": "ret", "e": {"k": "mcall", "recv": {"k": "name", "v": "self"},
                                       "m": "inner", "args": []}},
                    "PrivCall.outer reads or writes a private (#) member: the receiver state "
                    "cannot observe it"),
    "mark.js": ("export class Mark { constructor() { this.n = 1; } m(a) { return a; } }",
                "mark.js::program:Mark:m", ["this", "a"], None,
                "Mark.m is an instance method, and a this parameter cannot also name its receiver"),
    # A module binding named `self` would shadow the receiver inside the model.
    "selfy.js": ("export const self = 1;\n"
                 "export class S { constructor() { this.n = 1; } m(a) { return a; } }",
                 "selfy.js::program:S:m", ["a"], {"k": "ret", "e": {"k": "name", "v": "self"}},
                 "the module binds self, which the receiver must name"),
    "ghost.js": ("export class Real { constructor() { this.n = 1; } one() { return 1; } }",
                 "ghost.js::program:Ghost:one", [], None,
                 "class Ghost not accessible at module scope"),
}


def _fn(name, file, params, body=None):
    return {"name": name, "file": file, "params": params, "body": body or {"k": "skip"}}


def _length_of(name):
    return {"k": "ret", "e": {"k": "field", "a": {"k": "name", "v": name}, "f": "length"}}


@pytest.mark.skipif(not HAVE_NODE, reason="Node unavailable")
def test_driver_reports_the_receiver_it_built_and_names_every_refusal(tmp_path, differential):
    source = tmp_path / "source"
    source.mkdir()
    for file, text in (("gauge.js", SOURCE), ("shared.js", SHARED), ("modlist.js", MODLIST),
                       ("scal.js", SCALAR), ("loop.js", LOOP), ("thrower.js", THROWER)):
        (source / file).write_text(text)
    params = {"add": ["k"], "reset": ["v"], "grow": ["k"], "nest": ["k"]}
    funcs = [_fn("gauge.js::program:Gauge:" + m, "gauge.js", params.get(m, [])) for m in METHODS]
    funcs += [_fn("gauge.js::program:Gauge:<init>", "gauge.js", []),
              _fn("shared.js::program:Tuck:tuck", "shared.js", ["a"], _length_of("shared")),
              _fn("modlist.js::program:ModList:m", "modlist.js", ["a"], _length_of("xs")),
              _fn("scal.js::program:Scal:gain", "scal.js", ["a"],
                  {"k": "ret", "e": {"k": "binop", "op": "js:+",
                                     "a": {"k": "name", "v": "K"}, "b": {"k": "name", "v": "a"}}}),
              _fn("scal.js::program:plain", "scal.js", ["a"]),
              _fn("loop.js::program:Loop:one", "loop.js", []),
              _fn("thrower.js::program:Thrower:fail", "thrower.js", [])]
    # The private method `PrivCall:inner` is a candidate of its own, refused for the same reason.
    funcs.append(_fn("privcall.js::program:PrivCall:inner", "privcall.js", [], _self_field("#z")))
    for file, (text, name, ps, body, _) in REFUSED.items():
        (source / file).write_text(text + "\n")
        funcs.append(_fn(name, file, ps, body))
    cases, info, skipped = differential.runtime_backends.node_backend(
        str(source), funcs, 2, "js", tmp_path / "work")

    for _, name, _, _, reason in REFUSED.values():
        assert skipped.get(name) == reason, (name, skipped.get(name))
    assert skipped["privcall.js::program:PrivCall:inner"] == (
        "PrivCall.inner reads or writes a private (#) member: the receiver state cannot observe it")
    assert skipped["gauge.js::program:Gauge:<init>"] == "constructor: receiver fixture required"
    instance = {"gauge.js::program:Gauge:" + m for m in METHODS} | {
        "shared.js::program:Tuck:tuck", "modlist.js::program:ModList:m",
        "scal.js::program:Scal:gain", "loop.js::program:Loop:one",
        "thrower.js::program:Thrower:fail"}
    assert {c["name"] for c in cases} == instance | {"scal.js::program:plain"}
    assert info["instance_cases"] == 2 * len(instance)

    by = {}
    for c in cases:
        by.setdefault(c["name"].rsplit(":", 1)[1], []).append(c)
    # A module-scope function is read exactly as before: no receiver, no heap observation.
    for c, a in zip(by["plain"], (0, 1)):
        assert c["self"] is None and "post_heap" not in c and c["origin"] == "native"
        assert c["outcome"] == ("val", ("int", a + 1))
    for name in instance:
        for c in by[name.rsplit(":", 1)[1]]:
            assert c["self"] == ("ref", 0) and c["origin"] == "constructed", c
            assert "post_heap" in c

    # The Gauge the constructor built, exactly as reported, is the case's whole heap:
    # the receiver, then one cell per container it holds.
    fresh = [("Gauge", [("n", ("int", 2)), ("hist", ("ref", 1)), ("meta", ("ref", 2))], None),
             ("list", [], ("list", [])),
             ("dict", [], ("dict", [(("str", "unit"), ("str", "pts"))]))]
    for m in METHODS:
        assert all(c["heap"] == fresh for c in by[m]), m

    def post(c):
        return dict(c["post_heap"][0][1])

    # `add` writes `n` and grows the cell `hist` named; a fresh receiver per case, so the
    # second case's history holds only its own argument.
    for c, k in zip(by["add"], (0, 1)):
        assert c["args"] == [("int", k)] and c["outcome"] == ("val", ("int", 2 + k))
        assert post(c) == {"n": ("int", 2 + k), "hist": ("ref", 1), "meta": ("ref", 2)}
        assert c["post_heap"][1:] == [("list", [], ("list", [("int", k)])), fresh[2]]
    # `reset` returns undefined: only the post state says what it did.
    for c, v in zip(by["reset"], (0, 1)):
        assert c["outcome"] == ("val", ("unit",))
        assert [k for k, _ in c["post_heap"][0][1]] == ["n", "hist", "meta", "label"]
        assert post(c)["n"] == ("int", v) and post(c)["label"] == ("str", "marked")
    # `alias` points `b` at the address `meta` names: identity, not an equal copy.
    for c in by["alias"]:
        assert c["outcome"] == ("val", ("int", 7))
        assert post(c)["b"] == post(c)["meta"] == ("ref", 2)
    for c in by["unit"]:
        assert c["outcome"] == ("val", ("str", "pts")) and c["post_heap"] == c["heap"]
    # `2 * 0.5` is the Number 1, reported as Node reports any safe integer.
    for c in by["half"]:
        assert c["outcome"] == ("val", ("int", 1)) and post(c)["n"] == ("int", 1)
    # A returned container the receiver holds is that cell, not a copy of its contents.
    for c in by["items"]:
        assert c["outcome"] == ("val", ("ref", 1)) and c["post_heap"] == c["heap"]
    # A container the call creates is a new cell after the pre state's.
    for c, k in zip(by["grow"], (0, 1)):
        assert c["outcome"] == ("val", ("ref", 3)) and post(c)["extra"] == ("ref", 3)
        assert c["post_heap"][1:] == fresh[1:] + [("list", [], ("list", [("int", k)]))]
    # ... nested ones too, each its own cell; `return this` is the receiver, cell 0.
    for c, k in zip(by["nest"], (0, 1)):
        assert c["outcome"] == ("val", ("ref", 0)) and post(c)["deep"] == ("ref", 3)
        assert c["post_heap"][3:] == [("list", [], ("list", [("ref", 4), ("ref", 5)])),
                                      ("list", [], ("list", [("int", k)])),
                                      ("dict", [], ("dict", [(("str", "v"), ("int", k))]))]
    # A throwing method's writes before the throw are still compared.
    for c in by["fail"]:
        assert c["heap"] == [("Thrower", [("n", ("int", 1))], None)]
        assert c["outcome"] == ("exn", "RangeError") and post(c)["n"] == ("int", 9)

    # `tuck` mutates the module container through its module name, which the receiver
    # also holds (`this.xs`): one cell, bound by the module name as well. The module's
    # container is one object across cases, read immediately before each call.
    for c, (a, pre) in zip(by["tuck"], ((0, [5]), (1, [5, 0]))):
        assert c["globals"] == [("shared", ("ref", 1))]
        assert c["heap"] == [("Tuck", [("xs", ("ref", 1))], None),
                             ("list", [], ("list", [("int", v) for v in pre]))]
        assert c["outcome"] == ("val", ("int", len(pre) + 1))
        assert c["post_heap"][1] == ("list", [], ("list", [("int", v) for v in pre + [a]]))
    # A module container the receiver does not hold is a cell of its own, compared too.
    for c in by["m"]:
        assert c["globals"] == [("xs", ("ref", 1))]
        assert c["heap"] == [("ModList", [("n", ("int", 1))], None),
                             ("list", [], ("list", [("int", 1), ("int", 2)]))]
        assert c["outcome"] == ("val", ("int", 2)) and c["post_heap"] == c["heap"]
    for c, a in zip(by["gain"], (0, 1)):
        assert c["globals"] == [("K", ("int", 3))]
        assert c["heap"] == [("Scal", [("n", ("int", 1))], None)]
        assert c["outcome"] == ("val", ("int", 3 + a)) and c["post_heap"] == c["heap"]
    # A receiver that holds itself is a reference cycle through cell 0, not a refusal.
    for c in by["one"]:
        assert c["heap"] == [("Loop", [("me", ("ref", 0)), ("box", ("ref", 1))], None),
                             ("list", [], ("list", [("ref", 0)]))]
        assert c["post_heap"] == c["heap"]


def _env():
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    env.pop("AUTOFORM_NO_REEXEC", None)
    return env


def _run(args, cwd, env, timeout=900):
    p = subprocess.run(list(map(str, args)), cwd=cwd, env=env, text=True,
                       capture_output=True, timeout=timeout)
    assert p.returncode == 0, p.stdout[-3000:] + p.stderr[-3000:]
    return p


@pytest.fixture
def node_export(tmp_path):
    if not (os.environ.get("AUTOFORM_TEST_JOERN") == "1"
            or os.environ.get("AUTOFORM_TEST_ORACLES") == "1"):
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to run the Node receiver oracle end to end")
    env = _env()
    for tool in ("node", "lake"):
        if not shutil.which(tool, path=env["PATH"]):
            pytest.skip(tool + " unavailable")
    joern = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    if (joern / "joern-cli").is_dir():
        joern /= "joern-cli"
    if not (joern / "joern-parse").exists():
        pytest.skip("Joern unavailable")
    source = tmp_path / "source"
    source.mkdir()
    (source / "receivers.js").write_text(SOURCE)
    _run([joern / "joern-parse", source, "--language", "JSSRC", "--output", "cpg.bin"],
         tmp_path, env)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=cpg.bin", "--param", "out=ast.json"], tmp_path, env)
    module = "NodeReceiversFixture"
    target = GENERATED / (module + ".lean")
    try:
        _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp_path / "ast.json",
              target, module], ROOT, env)
        yield tmp_path, source, module, target, env
    finally:
        target.unlink(missing_ok=True)
        for product in (ROOT / ".lake/build/lib/lean/Autoform/Generated").glob(module + ".*"):
            product.unlink(missing_ok=True)


def _oracle(work, source, module, env, name):
    _run(["lake", "build", "Autoform.Runtime", "Autoform.Generated." + module], ROOT, env, 1800)
    run = work / ("run-" + name)
    run.mkdir()
    p = subprocess.run([sys.executable, str(ROOT / "scripts/differential.py"), str(work / "ast.json"),
                        str(source), module, "3", "--language", "js", "--no-cache"],
                       capture_output=True, text=True, cwd=run, env=env, timeout=1800)
    return p, json.loads((run / "conformance.json").read_text())


def test_instance_methods_agree_and_a_wrong_write_diverges(node_export):
    work, source, module, target, env = node_export
    instance = {"receivers.js::program:Gauge:" + m for m in METHODS}
    p, report = _oracle(work, source, module, env, "honest")
    assert p.returncode == 0, (p.stdout[-3000:], report.get("divergence_detail"))
    assert report["divergences"] == 0, report["divergence_detail"]
    agreed = {c["name"] for c in report["runtime_cases"] if c["comparison"] == "agree"}
    assert agreed == instance, (agreed, report["backend_skipped"], report["inconclusive_detail"])
    assert all("post_heap" in c and c["self"] == ["ref", 0] for c in report["runtime_cases"])
    assert report["by_origin"]["constructed"]["agree"] == 3 * len(instance)

    # A deliberately wrong model: `reset` writes "markex" where the source writes "marked".
    # The method returns undefined, so only the receiver's post state can catch it.
    text = target.read_text()
    reset = text.index('"receivers.js::program:Gauge:reset"')
    lit = text.index('"marked"', reset)
    target.write_text(text[:lit] + '"markex"' + text[lit + len('"marked"'):])
    p, report = _oracle(work, source, module, env, "wrong")
    diverged = {d["function"] for d in report["divergence_detail"]}
    assert diverged == {"receivers.js::program:Gauge:reset"}, (diverged, p.stdout[-3000:])
    assert all("heap graph=some false" in d["detail"] for d in report["divergence_detail"])
