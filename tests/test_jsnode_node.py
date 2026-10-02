"""JavaScript conformance test: `==`/`===`, `>>`/`>>>`, `??`, `null`/`undefined`, against Node.

Same chain as `test_javaintwidth_java.py`, with the one link that was missing for JS:

1. `tests/fixtures/jsnode/jsnode_cases.js` is the source; `ast.json` is what
   `cartographer/export_ast.sc` produced from it with a REAL `jssrc2cpg` 4.0.606 (Maven
   Central `io.joern:jssrc2cpg_3:4.0.606` plus its `astgen` 3.47.0 binary -- see
   `provenance.json`). Until item R no JS CPG had ever been exported by the current
   exporter: jssrc2cpg was not installed, and the token recovery for the operators it
   erases was only ever run on synthetic source spans.
2. `Autoform/JsNodeProgram.lean` is `render_lean.py` of that AST (checked byte for byte).
3. `Autoform/JsNode.lean` pins, with `#guard_msgs`, what Core computes for every `case_*`
   function; THIS file runs the same source under Node (`new Function`, every `case_*`
   called) and checks each pin against Node's value.

Value format on both sides: an integer as its decimal digits, `bool true`/`bool false`,
and a string as `str:<contents>`.

Skipped, not passed, when no `node` is on PATH.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

import pytest


ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIX = os.path.join(ROOT, "tests", "fixtures", "jsnode")
SRC = os.path.join(FIX, "jsnode_cases.js")
AST = os.path.join(FIX, "ast.json")
PROV = os.path.join(FIX, "provenance.json")
PINS = os.path.join(ROOT, "Autoform", "JsNode.lean")
PROGRAM = os.path.join(ROOT, "Autoform", "JsNodeProgram.lean")
RENDER = os.path.join(ROOT, "cartographer", "render_lean.py")

# A case Core is allowed to answer with a hole instead of Node's value, and why. EMPTY: the
# one family that needed it (`null === undefined`, both being Core's `Val.unit`) is
# answered since `Val.jsnull`. A new entry must name its reason; a pin that is a hole and
# is not listed here fails.
KNOWN_HOLES: dict = {}

NODE_RUNNER = r"""
const fs = require('fs');
const src = fs.readFileSync(process.argv[1], 'utf8');
const names = [...src.matchAll(/^function (case_\w+)\(\)/gm)].map(m => m[1]);
const f = new Function(src + '; return {' + names.join(',') + '};')();
for (const n of names) {
  const v = f[n]();
  let s;
  if (typeof v === 'boolean') s = 'bool ' + v;
  else if (typeof v === 'string') s = 'str:' + v;
  else if (Number.isInteger(v)) s = String(v);
  else s = 'other:' + String(v);
  console.log(n + '\t' + s);
}
"""


def pinned_results() -> dict:
    text = open(PINS).read()
    pat = re.compile(r'/-- info: "([^"]*)" -/\s*\n#guard_msgs in #eval jRun "(case_\w+)"')
    return {m.group(2): m.group(1) for m in pat.finditer(text)}


def declared_cases() -> list:
    return re.findall(r"^function (case_\w+)\(\)", open(SRC).read(), re.M)


@pytest.fixture(scope="module")
def node_results():
    if shutil.which("node") is None:
        pytest.skip("no node on PATH")
    r = subprocess.run(["node", "-e", NODE_RUNNER, SRC], check=True,
                       capture_output=True, text=True)
    return dict(line.split("\t", 1) for line in r.stdout.splitlines())


def test_every_case_is_pinned_and_agrees_with_node(node_results):
    declared = declared_cases()
    assert declared and set(node_results) == set(declared)
    pins = pinned_results()
    assert set(pins) == set(declared), (
        f"cases without a pin: {sorted(set(declared) - set(pins))}; "
        f"pins without a case: {sorted(set(pins) - set(declared))}")
    wrong = {}
    for case, expected in node_results.items():
        got = pins[case]
        if got == expected:
            continue
        if got.startswith("hole ") and KNOWN_HOLES.get(case) == got[len("hole "):]:
            continue
        wrong[case] = (expected, got)
    assert not wrong, "Core disagrees with Node (node, core): " + json.dumps(wrong, indent=1)


def test_known_holes_are_still_holes():
    # An allowlist entry for a case Core now answers is stale and hides a regression.
    pins = pinned_results()
    for case, label in KNOWN_HOLES.items():
        assert pins.get(case) == "hole " + label, case


def test_ast_was_exported_from_this_source():
    prov = json.load(open(PROV))
    assert prov["source_sha256"] == hashlib.sha256(open(SRC, "rb").read()).hexdigest(), (
        "jsnode_cases.js changed since ast.json was exported; re-run the command in "
        "tests/fixtures/jsnode/provenance.json")
    assert prov["ast_sha256"] == hashlib.sha256(open(AST, "rb").read()).hexdigest()


def test_ast_is_hole_free():
    # A hole in the export would make the comparison above vacuous for that case.
    assert '"hole' not in open(AST).read()


def test_ast_has_the_recovered_tokens():
    # The six operators jssrc2cpg folds into three. Every spelling must come out of the
    # REAL CPG; this is the check that was never run before item R.
    text = open(AST).read()
    ops = set(re.findall(r'"op":\s*"([^"]+)"', text))
    for op in ("===", "!==", "==", "!=", ">>", ">>>", "<<"):
        assert op in ops, op
    # `??` is not a Core operator: it is lowered, so no `||` appears in a `??` case...
    ast = {m["name"].rsplit(":", 1)[-1]: m for m in json.load(open(AST))}
    for name in ("case_nullish_zero", "case_nullish_empty", "case_nullish_false",
                 "case_nullish_null", "case_nullish_value", "case_nullish_in_cond"):
        body = json.dumps(ast[name]["body"])
        assert '"cond"' in body and '"||"' not in body, name
    # ...while a genuine `||` is still `||`.
    assert '"||"' in json.dumps(ast["case_or_zero"]["body"])
    # `null` and `undefined` are different literals.
    assert '"jsnull"' in text and '"k": "unit"' in text


def test_program_is_the_render_of_the_ast(tmp_path):
    out = tmp_path / "JsNodeProgram.lean"
    r = subprocess.run([sys.executable, RENDER, AST, str(out), "JsNode"],
                       capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    assert out.read_text() == open(PROGRAM).read(), (
        "Autoform/JsNodeProgram.lean is not the render of tests/fixtures/jsnode/ast.json")


def test_fixture_is_plain_function_declarations():
    # `new Function(src + ...)` in the Node leg evaluates the whole file; keep it a list of
    # declarations so the Core leg (which only looks the cases up) and Node see one program.
    body = re.sub(r"//[^\n]*", "", open(SRC).read())
    depth, top = 0, []
    for line in body.splitlines():
        if depth == 0 and line.strip() and not line.startswith("function "):
            top.append(line)
        depth += line.count("{") - line.count("}")
    assert not top, top
