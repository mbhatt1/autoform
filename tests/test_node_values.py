"""JavaScript arrays, plain objects and module constants through the whole Node oracle.

A TypeScript fixture goes through Joern, the exporter (`SourceCompiler.jsLiteral` folds
`[a, b]` and `{k: v}` to `Expr.listE`/`Expr.dictE`), `render_lean.py`, `lake build` and
`scripts/differential.py` against Node. Every function returns an array or an object --
which the Node driver refused before (`unusable result: no encoding for a value of type
array`) -- and several read a module-level `const`, which Core is given in its globals
frame as Node reports it immediately before the call (`node_reads`). Every case must be
compared and must agree; the shapes Core's literals cannot reproduce are refused by name.

Needs Joern, Node and Lean: set `AUTOFORM_TEST_JOERN=1` (or `AUTOFORM_TEST_ORACLES=1`).
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

SOURCE = '''export const PROD_ARN = "arn:prod:*";
export const DOGFOOD_ARN = "arn:dogfood:*";
const STAGES = ["alpha", "beta"];
const TAG = { key: "team", value: "core" };

export function arns(stage: string): string[] {
  return stage === "prod" ? [PROD_ARN] : [DOGFOOD_ARN, stage];
}
export function tag(stage: string): { key: string; value: string; n: number } {
  return { key: "k", value: stage, n: 2 };
}
export function nested(stage: string) {
  return { list: [stage, 1], inner: { v: stage }, none: null };
}
export function stages(stage: string): string[] {
  return STAGES;
}
export function tagged(stage: string) {
  return { tag: TAG, stage: stage };
}
export function grown(stage: string): string[] {
  const xs = [stage];
  xs.push("x");
  return xs;
}
export function sizes(stage: string): number[] {
  return [STAGES.length, 3];
}
'''
FUNCTIONS = ("arns", "tag", "nested", "stages", "tagged", "grown", "sizes")


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
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to run the Node value oracle end to end")
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
    (source / "values.ts").write_text(SOURCE)
    _run([joern / "joern-parse", source, "--language", "JSSRC", "--output", "cpg.bin"],
         tmp_path, env)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=cpg.bin", "--param", "out=ast.json"], tmp_path, env)
    module = "NodeValuesFixture"
    target = GENERATED / (module + ".lean")
    try:
        _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp_path / "ast.json",
              target, module], ROOT, env)
        yield tmp_path, source, module, env
    finally:
        target.unlink(missing_ok=True)
        for product in (ROOT / ".lake/build/lib/lean/Autoform/Generated").glob(module + ".*"):
            product.unlink(missing_ok=True)


def test_literals_fold_to_listE_and_dictE(node_export):
    work, _, _, _ = node_export
    funcs = {f["name"].split(":")[-1]: f for f in json.loads((work / "ast.json").read_text())}
    body = json.dumps(funcs["arns"]["body"])
    assert '"listE"' in body and "hole" not in body, body
    tag = json.dumps(funcs["tag"]["body"])
    assert '"dictE"' in tag and "setField" not in tag, tag
    # The synthesised `push` no longer carries its METHOD_REF as an argument.
    assert "__ecma.Array:push" not in json.dumps(list(funcs.values()))


def test_arrays_objects_and_module_constants_agree_with_node(node_export):
    work, source, module, env = node_export
    _run(["lake", "build", "Autoform.Runtime", "Autoform.Generated." + module], ROOT, env, 1800)
    run = work / "run"
    run.mkdir()
    p = subprocess.run([sys.executable, str(ROOT / "scripts/differential.py"), str(work / "ast.json"),
                        str(source), module, "4", "--language", "ts"],
                       capture_output=True, text=True, cwd=run, env=env, timeout=1800)
    report = json.loads((run / "conformance.json").read_text())
    assert p.returncode == 0, (p.stdout[-3000:], report.get("divergence_detail"))
    assert report["measurement_basis"] == "node-numeric-pool-v2"
    assert report["divergences"] == 0, report["divergence_detail"]
    compared = {c["name"].split(":")[-1] for c in report["runtime_cases"]}
    assert compared >= set(FUNCTIONS), (compared, report["backend_skipped"],
                                        report["inconclusive_detail"])
    assert all(c["comparison"] == "agree" for c in report["runtime_cases"])
    # Module constants were handed to Core, not read as `undefined`.
    assert report["agree"] >= 4 * len(FUNCTIONS)
