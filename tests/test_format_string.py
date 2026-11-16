"""Template literals (JS/TS) and string templates (Kotlin) against the real runtimes.

`<operator>.formatString` was the hole `op:formatString` outside Python. The exporter now
lowers it to a left fold of a dialect-specific append (`js:tpl`, `kt:tpl`,
`kt:tpl:integral`; `Semantics.languageBinop`), which converts each part the way the
source language does and is a NAMED hole where Core cannot reproduce that conversion.

Two kinds of check:

1. Always: the Lean side's `#guard`s are elaborated by `lake build` (Semantics.lean), and
   the exporter/Core wiring is asserted on the sources.
2. `AUTOFORM_TEST_JOERN=1` (plus Node / kotlinc): a fixture per language goes through
   joern-parse, `export_ast.sc` and `render_lean.py`, and every case is run by Lean
   (`runFunc`) and by the real runtime from the same arguments. A case is either
   compared (the UTF-8 bytes must be equal) or expected to be refused, and then the
   model must answer exactly the named hole -- never a different string. Nothing else
   passes.
"""
from __future__ import annotations

import json
import os
import shutil
import struct
import subprocess
import sys
from pathlib import Path

import pytest
from conftest import exporter_source

ROOT = Path(__file__).resolve().parents[1]
SEMANTICS = ROOT / "Autoform" / "Lang" / "Core" / "Semantics.lean"


def run(args, cwd, env, timeout=600):
    p = subprocess.run(list(map(str, args)), cwd=cwd, env=env, text=True,
                       capture_output=True, timeout=timeout)
    assert p.returncode == 0, p.stdout + p.stderr
    return p.stdout


# ------------------------------------------------------------------ static wiring

def test_exporter_lowers_templates_only_for_their_own_languages():
    src = exporter_source()
    assert 'mfn == "<operator>.formatString" && jsLikeFile) jsTemplate(kids)' in src
    assert 'mfn == "<operator>.formatString" && kotlinFile) ktTemplate(c, kids)' in src
    # Python keeps its own f-string lowering, ahead of both.
    assert src.index('&& pyFile) fstring(kids)') < src.index('&& jsLikeFile) jsTemplate(kids)')
    # A Kotlin Char is a code point in Core: never the integral arm.
    assert 'lazy val ktCharTypes = Set("char", "java.lang.Character", "kotlin.Char")' in src
    assert '"char"' not in src.split("lazy val ktIntegralTypes", 1)[1].split("lazy val ktCharTypes", 1)[0]


def test_core_template_arms_are_dialect_gated_and_named():
    text = SEMANTICS.read_text()
    head = text.split("def languageBinop", 1)[1].split("def javaFloatToIntegral", 1)[0]
    assert '| "js:tpl", .str s, x => match d with' in head
    assert '| .javascript => templateAppend s (jsTemplateString x)' in head
    assert '| .java => templateAppend s (ktTemplateString false x)' in head
    assert '| .java => templateAppend s (ktTemplateString true x)' in head
    assert '.hole "op:formatString:accumulator"' in head
    assert 'templateAppend (acc : String) : Except String String → EResult' in text
    assert '| .error r => .hole s!"op:formatString:{r}"' in text
    # The conversions refuse what Core cannot spell exactly.
    for label in ("js-float", "js-nullish", "js-object", "js-number-exponent",
                  "kt-float", "kt-null", "kt-object", "kt-int-or-char"):
        assert f'.error "{label}"' in text, label


# ------------------------------------------------------------------ differential

TS = r'''export function stepName(prefix: string, step: string): string { return `${prefix}-${step}-ApprovalWorkflowStep`; }
export function arn(region: string, account: string, role: string): string { return `arn:aws:iam:${region}:${account}:role/${role}`; }
export function escapes(a: string): string { return `tab\there\nnl \\ bs \` tick \${notsub} "dq" 'sq' \x41é\u{1F600} ${a}`; }
export function counted(n: number): string { return `n=${n}`; }
export function flag(b: boolean): string { return `b=${b}`; }
export function nested(a: string, b: boolean): string { return `<${b ? `y${a}` : "n"}>`; }
export function multi(a: string): string { return `line1
line2 ${a}`; }
export function noSub(): string { return `just text`; }
'''

# (function, args, expected): expected None = compare with Node; a string = the model
# must refuse with exactly this hole label (Node's answer is printed, not compared).
TS_CASES = [
    ("stepName", [("str", "Prod"), ("str", "Deploy")], None),
    ("arn", [("str", "us-east-1"), ("str", "123456789012"), ("str", "Admin")], None),
    ("arn", [("str", ""), ("str", ""), ("str", "")], None),
    ("escapes", [("str", "x")], None),
    ("counted", [("int", 7)], None),
    ("counted", [("int", -3)], None),
    ("counted", [("int", 0)], None),
    ("counted", [("float", 1.5)], "op:formatString:js-float"),
    ("flag", [("bool", True)], None),
    ("flag", [("bool", False)], None),
    ("nested", [("str", "a"), ("bool", True)], None),
    ("nested", [("str", "a"), ("bool", False)], None),
    ("multi", [("str", "z")], None),
    ("noSub", [], None),
]

KT = r'''package fs
fun withPrefix(a: String): String = "PREFIX_$a"
fun plain(a: String, b: String): String = "$a-$b"
fun esc(a: String): String = "tab\there\nnl \\ bs \$notvar \"dq\" é ${a}"
fun dollar(a: String): String = "cost $5 and $ alone $a"
fun raw(a: String): String = """raw \n ${'$'}x $a"""
fun intPart(n: Int): String = "n=$n"
fun longPart(n: Long): String = "n=${n}"
fun boolPart(b: Boolean): String = "b=$b"
fun dotted(a: String, b: String): String = "$a.$b"
fun nested(a: String, b: Boolean): String = "<${if (b) "y$a" else "n"}>"
fun dbl(d: Double): String = "d=$d"
'''

KT_CASES = [
    ("withPrefix", [("str", "abc")], None),
    ("plain", [("str", "a"), ("str", "b")], None),
    ("esc", [("str", "q")], None),
    ("dollar", [("str", "z")], None),
    ("raw", [("str", "r")], None),
    ("intPart", [("int", -12)], None),
    ("intPart", [("int", 2147483647)], None),
    ("longPart", [("int", -9223372036854775808)], None),
    ("boolPart", [("bool", True)], None),
    ("dotted", [("str", "x"), ("str", "y")], None),
    ("nested", [("str", "a"), ("bool", True)], None),
    ("nested", [("str", "a"), ("bool", False)], None),
    ("dbl", [("float", 0.1)], "op:formatString:kt-float"),
]


def lean_val(a):
    kind, v = a
    if kind == "str":
        return ".str " + json.dumps(v)
    if kind == "bool":
        return ".bool " + ("true" if v else "false")
    if kind == "float":
        return f".float (Fl.ofBits {struct.unpack('>Q', struct.pack('>d', v))[0]})"
    return f".int ({v})"


def js_val(a):
    kind, v = a
    return json.dumps(v) if kind in ("str", "bool", "float", "int") else "undefined"


def kt_val(a):
    kind, v = a
    if kind == "str":
        return json.dumps(v)
    if kind == "bool":
        return "true" if v else "false"
    if kind == "float":
        return repr(v)
    if v == -9223372036854775808:
        return "Long.MIN_VALUE"
    return str(v)


LEAN_DRIVER = '''
def hx (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b =>
    let d := Nat.toDigits 16 b.toNat
    String.ofList (if d.length < 2 then '0' :: d else d))
def showR (r : EResult) : String :=
  match r with
  | .val (.str s) => "str " ++ hx s
  | .hole l       => "hole " ++ l
  | _             => "other"
'''


def model_results(tmp_path, env, ast, cases, resolve):
    functions = json.loads(ast.read_text())
    model = tmp_path / "Model.lean"
    run([sys.executable, ROOT / "cartographer/render_lean.py", ast, model, "Tpl"], ROOT, env)
    driver = model.read_text() + "\nopen Autoform.Core Autoform.Generated.Tpl\n" + LEAN_DRIVER
    driver += "def main : IO Unit := do\n"
    for name, args, _ in cases:
        f = resolve(functions, name)
        values = [lean_val(a) for a in args]
        if f["params"][:1] == ["this"]:
            values.insert(0, ".unit")
        assert len(values) == len(f["params"]), (name, f["params"])
        driver += f'  IO.println (showR (runFunc program 400 {json.dumps(f["name"])} [{", ".join(values)}]))\n'
    (tmp_path / "Check.lean").write_text(driver)
    return run(["lake", "env", "lean", "--run", tmp_path / "Check.lean"], ROOT, env).splitlines()


def compare(cases, model, native):
    assert len(model) == len(native) == len(cases), (model, native)
    compared = refused = 0
    for (name, args, expected), m, n in zip(cases, model, native):
        if expected is None:
            assert m == "str " + n, f"{name}{args}: model {m!r}, runtime str {n!r}"
            compared += 1
        else:
            assert m == "hole " + expected, f"{name}{args}: expected refusal {expected}, model {m!r}"
            refused += 1
    return compared, refused


def joern_cli():
    home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    return home / "joern-cli" if (home / "joern-cli").is_dir() else home


@pytest.fixture(scope="module")
def env():
    if not os.environ.get("AUTOFORM_TEST_JOERN"):
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to parse/export and compare native runtimes")
    e = {k: os.environ[k] for k in ("PATH", "HOME", "LANG", "LC_ALL", "TMPDIR", "JAVA_HOME")
         if k in os.environ}
    e["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + e.get("PATH", "")
    if not shutil.which("lake", path=e["PATH"]):
        pytest.skip("Lean is not installed")
    if not (joern_cli() / "joern").is_file():
        pytest.skip("Joern is not installed (JOERN_HOME)")
    run(["lake", "build", "Autoform.Lang.Core.Semantics"], ROOT, e)
    return e


def export(tmp_path, env, language):
    run([joern_cli() / "joern-parse", tmp_path / "src", "--language", language, "--output", "cpg.bin"],
        tmp_path, env)
    run([joern_cli() / "joern", "--script", ROOT / "cartographer/export_ast.sc",
         "--param", "cpgPath=cpg.bin", "--param", "out=ast.json", "--param", "dataModel=lp64"],
        tmp_path, env)
    return tmp_path / "ast.json"


def labels(node, out):
    if isinstance(node, dict):
        if node.get("k") == "hole":
            out.append(node["label"])
        for v in node.values():
            labels(v, out)
    elif isinstance(node, list):
        for v in node:
            labels(v, out)
    return out


def test_ts_template_literals_against_node(tmp_path, env):
    if not shutil.which("node", path=env["PATH"]):
        pytest.skip("Node runtime unavailable")
    (tmp_path / "src").mkdir()
    (tmp_path / "src" / "fs.ts").write_text(TS)
    ast = export(tmp_path, env, "jssrc")
    functions = json.loads(ast.read_text())
    assert not [l for f in functions for l in labels(f["body"], []) if l.startswith("op:formatString")]

    def resolve(fs, name):
        hits = [f for f in fs if f["name"] == f"fs.ts::program:{name}"]
        assert len(hits) == 1, (name, [f["name"] for f in fs])
        return hits[0]
    model = model_results(tmp_path, env, ast, TS_CASES, resolve)
    # Node runs the same file (type annotations stripped by Node itself).
    runner = tmp_path / "run.mjs"
    runner.write_text("import * as m from './src/fs.ts';\n" + "".join(
        f"console.log(Buffer.from(m.{n}({', '.join(map(js_val, a))}), 'utf8').toString('hex'));\n"
        for n, a, _ in TS_CASES))
    native = run(["node", "--experimental-strip-types", "--no-warnings", runner], tmp_path, env).splitlines()
    compared, refused = compare(TS_CASES, model, native)
    assert compared == 13 and refused == 1


def test_kotlin_string_templates_against_the_jvm(tmp_path, env):
    if not (shutil.which("kotlinc", path=env["PATH"]) and shutil.which("java", path=env["PATH"])):
        pytest.skip("kotlinc/java unavailable")
    (tmp_path / "src").mkdir()
    (tmp_path / "src" / "Fs.kt").write_text(KT)
    ast = export(tmp_path, env, "kotlin")
    functions = json.loads(ast.read_text())
    assert not [l for f in functions for l in labels(f["body"], []) if l.startswith("op:formatString")]

    def resolve(fs, name):
        hits = [f for f in fs if f["name"].startswith(f"fs.{name}:")]
        assert len(hits) == 1, (name, [f["name"] for f in fs])
        return hits[0]
    model = model_results(tmp_path, env, ast, KT_CASES, resolve)
    (tmp_path / "Main.kt").write_text(
        "import fs.*\nfun hx(s: String) = s.toByteArray(Charsets.UTF_8).joinToString(\"\") { \"%02x\".format(it) }\n"
        "fun main() {\n" + "".join(f"  println(hx({n}({', '.join(map(kt_val, a))})))\n" for n, a, _ in KT_CASES)
        + "}\n")
    run(["kotlinc", tmp_path / "src" / "Fs.kt", tmp_path / "Main.kt", "-include-runtime", "-d", tmp_path / "t.jar"],
        tmp_path, env)
    native = run(["java", "-jar", tmp_path / "t.jar"], tmp_path, env).splitlines()
    compared, refused = compare(KT_CASES, model, native)
    assert compared == 12 and refused == 1
