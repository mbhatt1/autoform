"""Native execution adapters for the Joern conformance pipeline.

These consume exported function identities, never translate source to a second AST.
Drivers run in private copies, leaving the codebase under test untouched.
"""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import hashlib
import deep_json
import generated_module


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_fingerprints(root, funcs):
    paths = sorted({f.get("file", "") for f in funcs} - {""})
    return {p: sha256(Path(root) / p) for p in paths if (Path(root) / p).is_file()}


def semantics_fingerprints():
    root = Path(__file__).resolve().parents[1]
    return {str(p.relative_to(root)): sha256(p) for p in sorted((root / "Autoform/Lang/Core").rglob("*.lean"))}


def load_observations(report_path, ast_path, source_root, module, generated):
    """Accept runtime evidence only for these exact source/model artifacts."""
    report = deep_json.load(report_path)
    funcs = deep_json.load(ast_path)
    expected = dict(ast_sha256=sha256(ast_path),
                    generated_sha256=generated_module.model_digest(generated),
                    source_sha256=source_fingerprints(source_root, funcs),
                    semantics_sha256=semantics_fingerprints())
    if report.get("module") != module or report.get("provenance") != expected:
        raise ValueError("runtime evidence does not match the current source, AST and Lean module")
    for path, digest in report.get("backend_info", {}).get("dependencies_sha256", {}).items():
        if not Path(path).is_file() or sha256(path) != digest:
            raise ValueError("runtime header dependency does not match: " + path)
    if not report.get("build_stable") or report.get("divergences"):
        raise ValueError("runtime evidence contains a divergence or an unstable build")
    rows = report.get("runtime_cases", [])
    if not rows:
        raise ValueError("runtime evidence contains no compared observations")
    names = {f["name"] for f in funcs}
    if any(r.get("name") not in names or r.get("comparison") != "agree" for r in rows):
        raise ValueError("unattributed or non-agreeing runtime observation")
    from native_heap import validate_records
    validate_records(rows, report, funcs)
    return rows, report


def kotlin_toolchain():
    compiler = shutil.which("kotlinc")
    if compiler:
        libs = Path(compiler).resolve().parent.parent / "lib"
        jars = sorted(map(str, libs.glob("kotlin-stdlib*.jar")))
        return [compiler], [], os.pathsep.join(jars)
    joern = Path(os.environ.get("JOERN_HOME", str(Path.home() / "joern")))
    if (joern / "joern-cli").is_dir():
        joern /= "joern-cli"
    libs = joern / "frontends/kotlin2cpg/lib"
    if not shutil.which("java") or not list(libs.glob("*kotlin-compiler-embeddable*.jar")):
        return None
    runtime = os.pathsep.join(str(p) for p in sorted(libs.glob("*kotlin-stdlib*.jar"))
                             if "common" not in p.name)
    return (["java", "-cp", str(libs / "*"), "org.jetbrains.kotlin.cli.jvm.K2JVMCompiler"],
            ["-no-stdlib", "-no-reflect", "-classpath", runtime], runtime)


def compile_kotlin(src_root, candidates, work):
    """Compile private thunks beside their original declarations, using kotlinc.

    Returns actual JVM method names paired with the original CPG identities.
    Joern ships the standard Kotlin compiler; use it if no kotlinc is installed.
    """
    compiler, flags, runtime = kotlin_toolchain()
    source = Path(src_root).resolve()
    dest = Path(work) / "kotlin-source"
    copy_sources(source, dest)
    classes = Path(work) / "classes"
    classes.mkdir(exist_ok=True)
    names, skipped = {}, {}
    kt_type = dict(byte="Byte", short="Short", int="Int", long="Long", char="Char",
                   boolean="Boolean", float="Float", double="Double")
    kt_type["java.lang.String"] = "String"
    for i, (f, m, args, path) in enumerate(candidates):
        target = dest / Path(path).resolve().relative_to(source)
        code = target.read_text()
        package = re.search(r"(?m)^\s*package\s+([\w.]+)", code)
        prefix = package.group(1) + "." if package else ""
        short = f.get("sourceName", m.group("meth"))
        owner = m.group("cls")
        if owner not in (prefix.rstrip("."), "<global>", ""):
            skipped[f["name"]] = "Kotlin receiver fixture required"
            continue
        cls = "AutoformRuntime" + str(i)
        params = ", ".join("a%d: %s" % (j, kt_type[t]) for j, t in enumerate(args))
        vals = ", ".join("a%d" % j for j in range(len(args)))
        target.write_text(code + "\nobject " + cls + " {\n @JvmStatic fun invoke(" + params +
                          "): " + kt_type[m.group("ret")] + " = " + short + "(" + vals + ")\n}\n")
        names[f["name"]] = prefix + cls + ".invoke:" + m.group("ret") + "(" + ",".join(args) + ")"
    p = subprocess.run(compiler + flags + [str(dest), "-d", str(classes)],
                       capture_output=True, text=True, timeout=180)
    if p.returncode:
        return {}, {f["name"]: "kotlinc failed: " + (p.stderr + p.stdout)[-3000:]
                    for f, *_ in candidates}, runtime
    return names, skipped, runtime


def copy_sources(source, destination):
    shutil.copytree(source, destination, ignore=shutil.ignore_patterns(
        ".git", ".lake", ".venv", "node_modules", "__pycache__"))
    # Resolve installed packages without copying potentially gigabytes of dependencies.
    for modules in Path(source).rglob("node_modules"):
        rel = modules.relative_to(source)
        if "node_modules" not in rel.parts[:-1]:
            target = Path(destination) / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(modules.resolve(), target_is_directory=True)


def value(v):
    tag, data = v[0], v[1] if len(v) > 1 else None
    if tag in ("int", "float"):
        return (tag, int(data))
    if tag in ("str", "bool"):
        return (tag, data)
    if tag == "unit":
        return (tag,)
    raise ValueError("runtime value has no encoding: " + str(tag))


def records(rows, candidates, origin="native"):
    cases, skipped = [], {}
    for row in rows:
        f = candidates[row["id"]]
        if "skip" in row:
            skipped[f["name"]] = row["skip"]
            continue
        try:
            args = [value(v) for v in row["args"]]
            if "this" in f["params"]:
                args.insert(f["params"].index("this"), ("unit",))
            outcome = (("exn", row["exception"]) if "exception" in row
                       else ("val", value(row["result"])))
        except (ValueError, KeyError) as e:
            skipped[f["name"]] = str(e)
            continue
        cases.append(dict(name=f["name"], heap=[], self=None, args=args,
                          outcome=outcome, origin=origin))
    return cases, skipped


GO_DRIVER = r'''
import (
  "encoding/json"
  "fmt"
  "math"
  "reflect"
  "strings"
  "testing"
)
func autoformEncode(v reflect.Value) []interface{} {
  switch v.Kind() {
  case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
    return []interface{}{"int", fmt.Sprint(v.Int())}
  case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
    return []interface{}{"int", fmt.Sprint(v.Uint())}
  case reflect.Bool: return []interface{}{"bool", v.Bool()}
  case reflect.String: return []interface{}{"str", v.String()}
  case reflect.Float32, reflect.Float64:
    return []interface{}{"float", fmt.Sprint(math.Float64bits(v.Float()))}
  }
  panic("unsupported value type: " + v.Type().String())
}
func autoformArgument(t reflect.Type, iteration int) (reflect.Value, bool) {
  v := reflect.New(t).Elem()
  switch t.Kind() {
  case reflect.Int, reflect.Int8, reflect.Int16, reflect.Int32, reflect.Int64:
    bits := t.Bits()
    pool := []int64{0, 1, -1, int64((uint64(1) << (bits-1))-1), -int64((uint64(1) << (bits-1))-1)-1, 2, 31, 32, 63, 64}
    v.SetInt(pool[iteration % len(pool)])
  case reflect.Uint, reflect.Uint8, reflect.Uint16, reflect.Uint32, reflect.Uint64, reflect.Uintptr:
    pool := []uint64{0, 1, 2, ^uint64(0) >> (64-t.Bits()), 1 << (t.Bits()-1), 31, 32, 63, 64}
    v.SetUint(pool[iteration % len(pool)])
  case reflect.Bool: v.SetBool(iteration % 2 == 1)
  case reflect.String: v.SetString([]string{"", "a", "hello", "0", "λ"}[iteration % 5])
  case reflect.Float32, reflect.Float64:
    v.SetFloat([]float64{0, 1.5, -2.25, math.Inf(1), math.NaN()}[iteration % 5])
  default: return v, false
  }
  return v, true
}
func autoformCall(id int, fn interface{}, iteration int) (row map[string]interface{}) {
  row = map[string]interface{}{"id": id}
  defer func() {
    if e := recover(); e != nil { row["exception"] = "panic:" + strings.TrimPrefix(fmt.Sprint(e), "runtime error: ") }
  }()
  f := reflect.ValueOf(fn)
  t := f.Type()
  if t.IsVariadic() { row["skip"] = "variadic call needs argument cases"; return }
  if t.NumOut() > 1 { row["skip"] = "multiple return values"; return }
  if t.NumOut() == 1 {
    if _, ok := autoformArgument(t.Out(0), 0); !ok { row["skip"] = "return type: " + t.Out(0).String(); return }
  }
  args := []reflect.Value{}
  encoded := [][]interface{}{}
  for j := 0; j < t.NumIn(); j++ {
    v, ok := autoformArgument(t.In(j), iteration+j)
    if !ok { row["skip"] = "argument type: " + t.In(j).String(); return }
    args = append(args, v)
    encoded = append(encoded, autoformEncode(v))
  }
  row["args"] = encoded
  out := f.Call(args)
  if len(out) == 0 { row["result"] = []interface{}{"unit"} } else if len(out) == 1 {
    row["result"] = autoformEncode(out[0])
  } else { row["skip"] = "multiple return values" }
  return
}
func TestAutoformRuntime(t *testing.T) {
  rows := []map[string]interface{}{}
  __CALLS__
  b, err := json.Marshal(rows)
  if err != nil { t.Fatal(err) }
  fmt.Println("@@RESULT@@" + string(b))
}
'''


def go_backend(src_root, funcs, ncases, work):
    root = Path(src_root).resolve()
    # Preserve the containing module so local imports and replace directives work.
    module = next((p for p in [root, *root.parents] if (p / "go.mod").is_file()), root)
    dest = Path(work) / "go"
    copy_sources(module, dest)
    if not (dest / "go.mod").exists():
        (dest / "go.mod").write_text("module autoform.local/runtime\n\ngo 1.20\n")
    groups, skipped = {}, {}
    for f in funcs:
        short = f.get("sourceName", f["name"].rsplit(".", 1)[-1])
        source = root / f.get("file", "")
        if not re.fullmatch(r"[A-Za-z_]\w*", short) or short == "init":
            skipped[f["name"]] = "not a callable package function"
            continue
        if not source.is_file() or source.name.endswith("_test.go"):
            skipped[f["name"]] = "source file unavailable"
            continue
        # Joern gives methods a receiver parameter. They require a receiver fixture.
        if "this" in f["params"] or re.search(r"\([^)]*\)\.", f["name"]):
            skipped[f["name"]] = "receiver fixture required"
            continue
        groups.setdefault(source.parent, []).append((f, short))
    cases = []
    for directory, entries in groups.items():
        target = dest / directory.relative_to(module)
        source = root / entries[0][0]["file"]
        package = re.search(r"(?m)^\s*package\s+(\w+)", source.read_text()).group(1)
        calls = "\n".join(
            f"for i := 0; i < {max(1, ncases)}; i++ {{ rows = append(rows, autoformCall({idx}, {name}, i)) }}"
            for idx, (_, name) in enumerate(entries))
        (target / "autoform_runtime_test.go").write_text(
            "package " + package + "\n" + GO_DRIVER.replace("__CALLS__", calls))
        env = dict(os.environ)
        env.setdefault("GOCACHE", str(Path(work) / "go-cache"))
        r = subprocess.run(["go", "test", "-run", "^TestAutoformRuntime$", "-v", "-count=1", "-timeout=30s", "."],
                           cwd=target, env=env, capture_output=True, text=True, timeout=180)
        lines = [l[len("@@RESULT@@"):] for l in r.stdout.splitlines() if l.startswith("@@RESULT@@")]
        if r.returncode or not lines:
            for f, _ in entries:
                skipped[f["name"]] = "go test failed: " + (r.stderr + r.stdout)[-2000:]
            continue
        found, refused = records(json.loads(lines[-1]), [f for f, _ in entries])
        cases.extend(found)
        skipped.update(refused)
    return cases, {"packages": len(groups), "cases_built": len(cases)}, skipped


NODE_DRIVER = r'''
import {pathToFileURL} from 'node:url';
const targets = JSON.parse(process.argv[2]);
const rows = [];
function enc(v) {
  if (v === undefined || v === null) return ['unit'];
  if (typeof v === 'boolean') return ['bool', v];
  if (typeof v === 'string') return ['str', v];
  if (typeof v === 'bigint') return ['int', String(v)];
  if (typeof v === 'number') {
    if (Number.isSafeInteger(v) && !Object.is(v, -0)) return ['int', String(v)];
    const b = Buffer.alloc(8); b.writeDoubleBE(v); return ['float', String(b.readBigUInt64BE())];
  }
  throw Error('result type: ' + typeof v);
}
const pool = [0, 1, -1, 2147483647, 4294967296, 32, 64, -3.75, Infinity, NaN];
for (const target of targets) {
  try {
    await import(pathToFileURL(target.path).href);
  } catch (e) {
    for (const c of target.calls) rows.push({id:c.id, skip:'module load failed: ' + e.stack});
    continue;
  }
  const bindings = globalThis[Symbol.for('autoform.runtime')];
  for (const c of target.calls) {
    const fn = bindings[c.binding];
    if (typeof fn !== 'function') { rows.push({id:c.id, skip:'function not accessible at module scope'}); continue; }
    for (let i = 0; i < c.count; ++i) {
      const args = Array.from({length:c.arity}, (_, j) => pool[(i+j) % pool.length]);
      const row = {id:c.id, args:args.map(enc)};
      try {
        const result = Reflect.apply(fn, undefined, args);
        if (result && typeof result.then === 'function') row.skip = 'promise return requires async semantics';
        else row.result = enc(result);
      } catch (e) { row.exception = e?.constructor?.name || 'Error'; }
      rows.push(row);
    }
  }
}
console.log('@@RESULT@@' + JSON.stringify(rows));
'''


def node_backend(src_root, funcs, ncases, lang, work):
    root = Path(src_root).resolve()
    dest = Path(work) / "node"
    copy_sources(root, dest)
    groups, skipped, candidates = {}, {}, []
    for f in funcs:
        name = f.get("sourceName", f["name"].split(":")[-1])
        if not re.fullmatch(r"[A-Za-z_$][\w$]*", name):
            skipped[f["name"]] = "not a module-scope callable"
            continue
        path = root / f.get("file", "")
        if not path.is_file():
            skipped[f["name"]] = "source file unavailable"
            continue
        idx = len(candidates)
        candidates.append(f)
        groups.setdefault(path, []).append(dict(id=idx, binding=name, count=max(1, ncases),
            arity=len([p for p in f["params"] if p != "this"])))
    targets = []
    for path, calls in groups.items():
        target = dest / path.relative_to(root)
        bindings = ",".join(json.dumps(c["binding"]) + ": typeof " + c["binding"] +
                            " === 'undefined' ? undefined : " + c["binding"] for c in calls)
        with target.open("a") as stream:
            stream.write("\n;globalThis[Symbol.for('autoform.runtime')] = {" + bindings + "};\n")
        targets.append(dict(path=str(target), calls=calls))
    driver = Path(work) / "node_driver.mjs"
    driver.write_text(NODE_DRIVER)
    cmd = ["node"] + (["--experimental-strip-types"] if lang == "ts" else [])
    r = subprocess.run(cmd + [str(driver), json.dumps(targets)], capture_output=True, text=True, timeout=120)
    lines = [l[len("@@RESULT@@"):] for l in r.stdout.splitlines() if l.startswith("@@RESULT@@")]
    if r.returncode or not lines:
        skipped.update({f["name"]: "node driver failed: " + (r.stderr + r.stdout)[-2000:] for f in candidates})
        return [], {"cases_built": 0}, skipped
    cases, refused = records(json.loads(lines[-1]), candidates)
    skipped.update(refused)
    return cases, {"files": len(groups), "cases_built": len(cases)}, skipped
