"""Native execution adapters for the Joern conformance pipeline.

These consume exported function identities, never translate source to a second AST.
Drivers run in private copies, leaving the codebase under test untouched.
"""
from pathlib import Path
import collections
import json
import os
import re
import shutil
import subprocess
import hashlib
import deep_json
import generated_module
import sandbox


# The language of a source file, by extension, for every backend `differential.py`
# dispatches to (its `detect_language`); an extension not in it is refused, never defaulted.
LANG_BY_EXT = {".py": "python", ".pyi": "python",
               ".c": "c", ".h": "c",
               ".cpp": "c", ".cc": "c", ".cxx": "c", ".hh": "c", ".hpp": "c",
               ".java": "java", ".go": "go",
               ".js": "js", ".mjs": "js", ".cjs": "js", ".jsx": "js",
               ".ts": "ts", ".tsx": "ts", ".mts": "ts", ".cts": "ts",
               ".kt": "kotlin", ".kts": "kotlin"}

# The executables each language's runtime backend needs on PATH (Kotlin: `kotlin_toolchain`).
TOOLCHAIN = {"python": [], "c": ["cc"], "cpp": ["c++"], "java": ["javac", "java"], "go": ["go"],
             "js": ["node"], "ts": ["node"], "kotlin": ["kotlinc"]}

# Languages whose backend `pr` mode's cross-revision comparison (`pr_mode.py` `run_behaviour`)
# may run: the base revision's model against the head revision's runtime. A backend belongs
# here only when the cases it builds come from the exported function alone (its signature,
# its body's literals, a fixed seed) or, for Python, from the head's tests overlaid on the
# base, so the model and the runtime are handed the same inputs from the same state. The
# value says what the inputs are, for the report. A backend joins by adding its language
# here; `pr_mode.py` reads nothing else.
CROSS_REVISION_INPUTS = {
    "python": "head tests + random cases + strings from the code's literals",
    "java": "seeded random inputs (java_backend), strings from the code's literals",
    "kotlin": "seeded random inputs (java_backend), strings from the code's literals",
    "go": "fixed per-type input pools (go_backend)",
    "js": "fixed numeric pool and strings from the code's literals (node_backend)",
    "ts": "fixed numeric pool and strings from the code's literals (node_backend)",
    # `.c` units only in pr mode (`pr_mode.source_language`): a `.h` is shared with C++.
    "c": "seeded typed-boundary inputs and literal neighbours (native C oracle)",
    # C++ sources, and `.h` in a C++ corpus (`pr_mode.function_language`): the same native
    # oracle (`differential.py` runs them as `c`), called through C ABI thunks by
    # qualified name. A pr-only label: `LANG_BY_EXT` maps C++ extensions to `c`.
    "cpp": "seeded random and width-boundary inputs (native_c, C ABI thunks)",
}


def missing_toolchain(lang):
    """The tools `lang`'s backend needs that are not on PATH (empty when it can run)."""
    if lang == "kotlin":
        return [] if kotlin_toolchain() and shutil.which("javac") else ["Kotlin JVM compiler and JDK"]
    return [tool for tool in TOOLCHAIN.get(lang, []) if not shutil.which(tool)]


def cross_revision_unavailable(lang):
    """None when the cross-revision comparison can run `lang` on this machine (a backend in
    CROSS_REVISION_INPUTS and its toolchain on PATH), else the reason it cannot."""
    if lang not in CROSS_REVISION_INPUTS:
        return ("no cross-revision runtime backend for %s (the comparison covers %s)"
                % ("this language" if lang in (None, "other") else lang + " functions",
                   ", ".join(sorted(CROSS_REVISION_INPUTS))))
    missing = missing_toolchain(lang)
    if missing:
        return ("%s function: %s not on PATH, so its runtime backend cannot run"
                % (lang, ", ".join(missing)))
    return None


# String arguments shared by the JVM and Node drivers.
STRING_POOL = ["", "0", "11", "1.8.0_281", "17.0.1", "java.lang.String",
               "android.os.Bundle", "com.example.Foo"]

# `--literal-inputs` (differential.py): string and integer inputs mined from the code under
# test. A fixed pool and small random integers cannot reach a branch that tests a string
# against a constant: measured on a seeded `or` -> `and` regression in a function that
# returns early unless both node names contain ':', where 122 cases (the suite's 22 and 100
# random integers) never put a ':' in exactly one argument and the change passed. The
# constants a function compares against, splits on and prefix-tests are in its own body
# and its file, so they are taken from the exported AST: the same export is handed to the
# cross-revision run and its same-base control, so both draw identical inputs.
LITERAL_INPUTS_BASIS = "literal-inputs-v1"
MAX_MINED_LITERALS = 16
MAX_STRING_INPUTS = 64
GO_DRIVER_TIMEOUT = 180     # seconds for one `go test` driver run (per package)
NODE_DRIVER_TIMEOUT = 120   # seconds for one node driver run over every candidate


def output_tail(data, limit=2000):
    """The last `limit` characters of a subprocess stream, for a report. `data` is what
    `CompletedProcess` or `TimeoutExpired` carries: str, bytes (a killed process's partial
    output is bytes even in text mode) or None."""
    if data is None:
        return ""
    if isinstance(data, bytes):
        data = data.decode("utf-8", "replace")
    return data[-limit:]


def _mined(node, strings, ints):
    """String and integer literals of one exported body, in source order. A bare string
    statement (a docstring) is documentation, not a value the code compares against."""
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            k = n.get("k")
            if k == "exprS" and isinstance(n.get("e"), dict) and n["e"].get("k") == "str":
                continue
            if k == "tryCatch":
                # A handler's test of the caught exception against class names (`except
                # Exception` lowers to `x in ("ArithmeticError", ...)`) names types, not
                # values the code compares its inputs with.
                handler, parts = n.get("handler"), [n.get("body")]
                while isinstance(handler, dict) and handler.get("k") == "ifte":
                    test = handler.get("c") or {}
                    if not (test.get("k") == "inOp" and (test.get("a") or {}).get("v") == n.get("x")):
                        break
                    parts.append(handler.get("t"))
                    handler = handler.get("e")
                parts += [handler] + [v for key, v in n.items()
                                      if key not in ("k", "body", "handler", "x")]
                stack.extend(reversed(parts))
                continue
            if k == "str" and isinstance(n.get("v"), str):
                strings.append(n["v"])
            elif k == "int":
                # KNOWN DEFECT, deliberately NOT fixed here: `int()` reads decimal only,
                # so a hex/octal/binary or underscore-separated literal the exporter
                # passes through verbatim (`0xFF`, `1_000`) is dropped silently and its
                # neighbours are never drawn. Reading them adds inputs to every
                # `--literal-inputs` run that has one: needs a basis bump to
                # literal-inputs-v2 and re-measurement.
                try:
                    ints.append(int(n.get("v")))
                except (TypeError, ValueError):
                    pass
            stack.extend(reversed(list(n.values())))
        elif isinstance(n, list):
            stack.extend(reversed(n))


def utf8_encodable(s):
    """Whether `s` is a sequence of Unicode scalar values (no lone surrogate). A Lean
    `String` cannot hold anything else, and `str.encode()` raises on it."""
    try:
        s.encode("utf-8")
    except UnicodeEncodeError:
        return False
    return True


def mined_literals(f, funcs=(), extra=(), stats=None):
    """`(strings, ints)` mined for `f`: its own body's literals first, then `extra` (pr
    mode's head-revision literals of the same function), then the rest of its file's.

    A string literal holding a lone surrogate (an exporter can emit one from a `\\uD83D`
    escape in the source) is dropped and counted in `stats["literals_unencodable"]` when
    a `stats` dict is given: the JVM planner base64-encodes each drawn string with
    `str.encode()`, which raised UnicodeEncodeError and killed the run, and no runtime
    backend can hand Core a string Lean cannot represent. For a literal set WITHOUT
    surrogates the result is byte-identical to before (the filter removes nothing and the
    cap is applied to the same sequence), so the inputs drawn under the recorded
    `literal-inputs-v1` basis are unchanged -- CommonsLang3's literal set has none."""
    strings, ints = [], []
    _mined(f.get("body"), strings, ints)
    strings += [s for s in extra if isinstance(s, str)]
    for g in funcs:
        if g is not f and g.get("file") == f.get("file") and g.get("file"):
            _mined(g.get("body"), strings, ints)
    short = [s for s in dict.fromkeys(strings) if len(s) <= 64]
    keep = [s for s in short if utf8_encodable(s)]
    if stats is not None:
        stats["literals_unencodable"] = stats.get("literals_unencodable", 0) + len(short) - len(keep)
    return keep[:MAX_MINED_LITERALS], list(dict.fromkeys(ints))[:MAX_MINED_LITERALS]


def string_inputs(literals, cap=MAX_STRING_INPUTS):
    """Strings built from mined literals: each literal alone (a compared constant), with
    text around it (a separator `a:b` that splits, a prefix or a suffix that
    `startswith`/`endswith` accept), doubled, and joined pairwise (`hub` + `:`)."""
    out = ["", "x"]
    lits = [s for s in literals if s]
    for s in lits:
        out += [s, "a" + s + "b", s + "a", "a" + s, s + s]
    # KNOWN DEFECT, deliberately NOT fixed here: the per-literal block above adds 5 strings
    # each, so with 13 or more non-empty literals (2 + 5*13 = 67 > MAX_STRING_INPUTS) the
    # cap below cuts the list before ANY pairwise join is reached, and `hub` + `:`-style
    # inputs are never drawn for the richest literal sets. Reordering or widening changes
    # the string pool of every recorded run: needs a basis bump to literal-inputs-v2 and
    # re-measurement.
    for i, s in enumerate(lits[:6]):
        for t in lits[:6]:
            if s != t:
                out += [s + t, s + t + "a"]
    return list(dict.fromkeys(out))[:cap]


def integer_inputs(ints):
    """Each mined integer and its neighbours: a compared constant's boundary."""
    return list(dict.fromkeys(v + d for v in ints for d in (0, -1, 1)))


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
        # The distribution keeps its jars in `<home>/lib`; Homebrew's `bin/kotlinc` is a
        # wrapper script whose distribution lives under `<home>/libexec`. Without the
        # stdlib on the runtime classpath every compiled call that reaches
        # `kotlin.jvm.internal.Intrinsics` (any non-null reference parameter) failed
        # with NoClassDefFoundError.
        home = Path(compiler).resolve().parent.parent
        jars = sorted(str(p) for libs in (home / "lib", home / "libexec" / "lib")
                      for p in libs.glob("kotlin-stdlib*.jar") if not p.name.endswith("-sources.jar"))
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


def is_test_source(rel):
    """True for a path inside a test source set: `src/test*`, `src/*Test*`, any `test/`
    or `tests/` directory, or a file named `*Test.kt` / `*Tests.kt`.

    Test sources need the test classpath (mockk, junit), which the oracle is not given;
    compiling them with the main sources made one `unresolved reference: mockk` fail
    every candidate in the tree."""
    parts = Path(rel).parts
    for i, part in enumerate(parts[:-1]):
        if part in ("test", "tests"):
            return True
        if i and parts[i - 1] == "src" and (part.startswith("test") or "Test" in part):
            return True
    return bool(re.search(r"Tests?\.kt$", parts[-1])) if parts else False


KOTLINC_ERROR = re.compile(r"^(?P<path>\S[^:\n]*\.(?:kt|kts|java)):\d+:\d+: error: (?P<msg>.*)$",
                           re.MULTILINE)


def kotlinc_errors(output, root, cwd=None):
    """`(file relative to root, message)` for each kotlinc error, in the order reported.

    kotlinc prints a path relative to its working directory `cwd` when it can."""
    found = []
    for m in KOTLINC_ERROR.finditer(output):
        path = Path(m.group("path"))
        if cwd and not path.is_absolute():
            path = Path(cwd) / path
        try:
            path = path.resolve().relative_to(Path(root).resolve())
        except (ValueError, OSError):
            pass
        found.append((str(path), m.group("msg").strip()))
    return found


def kotlinc_failure_category(message):
    """Bucket one kotlinc error, as `java_failure_category` does for javac."""
    if "unresolved reference" in message.lower():
        return "unresolved reference (missing classpath or source)"
    if "cannot access" in message.lower():
        return "unreadable dependency"
    return "other kotlinc error"


_KT_COMMENT = re.compile(r"//[^\n]*|/\*.*?\*/", re.S)
_KT_PACKAGE = re.compile(r"(?m)^\s*package\s+([\w.]+)")
_KT_IMPORT = re.compile(r"(?m)^\s*import\s+(\w+(?:\.\w+)*)(\.\*)?")
# A top-level declaration: at column 0, after any modifiers; an extension's name is the
# part after its receiver type (`fun Foo.bar(`, `val String.baz`).
_KT_TOP_DECL = re.compile(
    r"(?m)^(?:(?:public|internal|private|protected|abstract|open|sealed|data|enum|annotation|"
    r"inline|value|const|lateinit|suspend|tailrec|operator|infix|external|expect|actual|fun)\s+)*"
    r"(?:class|interface|object|typealias|fun|val|var)\s+(?:<[^>\n]*>\s*)?"
    r"(?:[\w.]+(?:<[^>\n]*>)?\??\.)?(\w+)")
_KT_WORD = re.compile(r"[A-Za-z_]\w*")


def kotlin_reference_closure(seeds, pool):
    """The files of `pool` that the files `seeds` reference, transitively, with the seeds.

    A reference is resolved by package and simple name, the way Kotlin resolves it
    (Kotlin spec, "Declarations" / "Packages and imports"): an explicit import `p.N` (or
    `p.N.Inner`) names the files of package `p` that declare `N` at top level; a star
    import `p.*`, and a fully qualified `p.N` in code, the same; and a name used in a file
    without an import resolves first in that file's own package, so a word of a file that
    is a top-level declaration of another file of the same package names that file.
    Top-level declarations are read at column 0; a Java file declares its file name. A
    name that resolves nowhere (a dependency's) adds nothing. Over-approximate by
    design: the closure only decides which sources kotlinc is given, and a file too many
    is compiled, never run, while a file too few fails the whole attempt."""
    seeds = [Path(p) for p in seeds]
    files = list(dict.fromkeys(seeds + [Path(p) for p in pool]))
    text, package = {}, {}
    declares = collections.defaultdict(set)    # (package, name) -> files
    by_package = collections.defaultdict(set)
    for path in files:
        try:
            raw = path.read_text(errors="replace")
        except OSError:
            continue
        code = _KT_COMMENT.sub(" ", raw)
        text[path] = code
        m = _KT_PACKAGE.search(code)
        package[path] = m.group(1) if m else ""
        by_package[package[path]].add(path)
        names = {path.stem} if path.suffix == ".java" else set(_KT_TOP_DECL.findall(code))
        for name in names:
            declares[(package[path], name)].add(path)
    packages = sorted((p for p in by_package if p), key=len, reverse=True)

    def references(path):
        code, own = text.get(path, ""), package.get(path, "")
        found = set()
        for name, star in _KT_IMPORT.findall(code):
            if star:
                found |= by_package.get(name, set())
                continue
            parts = name.split(".")
            for i in range(len(parts) - 1, 0, -1):   # `p.N` or `p.N.Inner`
                hit = declares.get((".".join(parts[:i]), parts[i]))
                if hit:
                    found |= hit
                    break
        words = set(_KT_WORD.findall(code))
        for word in words:
            found |= declares.get((own, word), set())
        for pkg in packages:
            if pkg + "." in code:
                for m in re.finditer(re.escape(pkg) + r"\.(\w+)", code):
                    found |= declares.get((pkg, m.group(1)), set())
        return found

    closure, queue = list(seeds), list(seeds)
    seen = set(seeds)
    while queue:
        for ref in sorted(references(queue.pop(0))):
            if ref not in seen:
                seen.add(ref)
                closure.append(ref)
                queue.append(ref)
    return closure


def compile_kotlin(src_root, candidates, work, info=None):
    """Compile private thunks beside their original declarations, using kotlinc.

    Returns actual JVM method names paired with the original CPG identities.
    Joern ships the standard Kotlin compiler; use it if no kotlinc is installed.

    Test source sets are never compiled (`is_test_source`). The first attempt compiles the
    candidate files together with the project's other non-test sources; if that fails --
    one unresolved reference anywhere fails the whole invocation -- a second attempt
    compiles the candidate files with the same-repo files they reference, transitively
    (`kotlin_reference_closure`: by package and simple name, from imports and same-package
    use), which succeeds when the failure was elsewhere in the tree; a third compiles
    the candidate files alone, which succeeds whenever they do not depend on the rest of
    the project; if that fails too, each candidate file is compiled with its own closure
    and then alone, so one broken file does not sink the others. Every attempt, its file count and its FIRST errors
    are recorded in `info["kotlin_compile_attempts"]`; the files that failed are named in
    `info["compile_failing_files"]` and bucketed in `info["compile_failure_causes"]`.
    """
    info = {} if info is None else info
    compiler, flags, runtime = kotlin_toolchain()
    source = Path(src_root).resolve()
    dest = Path(work) / "kotlin-source"
    copy_sources(source, dest)
    classes = Path(work) / "classes"
    classes.mkdir(exist_ok=True)
    names, skipped = {}, {}
    thunked = []
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
        member = f["params"][0:1] == ["this"] and owner not in (prefix.rstrip("."), "<global>", "")
        if member and (f.get("paramTypes") or [owner])[0] != owner:
            skipped[f["name"]] = "Kotlin member extension function: two receivers"
            continue
        if member:
            # A member of a class, `object`, companion or enum: no thunk. The driver calls
            # the compiled method reflectively on a receiver it obtains itself (the
            # singleton, an enum entry, or a no-arg constructor's object), so the JVM
            # name IS the Joern identity.
            names[f["name"]] = f["name"]
            if target not in thunked:
                thunked.append(target)
            continue
        if owner not in (prefix.rstrip("."), "<global>", ""):
            skipped[f["name"]] = "Kotlin receiver fixture required"
            continue
        cls = "AutoformRuntime" + str(i)
        params = ", ".join("a%d: %s" % (j, kt_type[t]) for j, t in enumerate(args))
        vals = ["a%d" % j for j in range(len(args))]
        # A top-level extension function (`fun T.f(..)`): Joern lists its receiver as the
        # first parameter, `this`, and the first argument type; the thunk calls it on a0.
        extension = f["params"][0:1] == ["this"]
        call = (vals[0] + "." + short + "(" + ", ".join(vals[1:]) + ")" if extension
                else short + "(" + ", ".join(vals) + ")")
        target.write_text(code + "\nobject " + cls + " {\n @JvmStatic fun invoke(" + params +
                          "): " + kt_type[m.group("ret")] + " = " + call + "\n}\n")
        names[f["name"]] = prefix + cls + ".invoke:" + m.group("ret") + "(" + ",".join(args) + ")"
        if target not in thunked:
            thunked.append(target)
    if not names:
        return names, skipped, runtime
    # The project's dependency classpath (differential.JAVA_CLASSPATH_ENV).
    dependencies = os.environ.get("AUTOFORM_JAVA_CLASSPATH", "").strip(os.pathsep)
    if dependencies:
        if "-classpath" in flags:
            flags = list(flags)
            flags[flags.index("-classpath") + 1] += os.pathsep + dependencies
        else:
            flags = list(flags) + ["-classpath", dependencies]
        runtime = runtime + os.pathsep + dependencies if runtime else dependencies
    others = sorted(p for p in dest.rglob("*") if p.suffix in (".kt", ".java") and p.is_file()
                    and p not in thunked and not is_test_source(p.relative_to(dest)))

    def attempt(scope, files):
        launch = sandbox.sandboxed(compiler + flags + [str(p) for p in files] + ["-d", str(classes)],
                                   cwd=str(work), work=work)
        try:
            p = launch.run(capture_output=True, text=True, timeout=180, start_new_session=True)
            output, failed = p.stderr + p.stdout, p.returncode != 0
        except subprocess.TimeoutExpired:
            output, failed = "kotlinc timed out after 180s", True
        record = dict(scope=scope, files=len(files), ok=not failed)
        info["kotlin_compile_attempts"].append(record)
        if not failed:
            return []
        errors = kotlinc_errors(output, dest, work) or [("?", output.strip()[:1500] or "kotlinc failed")]
        # The HEAD of the output: kotlinc reports in file order and the first error is
        # usually the cause; the tail showed only the last file's follow-on errors.
        record["first_errors"] = ["%s: %s" % e for e in errors[:10]]
        failing = {}
        for path, message in errors:
            failing.setdefault(path, message)
        record["failing_files"] = sorted(failing)[:40]
        record["failing_files_total"] = len(failing)
        return errors

    info["kotlin_compile_attempts"] = []
    scopes = [("candidate files with the project's non-test sources", thunked + others)]
    closure = kotlin_reference_closure(thunked, others) if others else list(thunked)
    if others and len(thunked) < len(closure) < len(thunked) + len(others):
        scopes.append(("candidate files with the %d same-repo file(s) they reference"
                       % (len(closure) - len(thunked)), closure))
    if others:
        scopes.append(("candidate files alone", thunked))
    for scope, files in scopes:
        shutil.rmtree(classes)
        classes.mkdir()
        errors = attempt(scope, files)
        if not errors:
            return names, skipped, runtime
    # Still failing: one candidate file must not sink the others, so compile each with
    # the files it references, then alone. Classes accumulate: each attempt adds its own.
    failed_files = {}
    if len(thunked) > 1:
        shutil.rmtree(classes)
        classes.mkdir()
        for target in thunked:
            label = "candidate file " + str(target.relative_to(dest))
            own = kotlin_reference_closure([target], others) if others else [target]
            errors = (attempt(label + " with the %d same-repo file(s) it references" % (len(own) - 1), own)
                      if len(own) > 1 else None)
            if errors is None or errors:
                errors = attempt(label, [target])
            if errors:
                failed_files[target] = errors
    else:
        failed_files[thunked[0]] = errors
    first = {}
    for target, errors in failed_files.items():
        for path, message in errors:
            first.setdefault(path, message)
    info["compile_failing_files"] = dict(sorted(first.items())[:40])
    info["compile_failure_causes"] = dict(collections.Counter(
        kotlinc_failure_category(m) for m in first.values()).most_common())
    for f, m, args, path in candidates:
        target = dest / Path(path).resolve().relative_to(source)
        if f["name"] in names and target in failed_files:
            del names[f["name"]]
            skipped[f["name"]] = ("kotlinc failed: " + " | ".join(
                "%s: %s" % e for e in failed_files[target][:3]))[:1000]
    return names, skipped, runtime


def copy_sources(source, destination, node_ancestors=False):
    shutil.copytree(source, destination, ignore=shutil.ignore_patterns(
        ".git", ".lake", ".venv", "node_modules", "__pycache__"))
    # Resolve installed packages without copying potentially gigabytes of dependencies.
    for modules in Path(source).rglob("node_modules"):
        rel = modules.relative_to(source)
        if "node_modules" not in rel.parts[:-1]:
            target = Path(destination) / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.symlink_to(modules.resolve(), target_is_directory=True)
    # Node also searches every ancestor of a module's directory. The copy has none of the
    # source's ancestors, so a --subdir run would lose the package root's node_modules:
    # link the nearest one, which is the first directory Node would reach past the tree.
    # Node-only: kotlinc is handed the whole copy and would compile sources inside it.
    top = Path(destination) / "node_modules"
    if node_ancestors and not top.exists():
        for ancestor in Path(source).resolve().parents:
            if (ancestor / "node_modules").is_dir():
                top.symlink_to((ancestor / "node_modules").resolve(), target_is_directory=True)
                break


def value(v):
    tag, data = v[0], v[1] if len(v) > 1 else None
    if tag in ("int", "float"):
        return (tag, int(data))
    if tag in ("str", "bool"):
        return (tag, data)
    if tag == "unit":
        return (tag,)
    # The Node driver's arrays and plain objects (`enc` in NODE_DRIVER).
    if tag == "list":
        return (tag, [value(x) for x in data])
    if tag == "dict":
        return (tag, [(value(k), value(x)) for k, x in data])
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
            heap, glob = node_globals([(n, value(v)) for n, v in row.get("globals", [])])
        except (ValueError, KeyError) as e:
            skipped[f["name"]] = str(e)
            continue
        case = dict(name=f["name"], heap=heap, self=None, args=args,
                    outcome=outcome, origin=origin)
        if glob:
            case["globals"] = glob
        cases.append(case)
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
        # Joern gives methods a receiver parameter. They require a receiver fixture. The
        # receiver is the first parameter, typed `<package path>.<Type>`, and the method is
        # named `<package path>.<Type>.<method>`; calling it by its bare name would fail
        # to compile and take every other function of the package down with it.
        receiver = (f.get("paramTypes") or [""])[0].strip("*")
        if "this" in f["params"] or re.search(r"\([^)]*\)\.", f["name"]) or (
                f["params"] and receiver and f["name"] == receiver + "." + short):
            skipped[f["name"]] = "receiver fixture required"
            continue
        groups.setdefault(source.parent, []).append((f, short))
    cases, driver_failures = [], []
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
        # The build cache is forced into the work tree: a user GOCACHE outside it is not writable
        # under the sandbox, and go then fails without a usable message. No network inside the
        # sandbox either: a toolchain the go.mod asks for must already be local.
        env["GOCACHE"] = str(Path(work) / "go-cache")
        env["GOTOOLCHAIN"] = "local"
        launch = sandbox.sandboxed(["go", "test", "-run", "^TestAutoformRuntime$", "-v", "-count=1", "-timeout=30s", "."],
                                   cwd=str(target), env=env, work=work)
        package_name = str(directory.relative_to(module)) or "."
        try:
            r = launch.run(capture_output=True, text=True, timeout=GO_DRIVER_TIMEOUT,
                           start_new_session=True)
        except subprocess.TimeoutExpired as e:
            # Mirrors the Kotlin compile step: a hung driver is a recorded failure of
            # this package's calls, not a traceback that loses the whole run.
            reason = "driver timed out after %d s" % GO_DRIVER_TIMEOUT
            for f, _ in entries:
                skipped[f["name"]] = reason
            driver_failures.append({"package": package_name, "returncode": None,
                                    "timed_out_after_s": GO_DRIVER_TIMEOUT,
                                    "stderr_tail": output_tail(e.stderr)})
            continue
        lines = [l[len("@@RESULT@@"):] for l in r.stdout.splitlines() if l.startswith("@@RESULT@@")]
        if r.returncode or not lines:
            for f, _ in entries:
                skipped[f["name"]] = "go test failed: " + (r.stderr + r.stdout)[-2000:]
            driver_failures.append({"package": package_name, "returncode": r.returncode,
                                    "stderr_tail": output_tail(r.stderr)})
            continue
        found, refused = records(json.loads(lines[-1]), [f for f, _ in entries])
        cases.extend(found)
        skipped.update(refused)
    info = {"packages": len(groups), "cases_built": len(cases), "sandbox": sandbox.report()}
    if driver_failures:
        info["driver_failures"] = driver_failures
    return cases, info, skipped


NODE_DRIVER = r'''
import {pathToFileURL} from 'node:url';
const targets = JSON.parse(process.argv[2]);
const rows = [];
// Arrays and plain objects encode STRUCTURALLY, as Core's harness reports a boxed
// list/dict for JavaScript (`unboxDeep` in differential.py): a dense Array whose prototype
// is Array.prototype -> ['list', items]; an object whose prototype is Object.prototype
// (or null) with only enumerable string-keyed data properties -> ['dict', [key, value]
// pairs in Object.keys order]. Refused by name: a class instance, an array subclass, a
// sparse array or one with extra properties, a cycle, an accessor, a symbol or
// non-enumerable key, and an integer-like key (JS lists those first, ascending -- an
// order Core's object literal does not model, so the exporter does not fold them).
// `id`, when given, is a receiver case's identity map: every container the walk reaches
// becomes one cell (Core allocates one cell per array/object literal), so the first
// visit names it and carries its contents and a later visit names it again. An alias
// Node holds as one object is then one address in the model, not two equal copies, a
// cycle is a reference cycle rather than a refusal, and the receiver itself is ['self'].
function enc(v, depth = 0, open = new Set(), id = null) {
  if (v === undefined || v === null) return ['unit'];
  if (typeof v === 'boolean') return ['bool', v];
  if (typeof v === 'string') return ['str', v];
  if (typeof v === 'bigint') return ['int', String(v)];
  if (typeof v === 'number') {
    if (Number.isSafeInteger(v) && !Object.is(v, -0)) return ['int', String(v)];
    const b = Buffer.alloc(8); b.writeDoubleBE(v); return ['float', String(b.readBigUInt64BE())];
  }
  if (typeof v !== 'object') throw Error('no encoding for a value of type ' + typeof v);
  if (open.has(v)) throw Error('no encoding for a cyclic ' + (Array.isArray(v) ? 'array' : 'object'));
  if (depth >= 16) throw Error('no encoding for a value nested more than 16 deep');
  const keys = Reflect.ownKeys(v);
  open.add(v);
  try {
    if (Array.isArray(v)) {
      if (Object.getPrototypeOf(v) !== Array.prototype) throw Error('no encoding for an array subclass');
      if (keys.length !== v.length + 1 || !keys.every((k, i) => i === v.length ? k === 'length' : k === String(i)))
        throw Error('no encoding for a sparse array or an array with extra properties');
      return ['list', v.map(x => encRef(x, depth + 1, open, id))];
    }
    const proto = Object.getPrototypeOf(v);
    if (proto !== Object.prototype && proto !== null)
      throw Error('no encoding for a value of type object (' + (proto?.constructor?.name || 'class instance') + ')');
    const pairs = [];
    for (const k of keys) {
      if (typeof k !== 'string') throw Error('no encoding for an object with a symbol key');
      if (/^(0|[1-9][0-9]*)$/.test(k)) throw Error('no encoding for an object with an integer-like key');
      const d = Object.getOwnPropertyDescriptor(v, k);
      if (!('value' in d)) throw Error('no encoding for an object with an accessor property');
      if (!d.enumerable) throw Error('no encoding for an object with a non-enumerable property');
      pairs.push([['str', k], encRef(d.value, depth + 1, open, id)]);
    }
    return ['dict', pairs];
  } finally { open.delete(v); }
}
// A receiver case's element encoding: with `id` a container becomes a named cell
// (first visit carries the contents, a later visit is the bare name); without it this
// is `enc`, exactly as the arguments, globals and results have always been reported.
function encRef(v, depth, open, id) {
  if (!id || v === null || typeof v !== 'object') return enc(v, depth, open, id);
  if (v === id.self) return ['self'];
  if (id.map.has(v)) return ['cell', id.map.get(v)];
  const n = id.map.size;
  id.map.set(v, n);
  if (id.held) id.held.push(v);
  return ['cell', n, enc(v, depth, open, id)];
}
// The receiver's own enumerable data properties, in own-key order, each value named by
// `encRef`. Refused by name: a symbol key, a non-enumerable or accessor property (Core
// could not start from the state they show), and a value the wire cannot carry. The
// property names the refusal. Private (#) fields are not own properties at all: a body
// that touches one is refused before this runs (`private`, `node_members`).
function props(recv, id) {
  const out = [];
  for (const k of Reflect.ownKeys(recv)) {
    if (typeof k === 'symbol')
      throw Error('receiver property ' + String(k) + ' is a symbol key: not observable');
    const d = Object.getOwnPropertyDescriptor(recv, k);
    if (!d.enumerable)
      throw Error('receiver property ' + k + ' is not enumerable: not observable');
    if (!('value' in d))
      throw Error('receiver property ' + k + ' is an accessor property: not observable');
    try { out.push([k, encRef(d.value, 0, new Set(), id)]); }
    catch (e) { throw Error('receiver property ' + k + ': ' + e.message); }
  }
  return out;
}
// A property the body reads or writes through `this` that the receiver does not own but
// inherits is not in the reported state: a getter or setter runs code, a prototype data
// property is a value Core never sees. Either refuses the case, by name. An inherited
// method is not a state value and is left to Core, which resolves it as a method.
function inherited(recv, names) {
  for (const k of names) {
    if (Object.prototype.hasOwnProperty.call(recv, k)) continue;
    for (let o = Object.getPrototypeOf(recv); o !== null; o = Object.getPrototypeOf(o)) {
      const d = Object.getOwnPropertyDescriptor(o, k);
      if (!d) continue;
      if (!('value' in d))
        throw Error('receiver property ' + k + ' is an inherited getter or setter: not observable');
      if (typeof d.value !== 'function')
        throw Error('receiver property ' + k + ' is an inherited prototype data property: not observable');
      break;
    }
  }
}
const numbers = [0, 1, -1, 2147483647, 4294967296, 32, 64, -3.75, Infinity, NaN];
// A static method is looked up as an own data property of the class, never through a getter
// or the prototype chain: anything else is refused with the reason, not called. A method on
// the prototype is an instance method: the driver builds a receiver (the class's own
// constructor, which must take no arguments) and reports its state, rather than refuse.
function callee(owner, c) {
  if (c.member === undefined) {
    return typeof owner === 'function' ? {fn: owner, self: undefined}
                                       : {skip: 'function not accessible at module scope'};
  }
  if (typeof owner !== 'function') return {skip: 'class ' + c.binding + ' not accessible at module scope'};
  const d = Object.getOwnPropertyDescriptor(owner, c.member);
  // `this` is the class, as for `Class.method()`, unless the case records an explicit unit receiver.
  if (d && typeof d.value === 'function') return {fn: d.value, self: c.unitThis ? undefined : owner};
  if (d) return {skip: c.binding + '.' + c.member + ' is a static accessor or field, not a static method'};
  const pd = owner.prototype && Object.getOwnPropertyDescriptor(owner.prototype, c.member);
  if (pd && ('get' in pd || 'set' in pd))
    return {skip: c.binding + '.' + c.member + ' is a getter or setter, not a method'};
  if (pd && typeof pd.value !== 'function')
    return {skip: c.binding + '.' + c.member + ' is a prototype data property, not a method'};
  if (pd) {
    if (c.unitThis)
      return {skip: c.binding + '.' + c.member + ' is an instance method, and a this parameter cannot also name its receiver'};
    if (owner.length > 0)
      return {skip: c.binding + '.' + c.member + ' is an instance method, but the constructor of ' + c.binding + ' needs arguments'};
    if (c.private)
      return {skip: c.binding + '.' + c.member + ' reads or writes a private (#) member: the receiver state cannot observe it'};
    return {fn: pd.value, inst: true, cls: owner};
  }
  return {skip: 'no static method ' + c.binding + '.' + c.member};
}
for (const target of targets) {
  try {
    await import(pathToFileURL(target.path).href);
  } catch (e) {
    for (const c of target.calls) rows.push({id:c.id, skip:'module load failed: ' + e.stack});
    continue;
  }
  const bindings = globalThis[Symbol.for('autoform.runtime')];
  const readers = globalThis[Symbol.for('autoform.reads')] || {};
  for (const c of target.calls) {
    const {fn, self, skip, inst, cls} = callee(bindings[c.binding], c);
    if (skip) { rows.push({id:c.id, skip}); continue; }
    if (inst && c.instReads.includes('self') && readers['self']() !== undefined) {
      rows.push({id:c.id, skip: 'the module binds self, which the receiver must name'});
      continue;
    }
    // The exporter lowers a method's `this` to the name `self`, which the receiver is
    // bound to, so a receiver case never probes the module for a binding of that name.
    // Its reads also cover the methods it calls on `self` (`instReads`).
    const reads = inst ? c.instReads.filter(n => n !== 'self') : c.reads;
    for (let i = 0; i < c.count; ++i) {
      const args = c.pools.map((p, j) => { const pool = p || numbers; return pool[(i+j) % pool.length]; });
      const row = {id:c.id, args:args.map(enc)};
      // An instance method runs on a receiver the driver builds: a fresh object per
      // case, its own enumerable data properties reported before the call and -- also
      // when the call throws, for Core mutates before it raises -- after it. `cells`
      // re-reports every container named before the call (by the receiver or by a
      // module binding below), through the references the driver kept, so a container
      // the receiver no longer names is still compared.
      let recv = null, id = null, pre = null;
      if (inst) {
        try { recv = new cls(); }
        catch (e) {
          rows.push({id:c.id, skip: 'receiver not built: constructor threw ' + (e?.constructor?.name || 'Error')});
          continue;
        }
        id = {map: new Map(), held: [], self: recv};
        try { pre = props(recv, id); inherited(recv, c.selfProps); }
        catch (e) { rows.push({id:c.id, skip: e.message}); continue; }
      }
      // The module bindings the call tree reads, as they are IMMEDIATELY before the call
      // (an earlier call may have changed them). A function value is left to Core, which
      // resolves a module function by name; anything else the wire cannot carry refuses
      // the case -- Core would otherwise start from a different state than Node. In a
      // receiver case a container is named through the same identity map as the
      // receiver's (one object, one cell, however it is reached).
      const globals = [];
      let refused = null;
      for (const name of reads) {
        const v = readers[name]();
        if (typeof v === 'function') continue;
        try { globals.push([name, inst ? encRef(v, 0, new Set(), id) : enc(v)]); }
        catch (e) { refused = 'module binding ' + name + ': ' + e.message; break; }
      }
      if (refused) { rows.push({id:c.id, skip: refused}); continue; }
      if (globals.length) row.globals = globals;
      // Every container named so far is part of the state Core starts from; one first
      // reached later (the result, or a new property value) is not, and is not held.
      const held = inst ? id.held : null;
      if (inst) id.held = null;
      let result, threw = false;
      try {
        result = Reflect.apply(fn, inst ? recv : self, args);
      } catch (e) { row.exception = e?.constructor?.name || 'Error'; threw = true; }
      // Encoding stays outside the try: a result the wire cannot carry is not a throw.
      if (!threw) {
        if (result && typeof result.then === 'function') row.skip = 'promise return requires async semantics';
        else {
          // In a receiver case the result is named through the identity map too: Core
          // returns a reference, compared with the post-call heap rather than unboxed.
          try { row.result = inst ? encRef(result, 0, new Set(), id) : enc(result); }
          catch (e) { row.skip = 'unusable result: ' + e.message; }
        }
      }
      if (inst) {
        let post, cells;
        try {
          post = props(recv, id);
          cells = held.map(o => enc(o, 0, new Set(), id));
        } catch (e) { rows.push({id:c.id, skip: 'receiver state after the call: ' + e.message}); continue; }
        row.recv = {pre: pre, post: post, cells: cells};
      }
      rows.push(row);
    }
  }
}
console.log('@@RESULT@@' + JSON.stringify(rows));
'''


# Node: what a module needs from `node_modules`, and the imports tsc would not emit.
#
# `node --experimental-strip-types` erases annotations but keeps every import declaration,
# while tsc (and esbuild, swc, ts-node) drop an import whose bindings are used only as
# types: `import { Stage } from 'lib'` with `Stage` only in annotations never loads `lib`
# in the compiled program. An archived revision has no `node_modules`, so such an import
# failed the whole module with ERR_MODULE_NOT_FOUND although the program never loads it.
# `prepare_node_imports` drops exactly those declarations from the oracle's private copy,
# decided on Node's own stripped text: a binding is type-only when its name no longer
# occurs anywhere in the stripped module outside its declaration (a textual test, so a
# name in a string, a comment or a property key keeps the import: conservative). It is
# done only for a package that is not installed, only for a `.ts`-family file under a
# `tsconfig.json` that does not keep such imports (`verbatimModuleSyntax`,
# `preserveValueImports`, `importsNotUsedAsValues: preserve|error`, or
# `emitDecoratorMetadata`, which emits annotation types as values; an `extends` it cannot
# read counts as keeping them), and never for a side-effect `import 'x'`. Every package a
# module still cannot load is named with the fix in the refusal.
NODE_MODULES_ENV = "AUTOFORM_NODE_MODULES"
TS_SUFFIXES = (".ts", ".tsx", ".mts", ".cts")
NODE_SUFFIXES = TS_SUFFIXES + (".js", ".mjs", ".cjs", ".jsx")
NODE_STRIP = r"""
import { stripTypeScriptTypes, builtinModules } from 'node:module';
import { readFileSync, writeFileSync } from 'node:fs';
process.removeAllListeners('warning');
const [list, out] = process.argv.slice(2);
const files = JSON.parse(readFileSync(list, 'utf8'));
const result = {builtins: builtinModules, files: {}};
for (const f of files) {
  try { result.files[f] = {code: stripTypeScriptTypes(readFileSync(f, 'utf8'), {mode: 'strip'})}; }
  catch (e) { result.files[f] = {error: String((e && e.message) || e).slice(0, 200)}; }
}
writeFileSync(out, JSON.stringify(result));
"""
_DECL = re.compile(r"""import(?![\w$])\s*(?:(?P<clause>[^'"`;()]*?)\s*from\s*)?(?P<q>['"])(?P<spec>[^'"\n]+)(?P=q)[ \t]*;?""")
_TRIVIA = re.compile(r"""(?:\s+|//[^\n]*|/\*.*?\*/|^\#![^\n]*|(['"])use strict\1;?)*""", re.S)
_SPECIFIERS = re.compile(r"""(?:\bfrom\s*|\bimport\s*\(\s*|\brequire\s*\(\s*|^\s*import\s*)(['"])([^'"\n]+)\1""", re.M)
_KEEPS_IMPORTS = re.compile(r'"(?:verbatimModuleSyntax|preserveValueImports|emitDecoratorMetadata)"\s*:\s*true'
                            r'|"importsNotUsedAsValues"\s*:\s*"(?:preserve|error)"')


def package_name(spec):
    """`@scope/pkg/sub` -> `@scope/pkg`; `pkg/sub` -> `pkg`; None for a relative, absolute,
    `#import` or URL specifier, which no `node_modules` provides."""
    if spec.startswith((".", "/", "#")) or re.match(r"[a-z]+:", spec) and not spec.startswith("node:"):
        return None
    parts = spec.split("/")
    return "/".join(parts[:2]) if spec.startswith("@") else parts[0]


def _installed(path, name):
    for directory in Path(path).parents:
        if (directory / "node_modules" / name).exists():
            return True
    return False


def _bindings(clause):
    """Local names an import clause binds, or None when it is not one this reads."""
    clause = clause.strip()
    names = []
    m = re.fullmatch(r"(?:([A-Za-z_$][\w$]*)\s*,?\s*)?(?:\*\s*as\s+([A-Za-z_$][\w$]*)|\{([^{}]*)\})?", clause, re.S)
    if not clause or not m:
        return None
    if m.group(1):
        names.append(m.group(1))
    if m.group(2):
        names.append(m.group(2))
    if m.group(3) is not None:
        for entry in m.group(3).split(","):
            words = entry.split()
            if not words:
                continue
            if not re.fullmatch(r"[A-Za-z_$][\w$]*", words[-1]) or (len(words) > 1 and words[-2] != "as"):
                return None
            names.append(words[-1])
    return names or None


def _tsconfig_keeps_imports(path, stop):
    """True when the nearest tsconfig.json keeps type-only imports, None when there is
    none (no elision: nothing says how the project compiles), False otherwise."""
    for directory in [Path(path).parent, *Path(path).parent.parents]:
        config = directory / "tsconfig.json"
        if config.is_file():
            seen = set()
            while config is not None and config not in seen:
                seen.add(config)
                text = config.read_text(errors="replace")
                if _KEEPS_IMPORTS.search(text):
                    return True
                base = re.search(r'"extends"\s*:\s*"([^"]+)"', text)
                if not base:
                    return False
                parent = (config.parent / base.group(1))
                parent = parent if parent.suffix == ".json" else parent.with_suffix(".json")
                if not base.group(1).startswith(".") or not parent.is_file():
                    return True      # a package's base config we cannot read
                config = parent
            return True
        if directory == stop:
            break
    return None


def _resolve_local(path, spec):
    base = (Path(path).parent / spec)
    stem = base.with_suffix("") if base.suffix in (".js", ".mjs", ".cjs", ".jsx") else base
    for candidate in [base, *[Path(str(stem) + s) for s in NODE_SUFFIXES],
                      *[base / ("index" + s) for s in NODE_SUFFIXES]]:
        if candidate.is_file():
            return candidate
    return None


def prepare_node_imports(dest, work, launch_record=None):
    """Drop the type-only imports of uninstalled packages from the copy at `dest` (see
    above) and return `(missing, info)`: `missing` maps every module file to the packages
    it or a module it imports still needs and no `node_modules` provides."""
    dest = Path(dest)
    files = sorted(p for p in dest.rglob("*") if p.suffix in NODE_SUFFIXES and p.is_file()
                   and "node_modules" not in p.relative_to(dest).parts)
    info = {"type_only_imports_elided": 0}
    if not files:
        return {}, info
    listing, out = Path(work) / "strip-files.json", Path(work) / "strip-out.json"
    listing.write_text(json.dumps([str(p) for p in files]))
    script = Path(work) / "node_strip.mjs"
    script.write_text(NODE_STRIP)
    stripped = {"builtins": [], "files": {}}
    try:
        r = sandbox.sandboxed(["node", str(script), str(listing), str(out)], cwd=str(work), work=work).run(
            capture_output=True, text=True, timeout=120, start_new_session=True)
        if r.returncode == 0 and out.is_file():
            stripped = json.loads(out.read_text())
        else:
            info["strip_failed"] = (r.stderr or r.stdout)[-300:]
    except (OSError, subprocess.TimeoutExpired, ValueError) as exc:
        info["strip_failed"] = str(exc)[:300]
    builtins = set(stripped.get("builtins") or [])
    direct, local = {}, {}
    elided = []
    for path in files:
        text = path.read_text(errors="replace")
        entry = (stripped.get("files") or {}).get(str(path)) or {}
        code = entry.get("code") if path.suffix in TS_SUFFIXES else text
        if code is None:
            code = text
        needs, imports = set(), set()
        for _, spec in _SPECIFIERS.findall(code):
            name = package_name(spec)
            if name is None:
                if spec.startswith("."):
                    target = _resolve_local(path, spec)
                    if target is not None:
                        imports.add(target)
            elif not (spec.startswith("node:") or name in builtins or _installed(path, name)):
                needs.add(name)
        keeps = (_tsconfig_keeps_imports(path, dest) if path.suffix in TS_SUFFIXES
                 and "code" in entry else True)
        if needs and keeps is False and len(code) == len(text):
            edits, at = [], 0
            while True:
                at = _TRIVIA.match(code, at).end()
                m = _DECL.match(code, at)
                if not m:
                    break
                name = package_name(m.group("spec"))
                names = _bindings(m.group("clause") or "") if m.group("clause") is not None else None
                rest = code[:m.start()] + code[m.end():]
                if (name in needs and names and text[m.start():m.start() + 6] == "import"
                        and not any(re.search(r"(?<![\w$])" + re.escape(n) + r"(?![\w$])", rest)
                                    for n in names)):
                    edits.append((m.start(), m.end(), name))
                at = m.end()
            for start, end, name in reversed(edits):
                text = text[:start] + re.sub(r"[^\n]", " ", text[start:end]) + text[end:]
                code = code[:start] + re.sub(r"[^\n]", " ", code[start:end]) + code[end:]
            if edits:
                path.write_text(text)
                elided += [f"{path.relative_to(dest).as_posix()}: {name}" for _, _, name in edits]
                needs = set()
                for _, spec in _SPECIFIERS.findall(code):
                    name = package_name(spec)
                    if name and not (spec.startswith("node:") or name in builtins or _installed(path, name)):
                        needs.add(name)
        # A relative specifier without its extension (`'./b'`, `'../config'`) is resolved
        # by tsc's module resolution to `b.ts` / `config/index.ts` and emitted as such; Node
        # loads only the exact path, so the copy spells the file it resolves to.
        if len(code) == len(text):
            spelled = []
            for m in _SPECIFIERS.finditer(code):
                spec = m.group(2)
                if spec.startswith(".") and not (path.parent / spec).is_file():
                    target = _resolve_local(path, spec)
                    if target is not None:
                        rel = os.path.relpath(target, path.parent).replace(os.sep, "/")
                        spelled.append((m.start(2), m.end(2), rel if rel.startswith(".") else "./" + rel))
            for start, end, new in reversed(spelled):
                text = text[:start] + new + text[end:]
            if spelled:
                path.write_text(text)
                info["relative_specifiers_resolved"] = info.get("relative_specifiers_resolved", 0) + len(spelled)
        direct[path], local[path] = needs, imports
    missing = {}
    for path in files:
        seen, todo, needs = {path}, [path], set()
        while todo:
            current = todo.pop()
            needs |= direct.get(current, set())
            for nxt in local.get(current, ()):
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
        if needs:
            missing[str(path)] = sorted(needs)
    info["type_only_imports_elided"] = len(elided)
    if elided:
        info["elided"] = elided[:40]
    every = sorted({n for v in missing.values() for n in v})
    if every:
        info["packages_not_installed"] = every[:60]
    return missing, info


def missing_packages_reason(packages, error=""):
    """The refusal for a module that cannot load because packages are not installed: the
    fix first (a report caps long reasons), then the packages, nearest first."""
    found = re.findall(r"Cannot find (?:package|module) '([^']+)'", error)
    names = list(dict.fromkeys([package_name(n) or n for n in found] + list(packages)))
    shown = ", ".join(names[:6]) + (" (+%d more)" % (len(names) - 6) if len(names) > 6 else "")
    return ("module load failed: %d package(s) not installed, run `npm ci` in the repository "
            "(or set %s to an installed node_modules) and re-run: %s; no node_modules in the "
            "checkout or its ancestors provides them, for this module or one it imports"
            % (len(names), NODE_MODULES_ENV, shown or "?"))


def string_literals(node):
    """String literals of one exported body, in source order."""
    found, stack = [], [node]
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            if n.get("k") == "str" and isinstance(n.get("v"), str):
                found.append(n["v"])
            stack.extend(reversed(list(n.values())))
        elif isinstance(n, list):
            stack.extend(reversed(n))
    return found


def node_callee(f):
    """(call, None) for a module-scope function or `Class.method`, else (None, reason).

    Joern names JS/TS methods `<file>::program:<path>`: one segment is a module-scope
    function, `Class:method` a class member, anything deeper a nested closure. Whether a
    member is static is only known at runtime; the driver refuses non-static ones.
    """
    full = f["name"]
    path = (full.split("::program:", 1)[1].split(":") if "::program:" in full
            else [f.get("sourceName", full.split(":")[-1])])
    ident = r"[A-Za-z_$][\w$]*"
    if len(path) == 1 and re.fullmatch(ident, path[0]):
        return dict(binding=path[0]), None
    if len(path) == 2 and path[1] == "<init>":
        return None, "constructor: receiver fixture required"
    if len(path) == 2 and all(re.fullmatch(ident, p) for p in path):
        return dict(binding=path[0], member=path[1]), None
    return None, "not a module-scope callable or static method"


def node_pools(f, extra=()):
    """Per argument: a string pool for a string-typed parameter, None for the numeric pool.
    `extra`: further strings (`--literal-inputs`: built from the function's and its file's
    literals), after the body's own and before the fixed pool."""
    params, types = f["params"], f.get("paramTypes") or []
    if len(types) != len(params):  # misaligned types say nothing; do not guess
        types = [""] * len(params)
    strings = list(dict.fromkeys(string_literals(f.get("body")) + list(extra) + STRING_POOL))
    return [strings if t == "__ecma.String" else None
            for p, t in zip(params, types) if p != "this"]


JS_IDENT = re.compile(r"[A-Za-z_$][\w$]*")
# Bound by the statement that names them (`Stmt.assign`, `forIn`, `tryCatch`, `del`).
_BINDERS = ("assign", "forIn", "tryCatch", "del")


def _scan(node, reads, binds, calls):
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            k = n.get("k")
            if k == "name" and isinstance(n.get("v"), str):
                reads.add(n["v"])
            elif k in _BINDERS and isinstance(n.get("x"), str):
                binds.add(n["x"])
            elif k == "call" and isinstance(n.get("f"), str):
                calls.add(n["f"])
            elif k == "fnref" and isinstance(n.get("v"), str):
                calls.add(n["v"])
            stack.extend(n.values())
        elif isinstance(n, list):
            stack.extend(n)


def node_reads(f, by_name):
    """The module-scope names `f`'s call tree reads: every name a body reads that it
    neither binds nor takes as a parameter, over `f` and every function of the export it
    calls or references (transitively). These are the bindings Core needs in its globals
    frame to start from Node's state; `exports` is the module's own export object, and a
    name that is not a JavaScript identifier is the exporter's own temporary."""
    seen, todo, free = set(), [f["name"]], set()
    while todo:
        name = todo.pop()
        if name in seen or name not in by_name:
            continue
        seen.add(name)
        g = by_name[name]
        reads, binds, calls = set(), set(), set()
        _scan(g.get("body"), reads, binds, calls)
        free |= reads - binds - set(g.get("params") or [])
        todo.extend(calls)
    return sorted(n for n in free
                  if JS_IDENT.fullmatch(n) and n not in ("this", "exports", "undefined"))


def node_members(f, by_name, by_member):
    """(touches a private member, the property names read or written through `self`, the
    functions reached) over `f`'s call tree: `f`, every function it calls or references, and every method a
    method call on `self` could reach (by member name, on any class of the export -- an
    over-approximation; `by_member` maps a member name to those functions). A private
    (#) member is not an own property, so the receiver state cannot report it; a
    property the receiver does not own but inherits (a getter, a setter, a prototype
    data property) is not in the reported state either. The driver refuses an instance method that touches either,
    for Core could only guess at the value a read sees or the field a write changes."""
    touched = set()
    seen, todo = set(), [f["name"]]
    while todo:
        name = todo.pop()
        if name in seen or name not in by_name:
            continue
        seen.add(name)
        stack = [by_name[name].get("body")]
        while stack:
            n = stack.pop()
            if isinstance(n, dict):
                k = n.get("k")
                member = (n.get("f") if k in ("field", "setField") else
                          n.get("m") if k == "mcall" else None)
                if isinstance(member, str):
                    if member.startswith("#"):
                        return True, [], []
                    target = n.get({"field": "a", "setField": "r", "mcall": "recv"}[k])
                    if target == {"k": "name", "v": "self"}:
                        if k == "mcall":
                            todo.extend(by_member.get(member, ()))
                        else:
                            touched.add(member)
                if k == "call" and isinstance(n.get("f"), str):
                    todo.append(n["f"])
                elif k == "fnref" and isinstance(n.get("v"), str):
                    todo.append(n["v"])
                stack.extend(n.values())
            elif isinstance(n, list):
                stack.extend(n)
    return False, sorted(touched), sorted(seen)


def node_globals(pairs):
    """Wire `[(name, value)]` -> (heap cells, globals bindings). A list or dict becomes a
    boxed cell, as Core's own JavaScript arrays and objects are (`Expr.listE`/`dictE`
    allocate under `.javascript`), so the function reads the value it would have built."""
    heap = []

    def box(v):
        if v[0] == "list":
            items = [box(x) for x in v[1]]
            heap.append(("list", [], ("list", items)))
            return ("ref", len(heap) - 1)
        if v[0] == "dict":
            items = [(box(k), box(x)) for k, x in v[1]]
            heap.append(("dict", [], ("dict", items)))
            return ("ref", len(heap) - 1)
        return v
    return heap, [(name, box(v)) for name, v in pairs]


def node_receiver(row, f, args):
    """An instance-method case from the driver's receiver report (`row['recv']`).

    The receiver is cell 0 and its reported own properties are its fields, so the model
    starts from exactly the state Node reported. Every container the driver named before
    the call (reached from the receiver or bound by a module binding the body reads) is
    the cell numbered by its driver id plus one -- Core allocates one cell per array or
    object literal, so an alias Node holds as one object is one address in the model.
    After the call `cells` re-reports each of those containers by the same id, and a
    container first reached after the call (from the result or the receiver) extends the
    numbering, so post cell i is the same object as pre cell i and the observation's
    roots line up. A container is spelled `['cell', id, contents]` the first time the
    driver reaches it and `['cell', id]` afterwards; the receiver itself is `['self']`."""
    full = f["name"]
    cls = (full.split("::program:", 1)[1] if "::program:" in full else full).split(":")[0]
    recv = row["recv"]

    def walk(w, seen):
        if w[0] == "self":
            return ("ref", 0)
        if w[0] == "cell":
            if len(w) > 2:
                seen[w[1]] = w[2]
            return ("ref", 1 + w[1])
        if w[0] in ("list", "dict"):
            raise ValueError("receiver state: a container outside a cell")
        return value(w)

    def cell(w, seen):
        if w[0] == "list":
            return ("list", [], ("list", [walk(x, seen) for x in w[1]]))
        if w[0] == "dict":
            return ("dict", [], ("dict", [(walk(k, seen), walk(x, seen)) for k, x in w[1]]))
        raise ValueError("receiver state: a cell that is not an array or object")

    def cells(seen, start, out):
        # A container is first reached inside one named before it, so walking the cells
        # in id order meets every id it names before it needs that id's contents.
        d = start
        while d in seen:
            out.append(cell(seen[d], seen))
            d += 1
        if any(k >= d for k in seen):
            raise ValueError("receiver state: a container id was reported out of order")
        return out

    npre = len(recv["cells"])
    pre = {}
    fields = [(k, walk(w, pre)) for k, w in recv["pre"]]
    glob = [(n, walk(w, pre)) for n, w in row.get("globals", [])]
    heap = cells(pre, 0, [(cls, fields, None)])
    if len(heap) != 1 + npre:
        raise ValueError("receiver state: the containers reported after the call are not "
                         "the ones named before it")
    post = {}
    outcome = (("exn", row["exception"]) if "exception" in row
               else ("val", walk(row["result"], post)))
    post_fields = [(k, walk(w, post)) for k, w in recv["post"]]
    post_heap = [(cls, post_fields, None)] + [cell(w, post) for w in recv["cells"]]
    post_heap = cells(post, npre, post_heap)
    case = dict(name=f["name"], heap=heap, self=("ref", 0), args=args,
                outcome=outcome, origin="constructed", post_heap=post_heap)
    if glob:
        case["globals"] = glob
    return case


def node_backend(src_root, funcs, ncases, lang, work, literals=None, universe=None):
    """`literals`, when given, maps a function to extra string inputs (`node_pools`).
    `universe`, when given, is every exported function, `funcs` the sample: an instance
    method's scan (`node_members`) follows its calls there, sampled or not."""
    root = Path(src_root).resolve()
    dest = Path(work) / "node"
    copy_sources(root, dest, node_ancestors=True)
    extra_modules = os.environ.get(NODE_MODULES_ENV)
    linked = None
    if extra_modules and not (dest / "node_modules").exists():
        if Path(extra_modules).is_dir():
            (dest / "node_modules").symlink_to(Path(extra_modules).resolve(), target_is_directory=True)
            linked = str(Path(extra_modules).resolve())
        else:
            linked = "%s names a missing directory: %s" % (NODE_MODULES_ENV, extra_modules)
    missing, import_info = prepare_node_imports(dest, work) if lang == "ts" or lang == "js" else ({}, {})
    if linked:
        import_info["node_modules_from_env"] = linked
    groups, skipped, candidates = {}, {}, []
    by_name = {f["name"]: f for f in funcs}
    every = dict(by_name, **{g["name"]: g for g in universe or ()})
    by_member = {}
    for name in every:
        by_member.setdefault(name.rsplit(":", 1)[-1], []).append(name)
    for f in funcs:
        call, reason = node_callee(f)
        if reason:
            skipped[f["name"]] = reason
            continue
        path = root / f.get("file", "")
        if not path.is_file():
            skipped[f["name"]] = "source file unavailable"
            continue
        idx = len(candidates)
        candidates.append(f)
        # Only a class member can turn out to be an instance method (the driver decides).
        # Its module reads, should it be one, also cover the methods it calls on `self`.
        reads = node_reads(f, by_name)
        private, own, reached = (node_members(f, every, by_member) if "member" in call
                                 else (False, [], []))
        inst_reads = sorted(set(reads).union(*(node_reads(every[n], every) for n in reached)))
        groups.setdefault(path, []).append(dict(call, id=idx, count=max(1, ncases),
                                                pools=node_pools(f, literals(f) if literals else ()),
                                                unitThis="this" in f["params"],
                                                private=private, selfProps=own,
                                                instReads=inst_reads, reads=reads))
    targets = []
    for path, calls in groups.items():
        target = dest / path.relative_to(root)
        bindings = ",".join(json.dumps(b) + ": typeof " + b + " === 'undefined' ? undefined : " + b
                            for b in dict.fromkeys(c["binding"] for c in calls))
        readers = ",".join(json.dumps(n) + ": () => typeof " + n + " === 'undefined' ? undefined : " + n
                           for n in dict.fromkeys(n for c in calls for n in c["reads"] + c["instReads"]))
        with target.open("a") as stream:
            stream.write("\n;globalThis[Symbol.for('autoform.runtime')] = {" + bindings + "};\n")
            stream.write(";globalThis[Symbol.for('autoform.reads')] = {" + readers + "};\n")
        targets.append(dict(path=str(target), calls=calls))
    driver = Path(work) / "node_driver.mjs"
    driver.write_text(NODE_DRIVER)
    cmd = ["node"] + (["--experimental-strip-types"] if lang == "ts" else [])
    launch = sandbox.sandboxed(cmd + [str(driver), json.dumps(targets)], cwd=str(work), work=work)
    try:
        r = launch.run(capture_output=True, text=True, timeout=NODE_DRIVER_TIMEOUT,
                       start_new_session=True)
    except subprocess.TimeoutExpired as e:
        # Mirrors the Kotlin compile step: every candidate is a recorded skip with the
        # reason, and the run goes on to write conformance.json.
        reason = "driver timed out after %d s" % NODE_DRIVER_TIMEOUT
        skipped.update({f["name"]: reason for f in candidates})
        return [], {"cases_built": 0, "sandbox": launch.record, "driver_returncode": None,
                    "driver_timed_out_after_s": NODE_DRIVER_TIMEOUT,
                    "driver_stderr_tail": output_tail(e.stderr)}, skipped
    lines = [l[len("@@RESULT@@"):] for l in r.stdout.splitlines() if l.startswith("@@RESULT@@")]
    if r.returncode or not lines:
        skipped.update({f["name"]: "node driver failed: " + (r.stderr + r.stdout)[-2000:] for f in candidates})
        return [], {"cases_built": 0, "sandbox": launch.record, "driver_returncode": r.returncode,
                    "driver_stderr_tail": output_tail(r.stderr)}, skipped
    rows = json.loads(lines[-1])
    for row in rows:
        # A module that cannot load for want of a package says which, and how to fix it.
        text = str(row.get("skip", ""))
        if text.startswith("module load failed") and "ERR_MODULE_NOT_FOUND" in text:
            f = candidates[row["id"]]
            target = str(dest / (root / f.get("file", "")).relative_to(root))
            if missing.get(target) or "Cannot find package" in text:
                row["skip"] = missing_packages_reason(missing.get(target, ()), text)
    cases = []
    for row in rows:
        # An instance-method row carries its receiver report and becomes a case that
        # starts from that state and compares the post-call state; every other row is
        # read exactly as before.
        if "recv" in row and "skip" not in row:
            f = candidates[row["id"]]
            try:
                cases.append(node_receiver(row, f, [value(v) for v in row["args"]]))
            except (ValueError, KeyError) as e:
                skipped[f["name"]] = str(e)
            continue
        found, refused = records([row], candidates)
        cases.extend(found)
        skipped.update(refused)
    return cases, {"files": len(groups), "cases_built": len(cases), "sandbox": launch.record,
                   "instance_cases": sum(1 for c in cases if c.get("origin") == "constructed"),
                   **({"imports": import_info} if import_info else {})}, skipped
