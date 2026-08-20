"""WASM execution mode for the differential harness's C backend.

Two jobs, both narrow on purpose.

1. SANDBOX. The `cc` backend `dlopen`s a native shared library and calls into it. The
   neutral AST carries no C type information, so an argument the harness encodes as
   `int` may really be a pointer; on the real `sds` corpus 50 native calls segfaulted.
   A segfault kills the harness process, not just the case. Compiled to wasm32 the same
   wild pointer becomes a *trap* -- a catchable, classifiable, RECORDED outcome. The
   fork-per-call workaround in `differential.py` survives the crash; this tells you what
   the crash was.

2. A SECOND C IMPLEMENTATION. Native clang and wasm-clang are two conforming C
   implementations with different word sizes, different memory layouts and different
   optimisation choices. Where they return DIFFERENT values for the same inputs, the
   program almost certainly depends on undefined behaviour. That is reported as its own
   category, `ub-suspected`, and never as a conformance divergence against Lean --
   `Autoform/Lang/Core/Numeric.lean` deliberately maps UB to `Expr.hole`
   (`NumResult.ub`), so a program two conforming compilers disagree about is one where
   the hole is the CORRECT answer, not a bug in the semantics.

WHAT THIS IS NOT. It is not a universal WASM oracle replacing the runtime backends.
Python/Ruby ship only their *interpreter* to wasm, which buys nothing over the CPython
we already run; and wasm32 has 32-bit `long`/`size_t`/pointers, which is the wrong
`NumConfig` for kernel code -- that width axis is exactly what `Numeric.lean` models.
The wasm value here is sandboxing and cross-implementation disagreement, nothing wider.

TOOLCHAIN CHOICE: wasm32-wasi when a wasi sysroot is present, freestanding wasm32
otherwise. Real C corpora `#include <stdio.h>`, and freestanding wasm32 has no libc
headers at all -- on the `sds` corpus every single source failed to compile that way,
which is exactly the "backend silently reports zero cases" outcome this file exists to
avoid. With `wasi-libc` installed, `sds.c` compiles and links with 176 exported
functions, and its imports are all `wasi_snapshot_preview1`, which node's `node:wasi`
provides. Freestanding remains as a fallback so a header-free corpus still runs when no
sysroot exists.

Linking goes through `wasm-ld` DIRECTLY rather than the clang driver: the driver insists
on `libclang_rt.builtins-wasm32.a`, which Homebrew's LLVM does not ship. Going straight
to the linker with `--allow-undefined` turns any missing compiler-rt helper into an
import instead of a hard link failure, and `wasm_run.mjs` records a call that actually
needs one as `unsupported-import` rather than faking a return value.
"""
import json, os, re, shutil, subprocess, sys

RUNNER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "wasm_run.mjs")

# Where a wasm-capable clang and wasm-ld tend to live on a machine that has one but has
# not put it on PATH. Apple's own clang has NO wasm target at all (`clang
# -print-targets` lists none), so `cc` is deliberately absent from this list: picking it
# up would produce native objects and a confusing link failure.
_CLANG_HINTS = ["/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin",
                "/opt/homebrew/opt/llvm@18/bin", "/usr/local/opt/llvm@18/bin"]
_LD_HINTS = _CLANG_HINTS + ["/opt/homebrew/opt/lld/bin", "/usr/local/opt/lld/bin"]
_SYSROOT_HINTS = ["/opt/homebrew/opt/wasi-libc/share/wasi-sysroot",
                  "/usr/local/opt/wasi-libc/share/wasi-sysroot",
                  "/opt/wasi-sdk/share/wasi-sysroot",
                  "/usr/share/wasi-sysroot"]


def _find_sysroot():
    """A wasi sysroot, plus the lib dir holding its `libc.a`.

    wasi-libc ships several ABI variants (wasip1, wasi, wasip2); we take the first that
    actually contains a `libc.a`, preferring wasip1 because that is the ABI node's
    `node:wasi` implements.
    """
    cands = [os.environ["WASI_SYSROOT"]] if os.environ.get("WASI_SYSROOT") else []
    cands += _SYSROOT_HINTS
    for s in cands:
        if not os.path.isdir(s): continue
        for v in ("wasm32-wasip1", "wasm32-wasi", "wasm32-wasip2"):
            libdir = os.path.join(s, "lib", v)
            if os.path.isfile(os.path.join(libdir, "libc.a")):
                return s, libdir
    return None, None


def _find(names, hints, check=None):
    for d in hints:
        for n in names:
            p = os.path.join(d, n)
            if os.path.isfile(p) and os.access(p, os.X_OK) and (check is None or check(p)):
                return p
    for n in names:
        p = shutil.which(n)
        if p and (check is None or check(p)):
            return p
    return None


def _has_wasm_target(clang):
    try:
        r = subprocess.run([clang, "-print-targets"], capture_output=True, text=True,
                           timeout=30)
    except Exception:                                          # noqa: BLE001
        return False
    return "wasm32" in r.stdout


def toolchain():
    """Locate a C -> wasm32 compiler and a wasm runtime.

    Returns a dict on success, or a dict with `ok: False` and a *reason* on failure.
    It never returns None-meaning-maybe: a missing toolchain has to surface as a loud
    `UNSUPPORTED: no wasm toolchain`, because a backend that quietly reports zero cases
    is worse than no backend at all.
    """
    clang = _find(["clang", "clang-22", "clang-18"], _CLANG_HINTS, _has_wasm_target)
    if not clang:
        return {"ok": False,
                "reason": "no clang with a wasm32 target (Apple clang has none; "
                          "try `brew install llvm`)"}
    wasm_ld = _find(["wasm-ld"], _LD_HINTS)
    if not wasm_ld:
        return {"ok": False,
                "reason": "clang has a wasm32 target but wasm-ld is absent "
                          "(try `brew install lld`)"}
    node = shutil.which("node")
    if not node:
        return {"ok": False, "reason": "no wasm runtime: node not on PATH "
                                       "(wasmtime/wasmer/wasm3 also absent)"}
    sysroot, libdir = _find_sysroot()
    return {"ok": True, "clang": clang, "wasm_ld": wasm_ld, "node": node,
            "sysroot": sysroot, "libdir": libdir,
            "target": "wasm32-wasi" if sysroot else "wasm32-freestanding",
            "note": (None if sysroot else
                     "no wasi sysroot (`brew install wasi-libc`): freestanding only, so "
                     "any source that includes a libc header will NOT compile and its "
                     "functions are reported as build failures, not as passes")}


def compile_wasm(srcs, work, tc):
    """Compile C sources to one freestanding wasm32 module.

    Returns (path, info). `path` is None on failure and `info["error"]` says why --
    again, never a silent empty success.

    Sources are compiled INDIVIDUALLY and then linked, and a file that will not compile
    for wasm32 is dropped with its error retained. Whole-corpus all-or-nothing linking
    would let one unportable file (inline asm, target intrinsics -- routine in the Linux
    corpora) zero out the entire run.
    """
    env = dict(os.environ)
    env["PATH"] = os.path.dirname(tc["wasm_ld"]) + os.pathsep + env.get("PATH", "")
    objs, failed = [], {}
    # -O1 not -O0: at -O0 clang emits far more stack traffic, and the point of the
    # second-implementation oracle is to compare a *realistically optimised* build
    # against the native one, since UB is exactly what optimisers exploit differently.
    if tc.get("sysroot"):
        cflags = ["--target=wasm32-wasi", "--sysroot=" + tc["sysroot"], "-O1",
                  "-Wno-everything"]
    else:
        cflags = ["--target=wasm32", "-O1", "-nostdlib", "-fno-builtin",
                  "-Wno-everything"]
    for s in srcs:
        o = os.path.join(work, re.sub(r'[^A-Za-z0-9_]', '_', os.path.basename(s)) + ".o")
        r = subprocess.run([tc["clang"]] + cflags + ["-c", s, "-o", o],
                           capture_output=True, text=True, env=env, timeout=180)
        if r.returncode == 0 and os.path.exists(o):
            objs.append(o)
        else:
            failed[os.path.basename(s)] = (r.stderr or "")[-200:]
    info = {"sources": len(srcs), "compiled": len(objs),
            "compile_failed": len(failed),
            "compile_failed_detail": dict(list(failed.items())[:10])}
    if not objs:
        info["error"] = "no C source compiled to wasm32"
        return None, info
    out = os.path.join(work, "autoform_diff.wasm")
    # `--no-entry`: the harness calls individual exported functions, there is no `main`.
    # `--export-all`: which functions the AST names is decided at run time, not here.
    # `--allow-undefined`: an unresolved symbol becomes an import, which `wasm_run.mjs`
    # either implements or records as `unsupported-import` -- one missing compiler-rt
    # helper must not zero out the whole corpus.
    link = [tc["wasm_ld"], "--no-entry", "--export-all", "--allow-undefined"]
    if tc.get("libdir"):
        link += ["-L", tc["libdir"]]
    link += objs + (["-lc"] if tc.get("libdir") else []) + ["-o", out]
    r = subprocess.run(link, capture_output=True, text=True, env=env, timeout=300)
    if r.returncode != 0 or not os.path.exists(out):
        info["error"] = "wasm-ld failed: " + (r.stderr or "")[-300:]
        return None, info
    info["wasm_bytes"] = os.path.getsize(out)
    return out, info


class WasmCaller:
    """Batch-executes calls against a wasm module via node, resuming past hangs.

    A wasm function can loop forever, and there is no fuel in the JS engine to stop it.
    The runner flushes one result line per request, so a timeout tells us exactly which
    id never answered: that one is recorded `timeout` and the batch resumes after it.
    Without that, one non-terminating function would swallow every later case in the
    batch and the run would silently under-report.
    """

    def __init__(self, wasm_path, tc, work, timeout=20):
        self.wasm, self.tc, self.work, self.timeout = wasm_path, tc, work, timeout

    def run(self, calls):
        """calls: [{"id":int,"name":str,"args":[int,...]}] -> {id: result-dict}"""
        results, pending, guard = {}, list(calls), 0
        while pending and guard < 200:
            guard += 1
            req = os.path.join(self.work, "wasm_req_%d.json" % guard)
            with open(req, "w") as fh:
                json.dump(pending, fh)
            try:
                r = subprocess.run([self.tc["node"], RUNNER, self.wasm, req],
                                   capture_output=True, text=True,
                                   timeout=self.timeout + 2 * len(pending))
                out, timed_out = r.stdout, False
            except subprocess.TimeoutExpired as e:
                out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) \
                    else (e.stdout or "")
                timed_out = True
            got = set()
            for line in out.splitlines():
                line = line.strip()
                if not line.startswith("{"): continue
                try:
                    d = json.loads(line)
                except ValueError:
                    continue
                results[d["id"]] = d
                got.add(d["id"])
            rest = [c for c in pending if c["id"] not in got]
            if not rest:
                break
            if not timed_out and len(rest) == len(pending):
                # node died without answering anything: stop rather than spin.
                for c in rest:
                    results[c["id"]] = {"id": c["id"], "status": "error",
                                        "reason": "runner produced no output"}
                break
            # the first unanswered call is the one that hung (or crashed node).
            results[rest[0]["id"]] = {"id": rest[0]["id"], "status": "timeout"}
            pending = rest[1:]
        return results


# ------------------------------------------------------------------- UB adjudication

def adjudicate(native, wasm, native2=None):
    """Compare one native result with one wasm result for the same call.

    `native` is the int the `cc` backend returned, or None if the native call crashed
    or hung. `native2` is the same native call made a second time in the same child (see
    `call_in_child_twice`). `wasm` is a runner result dict.

    Returns (kind, detail). Kinds:
      agree              both ran, same value
      ub-suspected       both ran, different values, and the difference is NOT explained
                         by addresses or nondeterminism -- two conforming C
                         implementations genuinely disagree, so the program depends on
                         undefined behaviour
      address-valued     both ran and differ, but the result is a pointer: native
                         reports a 64-bit process address, wasm a 32-bit linear-memory
                         offset. A representation difference between two address spaces,
                         carrying no information about the program's semantics.
      nondeterministic   the native call returned different values on two consecutive
                         identical invocations, so there is nothing stable to compare
      trap               wasm trapped; the sandbox caught what natively segfaults
      native-crash       native died, wasm produced a value
      unsupported        wasm could not run it (missing export, libc import, i64)
      incomparable       neither side produced anything usable

    On suppression: `address-valued` and `nondeterministic` are not a way to make an
    inconvenient disagreement go away. They are counted, reported with examples, and
    kept out of BOTH the UB tally and the Lean comparison, because in each case the
    harness has positive evidence that the two numbers are not answers to the same
    question. What is never done is the reverse -- declining a case *because* the two
    implementations disagreed about a value.
    """
    ws = wasm.get("status") if wasm else None
    if ws == "val" and native is not None:
        wv, nv = int(wasm["value"]), int(native)
        if wv == nv:
            return "agree", None
        # Discriminator 1: the native side is not even self-consistent.
        if native2 is not None and native2 != nv:
            return "nondeterministic", {"native": nv, "native_again": native2,
                                        "wasm": wv}
        # Discriminator 2: both values look like addresses in their own address space.
        # A wasm pointer lands inside linear memory; a native heap/static address is far
        # larger than any value this harness's small integer inputs can compute.
        mem = int(wasm.get("memBytes") or 0)
        if mem and 0 < wv < mem and abs(nv) > (1 << 24):
            return "address-valued", {"native": nv, "wasm": wv, "wasm_mem": mem}
        return "ub-suspected", {"native": nv, "wasm": wv}
    if ws == "trap":
        return "trap", {"kind": wasm.get("kind"), "message": wasm.get("message"),
                        "native": native}
    if ws == "val" and native is None:
        return "native-crash", {"wasm": int(wasm["value"])}
    if ws in ("unsupported", "missing"):
        return "unsupported", {"reason": wasm.get("reason", ws)}
    if ws == "timeout":
        return "unsupported", {"reason": "wasm-timeout"}
    return "incomparable", {"wasm": ws, "native": native}


_WIDTH_TYPES = re.compile(
    r'\b(long|size_t|ssize_t|uintptr_t|intptr_t|ptrdiff_t|off_t|time_t)\b')


def width_sensitive_functions(src_root):
    """Names of C functions whose text mentions a pointer-width type.

    wasm32 has 32-bit `long`/`size_t`/pointers; the native build here is 64-bit. A
    function using those types will legitimately compute different values on the two
    targets WITHOUT any undefined behaviour -- that is a `NumConfig` difference, and it
    is precisely the width axis `Autoform/Lang/Core/Numeric.lean` models. Counting those
    as UB would inflate the headline number with results that are fully defined on both
    targets, so they are separated out and reported under their own key.

    This is a lexical scan, not a parse: it over-approximates (a function that merely
    mentions `long` in a comment is flagged) on purpose, because the failure that
    matters is claiming UB where there is none.
    """
    import glob as _glob
    names = set()
    for p in _glob.glob(os.path.join(src_root, "**", "*.c"), recursive=True) + \
            _glob.glob(os.path.join(src_root, "**", "*.h"), recursive=True):
        try:
            text = open(p, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        # crude brace-matched slice per top-level definition
        for m in re.finditer(r'^[A-Za-z_][\w \t\*]*?\b(\w+)\s*\([^;{]*\)\s*\{',
                             text, re.M):
            name, i, depth = m.group(1), m.end() - 1, 0
            for j in range(i, min(len(text), i + 20000)):
                if text[j] == '{': depth += 1
                elif text[j] == '}':
                    depth -= 1
                    if depth == 0: break
            sig_and_body = text[m.start():j + 1]
            if _WIDTH_TYPES.search(sig_and_body):
                names.add(name)
    return names


def classify_ub(fname, args, native, wasmv, src_text=None):
    """A best-effort reading of WHICH undefined behaviour a disagreement smells like.

    This is a hint for a human, explicitly labelled as such in the output. The finding
    that two conforming implementations disagree stands on its own; the attribution
    below does not, and must not be reported as if it did.
    """
    I32 = 1 << 31
    hints = []
    if native is not None and (native - wasmv) % (1 << 32) == 0 and native != wasmv:
        hints.append("width: values agree mod 2^32 -- native `long`/pointer is 64-bit, "
                     "wasm32 is 32-bit (a NumConfig difference, not necessarily UB)")
    if any(abs(a) >= 1 << 16 for a in args if isinstance(a, int)):
        hints.append("large operands: signed overflow in a multiply/add is plausible")
    if any(0 <= a < 64 for a in args if isinstance(a, int)) and \
            any(a >= 32 for a in args if isinstance(a, int)):
        hints.append("shift-past-width: an argument in [32,64) used as a shift count "
                     "is UB for a 32-bit type and differs by target")
    if native is not None and (native >= I32 or native < -I32):
        hints.append("native result exceeds int32 -- the C returns a wider type than "
                     "the harness's int model")
    if not hints:
        hints.append("unattributed: could be uninitialised read, strict aliasing, or "
                     "an argument that is really a pointer (layout differs by target)")
    return hints
