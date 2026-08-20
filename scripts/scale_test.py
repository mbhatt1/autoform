#!/usr/bin/env python3
"""scale_test.py — does the pipeline survive a codebase larger than `cachetools`?

Every published number in this repo comes from one 1,637-line corpus. This script runs
the *same* pipeline stage by stage on arbitrary source trees and records wall-clock,
peak RSS, artifact sizes and hole/coverage counts for each stage separately, so a
failure can be attributed to a stage rather than to "the pipeline".

Differences from `autoform.sh`, all of them deliberate:

* every stage gets its own timeout and its own timing/RSS record, and a stage that fails
  is recorded with its exit status, elapsed time and the tail of its stderr rather than
  aborting the run — a hard failure at a known input size *is* the measurement;
* nothing is written to the repo except `Autoform/Generated/<Module>.lean`, which
  `lake build` requires to live there. `formalization-graph.json`, the neutral AST and
  the ledger JSON go to the scratch directory, so a scale run cannot clobber the
  committed artifacts of the `cachetools` run;
* the generated module is removed again unless `--keep` is given.

Peak RSS comes from `/usr/bin/time -l` (macOS) or `-v` (GNU); it is the peak of the
whole child process tree for that stage, which for the Joern stages is a JVM.

Usage:
    scripts/scale_test.py --out results.json \
        --target Sqlparse /path/to/sqlparse \
        --target Requests /path/to/requests
    scripts/scale_test.py --report results.json     # re-print the table
"""
from __future__ import annotations

import argparse, json, os, re, shutil, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
JOERN = os.path.join(os.environ.get("JOERN_HOME", os.path.expanduser("~/joern")), "joern-cli")

# Generous, and recorded: a timeout is a result, but only if the limit is stated.
TIMEOUTS = {"parse": 3600, "graph": 3600, "export": 3600, "render": 900,
            "build": 5400, "ledger": 3600}


# ---------------------------------------------------------------------------
# running a stage
# ---------------------------------------------------------------------------

def _time_cmd(cmd: list[str]) -> list[str]:
    """Wrap a command in /usr/bin/time so we get peak RSS of the whole child tree."""
    if not os.path.exists("/usr/bin/time"):
        return cmd
    flag = "-l" if sys.platform == "darwin" else "-v"
    return ["/usr/bin/time", flag] + cmd


_RSS_PATTERNS = [
    re.compile(r"(\d+)\s+maximum resident set size"),       # BSD/macOS: bytes
    re.compile(r"Maximum resident set size[^:]*:\s*(\d+)"),  # GNU: kbytes
]


def _peak_rss_mb(stderr: str) -> float | None:
    for i, pat in enumerate(_RSS_PATTERNS):
        m = pat.search(stderr)
        if m:
            v = int(m.group(1))
            return round(v / (1 << 20), 1) if i == 0 else round(v / 1024, 1)
    return None


def run_stage(name: str, cmd: list[str], cwd: str, timeout: int) -> dict:
    """Run one pipeline stage. Never raises: a failure is data."""
    t0 = time.time()
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    try:
        p = subprocess.run(_time_cmd(cmd), cwd=cwd, env=env, timeout=timeout,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        elapsed, rc, out, err = time.time() - t0, p.returncode, p.stdout, p.stderr
        timed_out = False
    except subprocess.TimeoutExpired as e:
        elapsed, rc, timed_out = time.time() - t0, None, True
        out, err = e.stdout or b"", e.stderr or b""
    o = out.decode("utf-8", "replace")
    e = err.decode("utf-8", "replace")
    rec = {"stage": name, "seconds": round(elapsed, 1), "returncode": rc,
           "timed_out": timed_out, "timeout_limit": timeout,
           "peak_rss_mb": _peak_rss_mb(e),
           "ok": (rc == 0 and not timed_out),
           "stdout_tail": o[-6000:]}
    if not rec["ok"]:
        rec["stderr_tail"] = e[-4000:]
    status = "ok" if rec["ok"] else ("TIMEOUT" if timed_out else f"FAIL rc={rc}")
    print(f"    {name:<8} {rec['seconds']:>8.1f}s  rss="
          f"{rec['peak_rss_mb'] or '?':>8}MB  {status}", flush=True)
    return rec


# ---------------------------------------------------------------------------
# measuring the inputs and the artifacts
# ---------------------------------------------------------------------------

def source_size(src: str) -> dict:
    files = lines = 0
    for dirpath, dirnames, names in os.walk(src):
        dirnames[:] = [d for d in dirnames if d != ".git"]
        for n in names:
            if not n.endswith((".py", ".c", ".h", ".java")):
                continue
            files += 1
            try:
                with open(os.path.join(dirpath, n), "rb") as fh:
                    lines += fh.read().count(b"\n")
            except OSError:
                pass
    return {"source_files": files, "source_lines": lines}


def ast_stats(path: str) -> dict:
    """Shape of the neutral AST: node count and maximum term depth per function.

    Depth matters independently of size: the renderer emits one Lean term per function,
    so a deep AST becomes a deeply nested single term, which is what would stress Lean's
    elaborator.
    """
    with open(path) as fh:
        funcs = json.load(fh)

    def walk(n, d=1):
        """Iterative so a deep AST cannot blow *this* script's stack too."""
        nodes, deepest, stack = 0, d, [(n, d)]
        while stack:
            x, dd = stack.pop()
            if isinstance(x, dict):
                nodes += 1
                deepest = max(deepest, dd)
                for v in x.values():
                    if isinstance(v, (dict, list)):
                        stack.append((v, dd + 1))
            elif isinstance(x, list):
                for v in x:
                    if isinstance(v, (dict, list)):
                        stack.append((v, dd))
        return nodes, deepest

    total_nodes, max_depth, holes = 0, 0, 0
    for f in funcs:
        n, d = walk(f.get("body", {}))
        total_nodes += n
        max_depth = max(max_depth, d)
    blob = json.dumps(funcs)
    holes = blob.count('"k": "hole"') + blob.count('"k":"hole"') \
        + blob.count('"k": "holeS"') + blob.count('"k":"holeS"')
    return {"ast_functions": len(funcs), "ast_nodes": total_nodes,
            "ast_max_depth": max_depth, "ast_holes_raw": holes,
            "ast_bytes": os.path.getsize(path)}


def lean_stats(path: str) -> dict:
    if not os.path.exists(path):
        return {}
    with open(path, "rb") as fh:
        data = fh.read()
    lines = data.split(b"\n")
    return {"lean_bytes": len(data), "lean_lines": len(lines),
            "lean_longest_line": max((len(x) for x in lines), default=0)}


LEDGER_KEYS = ["functions", "holeFree", "callClosed", "holes"]


def parse_ledger(text: str, scratch: str, mod: str) -> dict:
    """Pull the coverage numbers out of the ledger stage.

    Prefers the JSON the template writes; falls back to the printed report, because a
    ledger that printed but failed to write is still a measurement.
    """
    out = {}
    jpath = os.path.join(scratch, f"ledger-{mod}.json")
    if os.path.exists(jpath):
        try:
            j = json.load(open(jpath))
            for k, v in j.items():
                if isinstance(v, (int, float, str)):
                    out["ledger_" + k] = v
        except (ValueError, OSError):
            pass
    for k in LEDGER_KEYS:
        m = re.search(rf"{k}\D{{0,20}}(\d+)", text)
        if m and ("ledger_" + k) not in out:
            out["ledger_" + k] = int(m.group(1))
    return out


# ---------------------------------------------------------------------------
# one target, end to end
# ---------------------------------------------------------------------------

def run_target(name: str, src: str, scratch: str, keep: bool) -> dict:
    print(f"\n== {name}  ({src})", flush=True)
    work = os.path.join(scratch, name)
    os.makedirs(work, exist_ok=True)
    cpg = os.path.join(work, "cpg.bin")
    ast = os.path.join(work, "ast.json")
    gen = os.path.join(ROOT, "Autoform", "Generated", f"{name}.lean")

    r = {"target": name, "source": src, "stages": []}
    r.update(source_size(src))
    print(f"   {r['source_lines']} lines in {r['source_files']} files", flush=True)

    def stage(sn, cmd, cwd=work, to=None):
        rec = run_stage(sn, cmd, cwd, to or TIMEOUTS[sn])
        r["stages"].append(rec)
        return rec["ok"]

    # 1. Joern parse. Run from `work` so Joern's `workspace/` lands in scratch, not the repo.
    if not stage("parse", [os.path.join(JOERN, "joern-parse"), src, "--output", cpg]):
        return r
    if os.path.exists(cpg):
        r["cpg_bytes"] = os.path.getsize(cpg)

    # 2. Cartographer. Output goes to scratch: the repo copy belongs to the cachetools run.
    stage("graph", [os.path.join(JOERN, "joern"), "--script",
                    os.path.join(ROOT, "cartographer", "formalization_graph.sc"),
                    "--param", f"cpgPath={cpg}",
                    "--param", f"out={os.path.join(work, 'formalization-graph.json')}"])
    fg = os.path.join(work, "formalization-graph.json")
    if os.path.exists(fg):
        r["graph_bytes"] = os.path.getsize(fg)

    # 3. Export the neutral AST.
    if not stage("export", [os.path.join(JOERN, "joern"), "--script",
                            os.path.join(ROOT, "cartographer", "export_ast.sc"),
                            "--param", f"cpgPath={cpg}", "--param", f"out={ast}"]):
        return r
    if os.path.exists(ast):
        try:
            r.update(ast_stats(ast))
        except (ValueError, RecursionError, MemoryError) as e:
            r["ast_stats_error"] = f"{type(e).__name__}: {e}"

    # 4. Render Lean.
    if not stage("render", [sys.executable,
                            os.path.join(ROOT, "cartographer", "render_lean.py"),
                            ast, gen, name]):
        return r
    r.update(lean_stats(gen))

    # 5. Elaborate. This is the stage most likely to break on a deep term.
    try:
        ok = stage("build", ["lake", "build", f"Autoform.Generated.{name}"], cwd=ROOT)

        # 6. Ledger — coverage numbers. Runs in scratch so its JSON lands there.
        if ok:
            tmpl = open(os.path.join(ROOT, "scripts", "ledger.lean.tmpl")).read()
            lpath = os.path.join(work, "Ledger.lean")
            with open(lpath, "w") as fh:
                fh.write(tmpl.replace("@MODULE@", name))
            # `lake env lean` prints the ledger report on stdout; run_stage keeps it.
            rec = run_stage("ledger", ["lake", "env", "lean", lpath], work,
                            TIMEOUTS["ledger"])
            r["stages"].append(rec)
            text = rec.get("stdout_tail", "")
            r["ledger_text"] = text
            r.update(parse_ledger(text, work, name))
    finally:
        if not keep and os.path.exists(gen):
            os.remove(gen)
            olean = os.path.join(ROOT, ".lake", "build", "lib", "lean", "Autoform",
                                 "Generated", f"{name}.olean")
            for ext in (".olean", ".ilean", ".trace", ".c", ".o"):
                p2 = olean.replace(".olean", ext)
                if os.path.exists(p2):
                    os.remove(p2)
    return r


# ---------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------

def fmt_table(results: list[dict]) -> str:
    def sec(r, s):
        for st in r["stages"]:
            if st["stage"] == s:
                if st["timed_out"]:
                    return "TIMEOUT"
                return f"{st['seconds']:.0f}" if st["ok"] else "FAIL"
        return "—"

    hdr = ("| target | src lines | funcs | AST MB | Lean MB | parse | export | render "
           "| build | ledger | peak RSS |")
    rows = [hdr, "|" + "---|" * 11]
    for r in results:
        rss = max((st.get("peak_rss_mb") or 0 for st in r["stages"]), default=0)
        rows.append("| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |".format(
            r["target"], r.get("source_lines", "?"), r.get("ast_functions", "?"),
            round(r.get("ast_bytes", 0) / 1e6, 1), round(r.get("lean_bytes", 0) / 1e6, 1),
            sec(r, "parse"), sec(r, "export"), sec(r, "render"),
            sec(r, "build"), sec(r, "ledger"), f"{rss:.0f}"))
    return "\n".join(rows)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--target", nargs=2, action="append", metavar=("NAME", "SRC"),
                    default=[], help="module name and source directory; repeatable")
    ap.add_argument("--scratch", default=tempfile.gettempdir(),
                    help="where CPGs, ASTs and Joern's workspace/ go")
    ap.add_argument("--out", default="scale-results.json")
    ap.add_argument("--keep", action="store_true",
                    help="keep Autoform/Generated/<Name>.lean after the run")
    ap.add_argument("--report", help="print the table for an existing results file")
    args = ap.parse_args()

    if args.report:
        print(fmt_table(json.load(open(args.report))["results"]))
        return 0
    if not args.target:
        ap.error("give at least one --target NAME SRC (or --report FILE)")

    os.makedirs(args.scratch, exist_ok=True)
    results = []
    for name, src in args.target:
        results.append(run_target(name, os.path.abspath(src), args.scratch, args.keep))
        with open(args.out, "w") as fh:
            json.dump({"results": results}, fh, indent=2)
    # Joern drops a workspace/ wherever it is invoked from; the repo must stay clean.
    stray = os.path.join(ROOT, "workspace")
    if os.path.isdir(stray):
        shutil.rmtree(stray)
    print("\n" + fmt_table(results))
    print(f"\nwrote {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
