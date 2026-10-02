#!/usr/bin/env python3
"""Build a runnable conformance sample of SQLite functions for scripts/differential.py.

    scripts/sqlite_sample.py <ast.json> <tree> <sqlite3.c> <outdir> [--n 100]

<ast.json> is the full-tree export (scripts/sqlite_corpus.sh), <tree> the source tree it
was parsed from (with the generated sqlite3.h), <sqlite3.c> the amalgamation of the SAME
checkout (`./configure && make sqlite3.c`; see docs/scale.md). Writes

    <outdir>/ast-<Module>.json   the sample: roots plus their transitive callees
    <outdir>/csrc/sample.c       the C side differential.py compiles with `cc`
    <outdir>/sample.json         why every candidate was kept or refused

The hole-free census is a static upper bound. This picks the subset that can actually be
EXECUTED on both sides with nothing invented, and refuses everything else:

* hole-free (no `hole`/`holeS` node, the same test differential.py uses);
* every C parameter and the return type is a plain integer type (`int`, `unsigned`,
  `u8`..`u64`, `i8`..`i64`, `sqlite3_int64`, ...; see INT_TYPES). The AST carries no C
  types and differential.py's C leg passes and returns `c_int`, so the generated wrapper
  is `int f(int ...)` and REFUSES (aborts, which differential.py counts as a skipped
  native call) any argument the real parameter type cannot hold and any result `int`
  cannot hold. Only calls where no conversion changes a value are compared; a pointer or
  floating parameter is refused outright. The signature is read from the definition in
  the source tree; a name with zero or several definitions in its file is refused
  (ambiguous configuration);
* the body has no preprocessor line: then the function text is the same under the
  configuration Joern parsed and the one the amalgamation is compiled with;
* the function reads no name that is neither a parameter nor assigned in its own body
  (a global, an enum constant, a macro c2cpg could not expand) -- Lean would need module
  state the sample does not carry, and the C side would read the real global;
* every call target is itself a sample candidate (transitively), so the sample module is
  call-closed by construction, and each callee is also integer-typed and runnable;
* the function is defined in a file that is part of the amalgamation, AND the
  amalgamation's default configuration actually compiles it (checked by building the
  candidates once and reading `nm`; FTS3/RTREE/... are opt-in there).

Selection is deterministic: candidates are ordered by sha256 of their name and the first
`--n` roots are taken (plus their callees, which are candidates by construction).

The C side: `sample.c` renames every sampled function with a macro, includes the
amalgamation, and defines an exported `int f(int...)` wrapper under the original name
that calls the renamed one. The function body that runs is SQLite's own, compiled from
the same checkout; static functions become callable through ctypes without editing them.
"""
import argparse, hashlib, json, os, re, subprocess, sys, threading

sys.setrecursionlimit(1_000_000)
threading.stack_size(1 << 29)


def walk(n):
    stack = [n]
    while stack:
        x = stack.pop()
        if isinstance(x, dict):
            yield x
            stack.extend(x.values())
        elif isinstance(x, list):
            stack.extend(x)


def has_hole(body):
    return any(x.get("k") in ("hole", "holeS") for x in walk(body))


STORAGE = {"static", "SQLITE_PRIVATE", "SQLITE_API", "SQLITE_NOINLINE", "inline",
           "__inline", "SQLITE_INLINE", "SQLITE_EXPERIMENTAL", "SQLITE_DEPRECATED",
           "SQLITE_CDECL", "SQLITE_STDCALL", "SQLITE_APICALL", "SQLITE_SYSAPI"}


def definitions(text, name):
    """(return-type tokens, param list text, body text) for each definition of `name`."""
    out = []
    # Definition: a line that starts with the return type (or the name on its own line
    # after a type line), the name, the parameter list, then `{`.
    pat = re.compile(r'(?m)^([A-Za-z_][\w \t\*]*?)\b' + re.escape(name)
                     + r'\s*\(([^;{}()]*)\)\s*\{')
    for m in pat.finditer(text):
        ret = m.group(1)
        # brace-match the body
        i, depth = m.end() - 1, 0
        while i < len(text):
            c = text[i]
            if c == '{': depth += 1
            elif c == '}':
                depth -= 1
                if depth == 0: break
            i += 1
        out.append((ret.split(), m.group(2), text[m.end():i]))
    return out


# Integer types whose values an `int` argument can carry exactly when it is in range.
INT_TYPES = {"int", "signed", "signed int", "unsigned", "unsigned int", "short",
             "short int", "unsigned short", "unsigned short int", "long", "long int",
             "unsigned long", "unsigned long int", "long long", "long long int",
             "unsigned long long", "unsigned long long int", "char", "signed char",
             "unsigned char", "u8", "u16", "u32", "u64", "i8", "i16", "i64", "LogEst",
             "tRowcnt", "Pgno", "sqlite_int64", "sqlite_uint64", "sqlite3_int64",
             "sqlite3_uint64"}
PARAM = re.compile(r'\s*(?:const\s+)?([A-Za-z_][\w ]*?)\s+([A-Za-z_]\w*)\s*')


def int_signature(ret_toks, params):
    """([(ctype, name)], return ctype) for an all-integer signature, else (None, why)."""
    ret = " ".join(t for t in ret_toks if t not in STORAGE)
    if ret not in INT_TYPES:
        return None, "return type %s" % ret
    if params.strip() in ("", "void"):
        return None, "no parameters"
    out = []
    for p in params.split(","):
        m = PARAM.fullmatch(p.replace("\n", " "))
        if not m or " ".join(m.group(1).split()) not in INT_TYPES:
            return None, "parameter `%s`" % " ".join(p.split())
        out.append((" ".join(m.group(1).split()), m.group(2)))
    return (out, ret), None


def names_read_and_bound(body):
    reads, bound, calls = set(), set(), set()
    for x in walk(body):
        k = x.get("k")
        if k == "name": reads.add(x.get("v"))
        elif k in ("assign", "forIn", "tryCatch"): bound.add(x.get("x"))
        elif k == "call": calls.add(x.get("f"))
        elif k in ("mcall", "fnref", "closure", "alloc", "setGlobal", "declGlobal",
                   "field", "setField", "boxNew", "boxFields", "boxArray"):
            calls.add(None)        # not leaf/pure: refuse below
    return reads, bound, calls


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ast"); ap.add_argument("tree"); ap.add_argument("amalg")
    ap.add_argument("outdir"); ap.add_argument("--n", type=int, default=100)
    ap.add_argument("--module", default="SqliteSample")
    a = ap.parse_args()

    funcs = json.load(open(a.ast))
    amal_files = set(re.findall(r'^/\*+ Begin file (\S+) \*+/$',
                                open(a.amalg, encoding="latin-1").read(), re.M))
    by_name = {}
    for f in funcs:
        by_name.setdefault(f["name"], []).append(f)

    texts, verdict, info = {}, {}, {}
    for f in funcs:
        nm = f["name"]
        if nm.endswith(":<global>"):
            continue
        if len(by_name[nm]) != 1:
            verdict[nm] = "name defined %d times in the AST" % len(by_name[nm]); continue
        if has_hole(f["body"]):
            verdict[nm] = "has holes"; continue
        rel = f.get("file", "")
        if os.path.basename(rel) not in amal_files:
            verdict[nm] = "file %s not in the amalgamation" % rel; continue
        path = os.path.join(a.tree, rel)
        if path not in texts:
            try: texts[path] = open(path, encoding="latin-1").read()
            except OSError: texts[path] = None
        if texts[path] is None:
            verdict[nm] = "source file unreadable"; continue
        defs = definitions(texts[path], nm)
        if len(defs) != 1:
            verdict[nm] = "%d textual definitions in %s" % (len(defs), rel); continue
        ret, params, body_txt = defs[0]
        sig, why = int_signature(ret, params)
        if why:
            verdict[nm] = "signature: " + why; continue
        ptypes, rtype = [t for t, _ in sig[0]], sig[1]
        pnames = [n for _, n in sig[0]]
        if pnames != list(f["params"]):
            verdict[nm] = "AST params %s != source %s" % (f["params"], pnames); continue
        if re.search(r'(?m)^\s*#', body_txt):
            verdict[nm] = "preprocessor directive in body"; continue
        reads, bound, calls = names_read_and_bound(f["body"])
        free = reads - bound - set(pnames)
        if free:
            verdict[nm] = "reads free name(s) %s" % sorted(free)[:5]; continue
        if None in calls:
            verdict[nm] = "object/closure/global construct in body"; continue
        info[nm] = {"file": rel, "params": pnames, "ptypes": ptypes, "ret": rtype,
                    "calls": sorted(calls)}
        verdict[nm] = "candidate"

    # transitive: every callee must be a candidate
    changed = True
    while changed:
        changed = False
        for nm in list(info):
            bad = [c for c in info[nm]["calls"] if c not in info]
            if bad:
                verdict[nm] = "calls non-candidate %s" % bad[:3]
                del info[nm]; changed = True

    os.makedirs(os.path.join(a.outdir, "csrc"), exist_ok=True)
    csrc = os.path.join(a.outdir, "csrc", "sample.c")

    def write_c(names):
        lines = ["/* Generated by scripts/sqlite_sample.py -- do not edit.",
                 " * Each sampled function is renamed by macro, the amalgamation is",
                 " * included unchanged, and an exported wrapper under the original name",
                 " * calls it. */"]
        for n in names:
            lines.append("#define %s %s__autoform_sqlite" % (n, n))
        lines.append('#include "%s"' % os.path.abspath(a.amalg))
        lines.append("#include <stdlib.h>")
        lines.append("#include <limits.h>")
        # IN-RANGE ONLY. differential.py passes and reads `c_int`. An argument the
        # parameter type cannot hold, or a result `int` cannot hold, is a value the
        # Lean side would see unconverted -- so the wrapper refuses it (abort), which
        # differential.py records as a skipped native call, never as a comparison.
        lines.append("#define AF_SIGNED(T) ((T)-1 < (T)0)")
        lines.append("#define AF_ARG_OK(T, a) (((a) >= 0 || AF_SIGNED(T)) && "
                     "(long long)(T)(a) == (long long)(a))")
        lines.append("#define AF_RET_OK(T, r) (AF_SIGNED(T) ? ((long long)(r) >= INT_MIN "
                     "&& (long long)(r) <= INT_MAX) : ((unsigned long long)(r) <= INT_MAX))")
        for n in names:
            ps, ts, rt = info[n]["params"], info[n]["ptypes"], info[n]["ret"]
            args = ", ".join("int a%d" % i for i in range(len(ps)))
            chk = " ".join("if (!AF_ARG_OK(%s, a%d)) abort();" % (t, i)
                           for i, t in enumerate(ts))
            call = "%s__autoform_sqlite(%s)" % (n, ", ".join(
                "(%s)a%d" % (t, i) for i, t in enumerate(ts)))
            lines += ["#undef %s" % n,
                      "int %s(%s){ %s %s r = %s; if (!AF_RET_OK(%s, r)) abort(); "
                      "return (int)r; }" % (n, args, chk, rt, call, rt)]
        open(csrc, "w").write("\n".join(lines) + "\n")

    # The amalgamation's DEFAULT configuration does not compile every file the tree
    # parse saw (FTS3, RTREE, ... are opt-in under SQLITE_CORE). Compile every candidate
    # once with the same `cc` command differential.py uses and keep only the ones whose
    # renamed body was actually defined; turning extensions on here would change the
    # configuration of every other function too.
    write_c(sorted(info))
    so = os.path.join(a.outdir, "probe.so")
    r = subprocess.run(["cc", "-shared", "-fPIC", "-O0", "-o", so, csrc],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit("cc failed on the probe build:\n" + r.stderr[-2000:])
    nm = subprocess.run(["nm", so], capture_output=True, text=True).stdout
    defined = set(m.group(1) for m in
                  re.finditer(r'^\S*\s+[tT]\s+(\w+)__autoform_sqlite$', nm, re.M))
    os.remove(so)
    for n in sorted(info):
        if n not in defined:
            verdict[n] = "not compiled by the amalgamation's default configuration"
            del info[n]
    changed = True
    while changed:
        changed = False
        for nm_ in list(info):
            bad = [c for c in info[nm_]["calls"] if c not in info]
            if bad:
                verdict[nm_] = "calls non-candidate %s" % bad[:3]
                del info[nm_]; changed = True

    order = sorted(info, key=lambda n: hashlib.sha256(n.encode()).hexdigest())
    roots = order[:a.n]
    closure, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in closure: continue
        closure.add(n); todo.extend(info[n]["calls"])
    sample = sorted(closure)
    ast_out = os.path.join(a.outdir, "ast-%s.json" % a.module)
    json.dump([by_name[n][0] for n in sample], open(ast_out, "w"), indent=1)
    write_c(sample)

    tally = {}
    for v in verdict.values():
        key = re.sub(r'[`(\[].*', '', v).strip()
        tally[key] = tally.get(key, 0) + 1
    report = {"ast": os.path.abspath(a.ast), "functions": len(verdict),
              "hole_free": sum(1 for v in verdict.values() if v != "has holes"),
              "candidates": len(info), "roots": roots, "sample": sample,
              "refusal_tally": dict(sorted(tally.items(), key=lambda kv: -kv[1])),
              "verdicts": verdict}
    json.dump(report, open(os.path.join(a.outdir, "sample.json"), "w"), indent=1)
    print("functions %d, hole-free %d, runnable int->int candidates %d, roots %d, "
          "sample (with callees) %d -> %s"
          % (report["functions"], report["hole_free"], len(info), len(roots),
             len(sample), ast_out))
    for k, v in list(report["refusal_tally"].items())[:15]:
        print("  %6d  %s" % (v, k))


t = threading.Thread(target=main); t.start(); t.join()
