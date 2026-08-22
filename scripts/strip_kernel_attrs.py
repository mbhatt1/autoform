#!/usr/bin/env python3
"""strip_kernel_attrs.py — remove GCC/kernel attributes that defeat Joern's C parser.

Joern parses C WITHOUT running the preprocessor, so a definition like

    static int __init setup_early_mem_profiling(char *str) { ... }

fails to parse and the whole FUNCTION is dropped — not translated into a hole, but absent
from the corpus entirely. On Linux `lib/` that was 574 functions, and no amount of work on
the semantics reaches a function the front end never produced.

The attributes stripped here carry no execution semantics:

  * `__init` / `__exit` / `__initdata` — ELF section placement.
  * `__user` / `__kernel` / `__iomem` / `__rcu` / `__percpu` — sparse annotations, no codegen.
  * `__weak` / `__visible` / `__used` — linkage.
  * `__cold` / `__pure` / `__must_check` / `__maybe_unused` — optimiser and warning hints.
  * `__printf(m,n)` / `__section(...)` / `__aligned(n)` / `__attribute__((...))` — likewise.

None of them changes what the function body computes, which is the only thing the
translation models. Stripping is therefore not an approximation; it removes text the
semantics never depended on.

It is NOT a substitute for a real preprocessed build. Macros that expand to *code* —
`MODULE_LICENSE`, `TEST_SPINLOCK_COMMON`, `DEFINE_SPINLOCK` — are untouched here and remain
`stmt:UNKNOWN`. Getting those right needs cpp with the kernel's own headers and config.

This rewrites a COPY. Never point it at a source tree you care about.

Usage: scripts/strip_kernel_attrs.py <staging-dir>
"""
from __future__ import annotations
import glob, os, re, sys

ATTRS = ['__init', '__exit', '__initdata', '__initconst', '__exitdata', '__ref', '__cold',
         '__must_check', '__weak', '__maybe_unused', '__always_inline', '__pure', '__used',
         '__read_mostly', '__attribute_const__', '__noreturn', '__visible', '__force',
         '__user', '__kernel', '__iomem', '__percpu', '__rcu', '__private']
BARE = re.compile(r'(?<![A-Za-z0-9_])(' + '|'.join(map(re.escape, ATTRS)) + r')(?![A-Za-z0-9_])')
PARAM = re.compile(r'(?<![A-Za-z0-9_])(__printf|__scanf|__section|__alias|__aligned'
                   r'|__attribute__)\s*\(\(?[^()]*\)?\)')


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    root = sys.argv[1]
    if not os.path.isdir(root):
        print(f"strip_kernel_attrs: {root} is not a directory", file=sys.stderr)
        return 2
    n = files = 0
    for f in glob.glob(os.path.join(root, "**", "*.c"), recursive=True) + \
             glob.glob(os.path.join(root, "**", "*.h"), recursive=True):
        s = open(f, errors="replace").read()
        t = BARE.sub(" ", PARAM.sub(" ", s))
        if t != s:
            open(f, "w").write(t)
            files += 1
            n += len(BARE.findall(s)) + len(PARAM.findall(s))
    print(f"strip_kernel_attrs: removed {n} attribute occurrence(s) from {files} file(s) "
          f"under {root}")
    print("  Provenance: any AST exported from this tree is from ATTRIBUTE-STRIPPED "
          "sources. Record that alongside the Joern version.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
