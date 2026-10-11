"""Replays the Linux `lcm()` overflow (kernel commit 74a5fef7cb08, docs/evidence-linux-lcm.md).

Pre-fix  7b212edf86e28f4d0198f2152b2f0553f51a59a5  `return (a * b) / gcd(a, b);`
Post-fix 74a5fef7cb0839c6b595f90c7914a62ac9d0bcf9  `return (a / gcd(a, b)) * b;`

Tracked inputs: the four kernel sources (tests/fixtures/defect/linux_lcm/{prefix,postfix}),
the pre-fix AST (ast-LinuxLcmPrefix.json + provenance record) and the recorded divergence
rows (tests/fixtures/defect/linux_lcm/recorded-cross-revision.json, extracted from the run's gitignored conformance.json).  Not tracked: the kernel
include skeleton, taken from the digest-pinned sparse clone ~/.cache/autoform/corpora/linux-v7.2.
A missing skeleton, C compiler or Lean toolchain is a named SKIP, never a pass.
"""
import json
import math
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
FIX = ROOT / "tests" / "fixtures" / "defect" / "linux_lcm"
CORPORA = Path(os.path.expanduser("~/.cache/autoform/corpora"))
SKELETON = CORPORA / "linux-v7.2"
ROW = ROOT / "tests" / "fixtures" / "defect" / "linux_lcm" / "recorded-cross-revision.json"
AST = ROOT / "ast-LinuxLcmPrefix.json"
M64 = 1 << 64


def test_fixture_is_exactly_the_one_line_fix():
    pre = (FIX / "prefix/lib/lcm.c").read_text().splitlines()
    post = (FIX / "postfix/lib/lcm.c").read_text().splitlines()
    changed = [(a.strip(), b.strip()) for a, b in zip(pre, post) if a != b]
    assert len(pre) == len(post)
    assert changed == [("return (a * b) / gcd(a, b);", "return (a / gcd(a, b)) * b;")]
    assert (FIX / "prefix/lib/gcd.c").read_bytes() == (FIX / "postfix/lib/gcd.c").read_bytes()


def test_recorded_divergence_rows_name_lcm_and_expect_the_post_fix_value():
    row = json.loads(ROW.read_text())
    assert row["divergences"] == len(row["divergence_detail"]) > 0
    assert {d["function"] for d in row["divergence_detail"]} == {"lcm"}
    fits = 0
    for d in row["divergence_detail"]:
        a, b = (v for _, v in d["case"]["args"])
        expected = d["observation"]["outcome"][1][1]          # what the post-fix native code returned
        assert expected == (a // math.gcd(a, b)) * b % M64     # i.e. the post-fix formula
        assert d["lean_repr"] != "Autoform.Core.EResult.val (Autoform.Core.Val.int %d)" % expected
        if a * b // math.gcd(a, b) < M64:                      # the true lcm fits: the fix's claim
            assert expected == a * b // math.gcd(a, b)
            fits += 1
    assert fits >= 1


def _tree(tmp_path, revision):
    root = tmp_path / revision
    root.mkdir()
    for name in ("Kbuild", "Kconfig", "Makefile", "include", "tools"):
        src = SKELETON / name
        shutil.copytree(src, root / name) if src.is_dir() else shutil.copy(src, root / name)
    shutil.copytree(FIX / revision / "lib", root / "lib")
    return root


def _native(differential, tree):
    fs = [dict(name=n, sourceName=n, file=n + ".c", params=["a", "b"],
               paramIntegerTypes=["u64", "u64"], returnIntegerType="u64") for n in ("gcd", "lcm")]
    lib = differential.c_runtime(str(tree / "lib"), fs)
    assert lib.info["files_compiled"] == 2, lib.info
    return lib(fs[1])


@pytest.mark.skipif(shutil.which("cc") is None, reason="C compiler unavailable")
@pytest.mark.skipif(not (SKELETON / "include/linux/kernel.h").is_file(),
                    reason="kernel v7.2 sparse skeleton absent under ~/.cache/autoform/corpora/linux-v7.2")
def test_native_prefix_wraps_and_postfix_does_not(tmp_path, differential):
    pre = _native(differential, _tree(tmp_path, "prefix"))
    post = _native(differential, _tree(tmp_path, "postfix"))
    assert pre(1 << 32, 1 << 32) == 0 and post(1 << 32, 1 << 32) == 1 << 32
    assert pre(1 << 63, 2) == 0 and post(1 << 63, 2) == 1 << 63
    assert pre(4, 6) == post(4, 6) == 12 and pre(0, 6) == post(0, 6) == 6


@pytest.mark.skipif(not os.environ.get("AUTOFORM_TEST_LEAN"),
                    reason="set AUTOFORM_TEST_LEAN=1 to render + lake build + run the oracle (needs elan, cc)")
@pytest.mark.skipif(shutil.which("cc") is None, reason="C compiler unavailable")
@pytest.mark.skipif(not (SKELETON / "include/linux/kernel.h").is_file(),
                    reason="kernel v7.2 sparse skeleton absent under ~/.cache/autoform/corpora/linux-v7.2")
def test_lean_model_of_the_prefix_revision_diverges_from_postfix_native(tmp_path):
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ["PATH"])
    py = sys.executable
    run = lambda *a, cwd=ROOT: subprocess.run(a, cwd=cwd, env=env, capture_output=True, text=True)
    r = run(py, "cartographer/render_lean.py", str(AST), "Autoform/Generated/LinuxLcmPrefix.lean",
            "LinuxLcmPrefix", "--shard-functions", "0")
    assert r.returncode == 0, r.stdout + r.stderr
    r = run("lake", "build", "Autoform.Generated.LinuxLcmPrefix")
    assert r.returncode == 0, (r.stdout + r.stderr)[-1500:]
    out = tmp_path / "out"
    out.mkdir()
    r = run(py, str(ROOT / "scripts/differential.py"), str(AST), str(_tree(tmp_path, "postfix") / "lib"),
            "LinuxLcmPrefix", "100", "--no-cache", cwd=out)
    assert r.returncode == 1, r.stdout[-1500:]          # 1 = divergences found
    row = json.loads((out / "conformance.json").read_text())
    assert row["divergences"] > 0
    lcm = [d for d in row["divergence_detail"] if d["function"] == "lcm"]
    assert lcm and all(d["function"] == "lcm" for d in row["divergence_detail"])
    witnesses = [d for d in lcm if (lambda a, b: a * b // math.gcd(a, b) < M64)(*(v for _, v in d["case"]["args"]))]
    assert witnesses and all(d["lean_repr"].endswith("(Autoform.Core.Val.int 0)") for d in witnesses)
