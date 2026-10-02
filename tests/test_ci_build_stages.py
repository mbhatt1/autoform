"""The build job builds the library in stages, one V8Base part at a time, saving the cache
after every stage. Each of those properties exists because the single `lake build` it
replaced was killed by memory exhaustion partway through the heavy V8Base parts (runner
`shutdown signal`, exit 143) and lost its whole cache with it (STRATEGY.md section 67).
None of it can be run here, so these tests pin the shape of the workflow instead."""
import glob
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CI = os.path.join(ROOT, ".github", "workflows", "ci.yml")
SCRIPT = os.path.join(ROOT, "scripts", "ci_build_v8base_parts.sh")


def _build_job_steps():
    text = open(CI).read()
    body = text.split("\njobs:\n", 1)[1]
    jobs = re.split(r"(?m)^  ([a-z][a-z0-9-]*):\s*$", body)
    job = dict(zip(jobs[1::2], jobs[2::2]))["build-and-audit"]
    chunks = re.split(r"(?m)^      - ", job)[1:]
    steps = []
    for c in chunks:
        m = re.match(r"name:\s*(.*)", c)
        steps.append((m.group(1).strip() if m else "", c))
    return steps


def test_the_part_ranges_cover_every_v8base_part_exactly_once():
    ranges = []
    for _, c in _build_job_steps():
        m = re.search(r"run:\s*scripts/ci_build_v8base_parts\.sh\s+(\d+)\s+(\d+)", c)
        if m:
            ranges.append((int(m.group(1)), int(m.group(2))))
    assert ranges, "no step builds the V8Base parts"
    parts = len(glob.glob(os.path.join(ROOT, "Autoform", "SpecsGen", "V8Base", "Part*.lean")))
    covered = [n for a, b in ranges for n in range(a, b + 1)]
    assert covered == list(range(1, parts + 1)), (
        "the staged ranges %s do not cover Part1..Part%d exactly once, in order" % (ranges, parts))


def test_every_build_stage_is_followed_by_its_own_cache_save():
    steps = _build_job_steps()
    stages = [i for i, (n, _) in enumerate(steps) if n.startswith("lake build")]
    assert len(stages) >= 3
    for i in stages:
        name, _ = steps[i + 1]
        assert name.startswith("Save .lake"), (
            "step %r is not followed by a cache save (got %r): a runner loss would cost "
            "the whole stage" % (steps[i][0], name))
        assert "if: always()" in steps[i + 1][1], "the save must run when the stage fails"


def test_save_keys_are_distinct_because_a_cache_entry_is_immutable():
    keys = []
    for n, c in _build_job_steps():
        if n.startswith("Save .lake"):
            m = re.search(r"key:\s*(.+)", c)
            assert m, n
            keys.append(m.group(1).strip())
    assert len(keys) >= 3 and len(keys) == len(set(keys)), keys


def test_each_stage_has_a_time_limit_and_nothing_hands_lake_a_job_flag_it_lacks():
    text = open(CI).read()
    for n, c in _build_job_steps():
        if n.startswith("lake build"):
            assert "timeout-minutes:" in c, n
    assert not re.search(r"lake build[^\n]*\s-j\b", text), "Lake 5.0.0 has no -j"
    assert "xargs -P" not in text


def test_only_the_final_step_runs_the_default_target():
    bare = [n for n, c in _build_job_steps()
            if n.startswith("lake build") and re.search(r"run:\s*lake build\s*$", c, re.M)]
    assert len(bare) == 1 and "default target" in bare[0], bare


def test_the_part_builder_is_strictly_sequential():
    src = open(SCRIPT).read()
    code = [l for l in src.splitlines() if l.strip() and not l.lstrip().startswith("#")]
    assert any("for n in" in l for l in code)
    assert not any(re.search(r"&\s*$", l) or "xargs" in l or "parallel" in l for l in code), (
        "building parts concurrently is what exhausted the runner's memory")
    assert "set -euo pipefail" in src
