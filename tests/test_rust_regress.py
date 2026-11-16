"""The Rust regression leg (scripts/rust_regress.py, `autoform regress` on a Cargo library).

The first group needs NO toolchain: the case classifier, the signature table on the recorded
rustdoc JSON of the fixture crate, base-tree detection for `regress --lang auto`, and that a
rustc/cargo which ignores `+toolchain` is not taken for the pinned one.

The last test runs the leg end to end on the fixture crate and a seeded head (a regression in
a translated function, a change in a hole function, a refactor, a changed signature, a removed
and an added function). It is gated exactly like tests/test_rust_aeneas.py: it SKIPS without
the pinned toolchain, Aeneas and the scratch Lake project, unless AUTOFORM_RUST_REQUIRED=1.
"""
import json
import os
import shutil
import stat
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import rust_aeneas as R  # noqa: E402
import rust_regress as G  # noqa: E402

CRATE = ROOT / "tests" / "fixtures" / "rust_proto"
REC = CRATE / "recorded"


def case(evidence="model", aeneas="ok 6"):
    return {"evidence": evidence, "aeneas": aeneas}


def test_classifier_judges_head_against_the_base_model_where_base_agreed():
    assert G.classify(case(), "ok 6", "ok 6") == ("unchanged", None)
    assert G.classify(case(), "ok 6", "ok 7") == ("regression", None)
    assert G.classify(case(), "ok 6", "panic") == ("regression", None)
    # a native panic agrees with any Aeneas fail, at base and at head
    assert G.classify(case(aeneas="fail integerOverflow"), "panic", "panic") == ("unchanged", None)
    assert G.classify(case(aeneas="fail integerOverflow"), "panic", "ok 0") == ("regression", None)


def test_classifier_never_calls_a_change_without_a_model_verdict_a_regression():
    # native-only (a hole at base): a change, not a regression
    assert G.classify(case("native-only", None), "ok 1", "ok 2") == ("behaviour-change", None)
    assert G.classify(case("native-only", None), "ok 1", "ok 1") == ("unchanged", None)
    # base already diverged from its model: no model verdict either way
    assert G.classify(case(aeneas="ok 5"), "ok 6", "ok 5") == ("behaviour-change", None)
    assert G.classify(case(aeneas="ok 5"), "ok 6", "ok 6") == ("unchanged", None)
    # Aeneas `div` is never a verdict
    assert G.classify(case(aeneas="div"), "ok 6", "ok 7") == ("behaviour-change", None)
    # a missing native result is inconclusive, never agreement
    assert G.classify(case(), "ok 6", None)[0] == "inconclusive"
    assert G.classify(case(), None, "ok 6")[0] == "inconclusive"


def test_signatures_table_matches_the_oracle_encodings():
    doc = json.loads((REC / "rustdoc.json").read_text())
    sigs = G.signatures(doc)
    assert sigs["proto::gcd"][0] == [[["int", "u64"], ["int", "u64"]], ["int", "u64"]]
    assert sigs["proto::max_ref"][0][0] == [["ref", ["int", "i64"]], ["ref", ["int", "i64"]]]
    assert sigs["<u16 as proto::Shape>::area"][0] == [[["ref", ["int", "u16"]]], ["int", "u32"]]
    # unencodable functions are listed with the oracle's reason, never compared
    assert sigs["proto::halve"][0] is None and "float" in sigs["proto::halve"][1]
    assert sigs["proto::bump"][0] is None and "&mut" in sigs["proto::bump"][1]
    assert sigs["proto::read_raw"][0] is None and "unsafe" in sigs["proto::read_raw"][1]
    assert set(n for _, _, n in sigs.values()) >= {"proto::count_ones_u32", "proto::fact"}


def _git(repo, *args):
    subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                   env=dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@example.invalid",
                            GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@example.invalid"))


def test_regress_auto_detects_a_cargo_library_at_the_base_commit(tmp_path):
    sys.path.insert(0, str(ROOT / "src"))
    from autoform.cli import _cargo_library_at
    repo = tmp_path / "repo"
    repo.mkdir()
    _git(repo, "init", "-q")
    (repo / "README").write_text("x\n")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "no crate")
    shutil.copytree(CRATE / "src", repo / "sub" / "src")
    shutil.copy(CRATE / "Cargo.toml", repo / "sub" / "Cargo.toml")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "crate")
    assert _cargo_library_at(repo, "HEAD", "sub")
    assert not _cargo_library_at(repo, "HEAD")            # the root is not a package
    assert not _cargo_library_at(repo, "HEAD~1", "sub")   # judged at the base commit, not the tree


def test_regress_on_a_crate_takes_the_rust_leg_with_both_checkouts(tmp_path, monkeypatch):
    """`autoform regress` on a local Cargo library: both commits are checked out and handed to
    the bundled scripts/rust_regress.py (stubbed at `_run_command`), and nothing is left behind."""
    monkeypatch.syspath_prepend(str(ROOT / "src"))
    import autoform.cli as cli
    repo = tmp_path / "repo"
    shutil.copytree(CRATE, repo, ignore=shutil.ignore_patterns("recorded", "target"))
    _git(repo, "init", "-q")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    _git(repo, "tag", "base")
    (repo / "src" / "lib.rs").write_text((repo / "src" / "lib.rs").read_text() + "\npub fn one() -> u8 { 1 }\n")
    _git(repo, "commit", "-qam", "head")
    seen = {}

    def fake(command, *, env, timeout=None, **_):
        seen["command"] = command
        args = dict(zip(command[2::2], command[3::2]))
        seen["trees"] = {k: (Path(args[k]) / "src" / "lib.rs").read_text() for k in ("--base", "--head")}
        return 1
    monkeypatch.setattr(cli, "_run_command", fake)
    ws = tmp_path / "ws"
    code = cli.main(["--workspace", str(ws), "regress", str(repo), "Proto", "--base", "base",
                     "--rust-lean-project", str(tmp_path / "lp")])
    assert code == 1
    cmd = seen["command"]
    assert cmd[1] == str(ws.resolve() / "scripts" / "rust_regress.py")
    assert "pub fn one" not in seen["trees"]["--base"] and "pub fn one" in seen["trees"]["--head"]
    assert cmd[cmd.index("--lean-project") + 1] == str((tmp_path / "lp").resolve())
    assert cmd[cmd.index("--module") + 1] == "Proto"
    runs = json.loads((ws / "artifacts/regression/Proto/runs.json").read_text())
    assert runs["base"]["commit"] and runs["head"]["commit"] != runs["base"]["commit"]
    sources = ws / "sources"
    assert not sources.exists() or not any(sources.iterdir())
    # --lang joern keeps the source pipeline (autoform.sh) even on a crate
    seen.clear()
    monkeypatch.setattr(cli, "_run_command", lambda command, **_: seen.setdefault("command", command) and 2)
    cli.main(["--workspace", str(ws), "regress", str(repo), "Proto", "--base", "base", "--lang", "joern"])
    assert seen["command"][1].endswith("autoform.sh")


def test_a_rustc_that_ignores_plus_toolchain_is_not_the_pin(tmp_path):
    """Homebrew's rustc prints its own version for `rustc +nightly-... -V`, and its cargo
    rejects `+toolchain`: neither the Rust path nor doctor may take that for the pin."""
    bin_ = tmp_path / "bin"
    bin_.mkdir()
    for name, body in (("rustc", 'echo "rustc 1.97.1 (8bab26f4f 2026-07-14) (Homebrew)"'),
                       ("cargo", 'case "$1" in +*) echo "error: no such command: \\`$1\\`" >&2; exit 101;; esac\n'
                                 'echo "cargo 1.97.1 (Homebrew)"')):
        p = bin_ / name
        p.write_text("#!/bin/sh\n" + body + "\n")
        p.chmod(p.stat().st_mode | stat.S_IXUSR)
    env = dict(os.environ, PATH=str(bin_) + os.pathsep + "/usr/bin:/bin")
    pin = json.loads((ROOT / "rust-pins.json").read_text())["rust_toolchain"]
    assert not R.toolchain_present(pin, env)
    (bin_ / "home").mkdir()
    r = subprocess.run([sys.executable, "-m", "autoform", "doctor", "--json"], cwd=ROOT,
                       env=dict(env, HOME=str(bin_ / "home"), PYTHONPATH=str(ROOT / "src"),
                                JOERN_HOME=str(tmp_path / "nojoern")),
                       capture_output=True, text=True, timeout=180)
    assert json.loads(r.stdout)["tools"]["rust-toolchain"]["status"] == "missing"


# --------------------------------------------------------------------------- end to end

LP = os.environ.get("AUTOFORM_RUST_LEAN_PROJECT")
REQUIRED = os.environ.get("AUTOFORM_RUST_REQUIRED") == "1"


def _skip_reason():
    gone = R.missing()
    if gone:
        return "rust/aeneas prerequisites missing: %s (set AENEAS_HOME; see docs/rust.md)" % ", ".join(gone)
    if not LP:
        return "AUTOFORM_RUST_LEAN_PROJECT not set (scratch Lake project with Aeneas built)"
    return None


def _seed_head(base, head):
    shutil.copytree(base, head)
    src = head / "src" / "lib.rs"
    text = src.read_text()
    edits = [
        # regression in a translated function: clamp no longer clamps from above
        ("    } else if x > hi {\n        hi\n", "    } else if x > hi {\n        x\n"),
        # refactor of a translated function: same behaviour
        ("    while b != 0 {\n        let t = a % b;\n        a = b;\n        b = t;\n    }\n    a\n",
         "    while b != 0 {\n        (a, b) = (b, a % b);\n    }\n    a\n"),
        # change in a hole function (external axiom at base): native-only evidence
        ("    x.count_ones()\n", "    x.count_ones() + (x == 7) as u32\n"),
        # signature change: not comparable
        ("pub fn add_wrapping(a: u32, b: u32) -> u32 {", "pub fn add_wrapping(a: u64, b: u64) -> u64 {"),
        # removal, and an addition
        ("pub fn is_even(x: u32) -> bool {\n    x % 2 == 0\n}\n", "pub fn is_odd(x: u32) -> bool {\n    x % 2 == 1\n}\n"),
    ]
    for old, new in edits:
        assert old in text, old
        text = text.replace(old, new)
    src.write_text(text)


def test_rust_regress_end_to_end_on_the_fixture(tmp_path):
    reason = _skip_reason()
    if reason:
        if REQUIRED:
            pytest.fail("AUTOFORM_RUST_REQUIRED=1 but " + reason)
        pytest.skip(reason)
    base, head, out = tmp_path / "base", tmp_path / "head", tmp_path / "out"
    shutil.copytree(CRATE, base, ignore=shutil.ignore_patterns("recorded", "target"))
    _seed_head(base, head)
    p = subprocess.run([sys.executable, str(ROOT / "scripts" / "rust_regress.py"), "--base", str(base),
                        "--head", str(head), "--out", str(out), "--lean-project", LP, "--module", "Proto"],
                       capture_output=True, text=True, timeout=5400)
    assert p.returncode == 1, p.stdout[-3000:] + p.stderr[-3000:]
    rep = json.loads((out / "rust-regression.json").read_text())
    status = {f["callee"]: f["status"] for f in rep["functions"]}
    assert rep["control"]["flagged"] == 0
    assert rep["control"]["reproduced_base_model_run"] == rep["base_model"]["conformance"]["total"]
    assert rep["cases"]["unstable"] == 0
    assert [f["callee"] for f in rep["regressions"]] == ["proto::clamp"]
    assert [f["callee"] for f in rep["behaviour_changes"]] == ["proto::count_ones_u32"]
    assert status["proto::gcd"] == "unchanged"
    assert status["proto::add_wrapping"] == "not-comparable"
    assert "signature changed" in rep["not_comparable"]["proto::add_wrapping"]
    assert "removed at head" in rep["not_comparable"]["proto::is_even"]
    assert rep["functions_added_at_head"] == ["proto::is_odd"]
    assert "proto::count_ones_u32" in rep["functions_native_only"]
    # every other compared function is unchanged; nothing else is flagged
    flagged = {c for c, s in status.items() if s in ("regression", "behaviour-change")}
    assert flagged == {"proto::clamp", "proto::count_ones_u32"}
    ex = rep["regressions"][0]["examples"][0]
    assert ex["base_native"] == ex["base_model"] != ex["head_native"]


def test_pr_mode_takes_the_rust_leg_on_the_fixture_history(tmp_path):
    """`autoform pr` on the crate's two-commit history: the same seeded head as the leg
    above, pruned to the changed public functions and mapped into the pr report. The
    exporter is not run (no Rust frontend), the leg is the whole comparison, and the
    change fails `--fail-on behaviour-changed`. Gated exactly like the test above."""
    reason = _skip_reason()
    if reason:
        if REQUIRED:
            pytest.fail("AUTOFORM_RUST_REQUIRED=1 but " + reason)
        pytest.skip(reason)
    repo = tmp_path / "repo"
    shutil.copytree(CRATE, repo, ignore=shutil.ignore_patterns("recorded", "target"))
    _git(repo, "init", "-q")
    _git(repo, "add", ".")
    _git(repo, "commit", "-qm", "base")
    _git(repo, "tag", "base")
    seeded = tmp_path / "seeded"
    _seed_head(repo, seeded)
    shutil.copy(seeded / "src" / "lib.rs", repo / "src" / "lib.rs")
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "head")
    _git(repo, "tag", "head")
    out = tmp_path / "out"
    p = subprocess.run([sys.executable, str(ROOT / "scripts" / "pr_mode.py"), str(repo),
                        "--base", "base", "--head", "head", "--module", "PullRequestRustE2E",
                        "--out", str(out), "--sarif", str(out / "pr.sarif"),
                        "--markdown", str(out / "pr.md"), "--fail-on", "behaviour-changed"],
                       env=dict(os.environ, AUTOFORM_RUST_LEAN_PROJECT=LP),
                       capture_output=True, text=True, timeout=5400)
    assert p.returncode == 1, p.stdout[-3000:] + p.stderr[-3000:]
    report = json.loads((out / "pr.json").read_text())
    by_name = {f["name"]: f for f in report["functions"]}
    # the crate's untouched public functions are pruned: the seeded ones are reported, the
    # removed one under `removed`
    assert set(by_name) == {"proto::clamp", "proto::gcd", "proto::count_ones_u32",
                            "proto::add_wrapping", "proto::is_odd"}, sorted(by_name)
    assert [f["name"] for f in report["removed"]] == ["proto::is_even"]
    assert "removed at head" in report["removed"][0]["reason"]
    assert all(f["level"] == "none" and f["language"] == "rust" and f["detection"] == "rustdoc"
               and f["file"] == "src/lib.rs" and "change_detail" not in f
               for f in report["functions"])
    status = {n: f["behaviour"]["status"] for n, f in by_name.items()}
    assert status == {"proto::clamp": "changed", "proto::count_ones_u32": "changed",
                      "proto::gcd": "unchanged-on-inputs", "proto::add_wrapping": "not-compared",
                      "proto::is_odd": "not-compared"}
    clamp = by_name["proto::clamp"]["behaviour"]["counter_inputs"][0]
    assert clamp["call"].startswith("proto::clamp(") and clamp["origin"] == "model"
    assert clamp["base_model"] == clamp["base_runtime"] != clamp["head_runtime"]
    ones = by_name["proto::count_ones_u32"]["behaviour"]["counter_inputs"][0]
    assert ones["origin"] == "native-only" and ones["base_runtime"] != ones["head_runtime"]
    assert "signature changed" in by_name["proto::add_wrapping"]["behaviour"]["reason"]
    assert by_name["proto::is_odd"]["change"] == "added"
    assert by_name["proto::is_odd"]["behaviour"]["reason"] == \
        "added at head: it has no base model to compare"
    # a Rust-only change: the exporter never ran, and the leg is the whole analysis
    assert report["exporter"]["status"] == "not-run"
    assert "no Rust frontend" in report["exporter"]["reason"]
    assert report["behaviour"]["languages"] == ["rust"]
    assert report["behaviour"]["stages"]["rust"]["status"] == "passed"
    assert report["behaviour"]["summary"] == {"changed": 2, "unchanged-on-inputs": 1,
                                              "not-compared": 2}
    assert report["gate"]["status"] == "evidence" and report["gate"]["exit_code"] == 1
    leg = json.loads((out / "rust" / "rust-regression.json").read_text())
    assert leg["function_spans"]["head"]["proto::clamp"]["file"] == "src/lib.rs"
    assert "Languages compared: rust" in (out / "pr.md").read_text()
