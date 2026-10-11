"""The Rust path end to end on the fixture crate (docs/rust.md): rustdoc -> Charon -> Aeneas
-> ledger -> native-vs-Aeneas oracle -> kernel-checked case theorems.

Needs cargo with the pinned nightly, charon and aeneas (AENEAS_HOME), lake, and
AUTOFORM_RUST_LEAN_PROJECT naming a scratch Lake project with the Aeneas library built
(scripts/rust_setup.sh). Without them it SKIPS with the named reason -- unless
AUTOFORM_RUST_REQUIRED=1 (the Rust CI job), where a missing prerequisite is a FAILURE, so
the job cannot go green by skipping. Never touches Autoform's own lakefile or toolchain.

The expected figures are the fixture's, pinned here on purpose: a change in Charon, Aeneas,
the mapping or the encoders that moves any of them must be looked at, not absorbed.
"""
import json
import os
import shutil
import subprocess
import sys

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPT = os.path.join(ROOT, "scripts", "rust_aeneas.py")
CRATE = os.path.join(ROOT, "tests", "fixtures", "rust_proto")
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import rust_aeneas  # noqa: E402

LP = os.environ.get("AUTOFORM_RUST_LEAN_PROJECT")
REQUIRED = os.environ.get("AUTOFORM_RUST_REQUIRED") == "1"
_gone = rust_aeneas.missing()
_reason = None
if _gone:
    _reason = "rust/aeneas prerequisites missing: %s (set AENEAS_HOME; see docs/rust.md)" % ", ".join(_gone)
elif not LP:
    _reason = "AUTOFORM_RUST_LEAN_PROJECT not set (scratch Lake project with Aeneas built; scripts/rust_setup.sh)"
if _reason:
    if REQUIRED:
        raise RuntimeError("AUTOFORM_RUST_REQUIRED=1 but " + _reason)
    pytest.skip(_reason, allow_module_level=True)

EXPECTED_HOLES = {
    "proto::halve": ["aeneas:error:Improperly typed constant value"],
    "proto::read_raw": ["aeneas:error:Aeneas does not yet support dereferencing raw pointers."],
    "proto::first_byte": ["aeneas:external-axiom:core::str::{str}::as_bytes"],
    "proto::count_ones_u32": ["aeneas:external-axiom:core::num::{u32}::count_ones"],
}
EXPECTED_INCONCLUSIVE = {"<proto::Counter>::get", "<proto::Counter>::new", "proto::Shape::double_area",
                         "proto::bump", "proto::larger"}


def run(tmp_path, *extra):
    out = tmp_path / "out"
    p = subprocess.run([sys.executable, SCRIPT, "--crate", CRATE, "--lean-project", LP,
                        "--out", str(out), *extra], capture_output=True, text=True, timeout=5400)
    evidence = os.environ.get("AUTOFORM_RUST_EVIDENCE_DIR")
    if evidence:
        dest = os.path.join(evidence, "proto-" + ("-".join(e.strip("-") for e in extra) or "debug"))
        shutil.rmtree(dest, ignore_errors=True)
        shutil.copytree(out, dest)
    conf = json.load(open(out / "conformance.json")) if (out / "conformance.json").exists() else None
    led = json.load(open(out / "ledger-Proto.json")) if (out / "ledger-Proto.json").exists() else None
    return p, conf, led, out


@pytest.fixture(scope="module")
def debug_run(tmp_path_factory):
    return run(tmp_path_factory.mktemp("debug"))


def test_debug_profile_ledger_names_every_hole(debug_run):
    p, conf, led, _ = debug_run
    assert p.returncode == 0, p.stdout[-2000:] + p.stderr[-2000:]
    assert led["functions"] == 23 and led["holeFree"] == 19
    holes = {d["rust"]: d["holes"] for d in led["functionsDetail"] if d["holes"]}
    assert holes == EXPECTED_HOLES
    assert all(d["status"] in ("translated", "hole") for d in led["functionsDetail"])


def test_debug_profile_oracle_agrees_and_names_what_it_cannot_compare(debug_run):
    p, conf, led, _ = debug_run
    assert conf["divergences"] == 0 and conf["inconclusive"] == 0
    assert conf["functions_covered"] == 14 and conf["total"] > 1000
    assert set(conf["inconclusive_functions"]) == EXPECTED_INCONCLUSIVE
    assert all(conf["inconclusive_functions"].values())
    # every translated function is either compared or inconclusive with a reason
    states = {d["rust"]: d["oracle"]["status"] for d in led["functionsDetail"] if d["status"] == "translated"}
    assert set(states.values()) <= {"compared", "inconclusive"} and len(states) == 19


def test_debug_profile_case_theorems_are_kernel_checked(debug_run):
    p, conf, led, out = debug_run
    kc = conf["kernel_checked"]
    assert kc["emitted"] >= 150 and kc["proved"] >= 140
    # The only accepted failure classes: recursion (partial_fixpoint) and loops beyond --fuel.
    assert set(kc["failure_reasons"]) <= {
        "recursion: Aeneas partial_fixpoint is not evaluated by the kernel",
        "loop did not finish within --fuel iterations (or a std loop inside it)"}, kc["failure_reasons"]
    src = (out / kc["file"]).read_text()
    assert "native_decide" not in src and "sorry" not in src
    by_fn = {d["rust"]: d["theorems"] for d in led["functionsDetail"] if d.get("theorems")}
    assert by_fn["proto::gcd"]["proved"] == by_fn["proto::gcd"]["emitted"] > 0     # a loop, proved
    assert by_fn["proto::sub_sat"]["proved"] == by_fn["proto::sub_sat"]["emitted"]  # saturating std op
    assert by_fn["proto::fact"]["proved"] == 0                                       # recursion


def test_provenance_records_the_exact_tools(debug_run):
    p, conf, led, out = debug_run
    prov = json.load(open(out / "rust-provenance.json"))
    assert prov["matches_pins"]["aeneas"] and prov["matches_pins"]["charon"]
    assert prov["matches_pins"]["rust_toolchain"] and prov["matches_pins"]["lean_toolchain"]
    assert prov["rustc"] and prov["lean"] and prov["crate"]["source_tree_sha256"]
    assert prov["sandbox"]["harness"]["mechanism"]


def test_release_profile_divergences_are_exactly_the_overflowing_functions(tmp_path):
    """The debug-profile assumption is tested: release wraps, Aeneas says fail."""
    p, conf, led, _ = run(tmp_path, "--profile", "release", "--theorems-per-function", "0")
    assert p.returncode == 1, p.stdout[-1500:] + p.stderr[-1500:]
    assert {d["function"] for d in conf["divergence_detail"]} == {"proto::add_checked", "proto::fact"}
    assert all(d["aeneas"] == "fail integerOverflow" and d["rust"].startswith("ok ")
               for d in conf["divergence_detail"])


def test_missing_lean_project_is_a_named_error(tmp_path):
    out = tmp_path / "o"
    p = subprocess.run([sys.executable, SCRIPT, "--crate", CRATE, "--lean-project", str(tmp_path / "nope"),
                        "--out", str(out)], capture_output=True, text=True, timeout=600)
    assert p.returncode == 2
    assert json.load(open(out / "rust-error.json"))["error"] == "lean-project-missing"


GCD = os.environ.get("AUTOFORM_RUST_GCD_CRATE")


def test_real_crate_reproduces_the_tracked_evidence(tmp_path):
    """gcd 2.3.0 from crates.io (digest-verified by the caller), rerun from scratch: every figure
    in the tracked evidence-RustGcd.json -- the ones docs bind -- must come out identical."""
    if not GCD:
        if REQUIRED:
            pytest.fail("AUTOFORM_RUST_REQUIRED=1 but AUTOFORM_RUST_GCD_CRATE (unpacked gcd-2.3.0.crate) is not set")
        pytest.skip("AUTOFORM_RUST_GCD_CRATE not set (unpacked, sha256-verified gcd-2.3.0.crate)")
    tracked = json.load(open(os.path.join(ROOT, "evidence-RustGcd.json")))
    out, ev = tmp_path / "out", tmp_path / "evidence.json"
    p = subprocess.run([sys.executable, SCRIPT, "--crate", GCD, "--module", "RustGcd", "--lean-project", LP,
                        "--out", str(out), "--evidence", str(ev),
                        "--crate-sha256", tracked["crate"]["crate_sha256"]],
                       capture_output=True, text=True, timeout=5400)
    evidence = os.environ.get("AUTOFORM_RUST_EVIDENCE_DIR")
    if evidence and out.exists():
        shutil.rmtree(os.path.join(evidence, "gcd-2.3.0"), ignore_errors=True)
        shutil.copytree(out, os.path.join(evidence, "gcd-2.3.0"))
    assert p.returncode == 0, p.stdout[-2000:] + p.stderr[-2000:]
    fresh = json.load(open(ev))
    for key in ("crate", "pins", "ledger", "oracle", "kernel_checked", "assumptions"):
        assert fresh[key] == tracked[key], key
