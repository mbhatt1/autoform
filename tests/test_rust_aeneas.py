"""Rust via Charon+Aeneas differential prototype (docs/rust.md). EXPERIMENTAL.

Skips with a NAMED reason unless cargo, charon, aeneas and lake are present AND
AUTOFORM_RUST_LEAN_PROJECT names a scratch Lake project in which the Aeneas Lean library
is already built (see docs/rust.md). Never touches Autoform's own lakefile/toolchain.
"""
import json, os, subprocess, sys
import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCRIPT = os.path.join(ROOT, "scripts", "rust_aeneas.py")
CRATE = os.path.join(ROOT, "tests", "fixtures", "rust_proto")
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import rust_aeneas  # noqa: E402

LP = os.environ.get("AUTOFORM_RUST_LEAN_PROJECT")
_gone = rust_aeneas.missing()
if _gone:
    pytest.skip("rust/aeneas prerequisites missing: %s (set AENEAS_HOME)" % ", ".join(_gone),
                allow_module_level=True)
if not LP:
    pytest.skip("AUTOFORM_RUST_LEAN_PROJECT not set (scratch Lake project with Aeneas built)",
                allow_module_level=True)


def run(profile, tmp_path):
    p = subprocess.run([sys.executable, SCRIPT, "--crate", CRATE, "--lean-project", LP,
                        "--out", str(tmp_path), "--profile", profile],
                       capture_output=True, text=True)
    return p, json.load(open(tmp_path / "conformance.json"))


def test_debug_profile_agrees(tmp_path):
    p, c = run("debug", tmp_path)
    assert p.returncode == 0, p.stdout[-1500:]
    assert c["divergences"] == 0 and c["total"] > 100
    assert c["provenance"]["aeneas"] and c["provenance"]["lean_toolchain"]


def test_release_wrap_is_an_expected_divergence(tmp_path):
    """The overflow assumption is tested: release wraps `+`, Aeneas says fail."""
    p, c = run("release", tmp_path)
    assert p.returncode == 1
    assert {d["function"] for d in c["divergence_detail"]} == {"add_checked"}
