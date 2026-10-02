"""A fixture AST must be a function of its source AND of the current exporter.

Each fixture's provenance.json records the sha256 of cartographer/export_ast.sc it was
exported with.  Before this test that field was "informational", and a fixture AST could
silently stop matching its exporter (tests/fixtures/pyscoping did: after the exporter
began wrapping list literals in boxContainer, the committed AST no longer reproduced and
2 of its 28 pins degraded to the hole call:<unpackEx> without any test noticing).

If this fails: re-export the fixture with the current exporter using the recorded command,
compare with the committed AST (byte-identical => just update exporter_sha256 and
ast_sha256 in provenance.json; different => understand the diff, re-render the Generated
program, and re-run the fixture's oracle test), then update provenance.json.
"""
import glob
import hashlib
import json
import os

import pytest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROVS = sorted(glob.glob(os.path.join(ROOT, "tests", "fixtures", "*", "provenance.json"))
               + glob.glob(os.path.join(ROOT, "tests", "boxed_sample", "provenance.json")))


def sha(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def test_fixtures_found():
    assert len(PROVS) >= 10


@pytest.mark.parametrize("prov", PROVS, ids=lambda p: os.path.basename(os.path.dirname(p)))
def test_fixture_exporter_current(prov):
    d = json.load(open(prov))
    assert d["exporter_sha256"] == sha(os.path.join(ROOT, d["exporter"])), (
        f"{prov}: recorded against an older {d['exporter']}; re-export and re-record (see module docstring)")
    folder = os.path.dirname(prov)
    ast = [f for f in ("ast.json", "ast-BoxedSample.json") if os.path.exists(os.path.join(folder, f))][0]
    assert d["ast_sha256"] == sha(os.path.join(folder, ast)), f"{prov}: ast_sha256 does not match {ast}"
