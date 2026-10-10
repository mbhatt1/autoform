"""Exercise the public source CLI through native observations and kernel proofs."""
import json
import os
from pathlib import Path
import subprocess

import pytest

ROOT = Path(__file__).resolve().parents[1]
LANGUAGES = {"python": "Python", "c": "C", "cpp": "CPP", "java": "Java",
             "go": "Go", "js": "JS", "ts": "TS", "kotlin": "Kotlin"}


@pytest.mark.skipif(os.environ.get("AUTOFORM_TEST_JOERN") != "1", reason="set AUTOFORM_TEST_JOERN=1 for the full CLI pipeline")
@pytest.mark.parametrize("language", LANGUAGES)
def test_source_to_native_conformance_proofs(language):
    module = "Pipeline" + LANGUAGES[language]
    result = subprocess.run(["bash", str(ROOT / "autoform.sh"),
                             str(ROOT / "examples/source" / language), module],
                            cwd=ROOT, text=True, capture_output=True, timeout=900)
    assert result.returncode == 0, result.stdout + result.stderr
    evidence = ROOT / "artifacts/pipeline" / module
    status = json.loads((evidence / "pipeline.json").read_text())
    observations = json.loads((evidence / "conformance.json").read_text())
    proofs = json.loads((evidence / "specs.json").read_text())
    assert status["status"] == "passed" and status["stage"] == "complete"
    assert observations["agree"] == observations["total"] > 0
    assert observations["divergences"] == 0
    assert proofs["build_clean"] and proofs["proved"] > 0
    assert proofs["open_obligations"] == 0
    assert proofs["cross_runtime_evidence"]
