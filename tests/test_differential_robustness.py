"""Robustness and accounting fixes to the differential oracle, kept apart from the
end-to-end backend tests because none of these needs a toolchain.

Each test names a way the oracle used to fail *silently or loudly for the wrong reason*:
`AUTOFORM_CASE_CAP=""` raised at import and took synth_specs.py down with it; `0` dropped
every case and said nothing; a lone surrogate in a mined string literal killed the JVM
planner at `str.encode()`; the C backend's `plan[:cap]` cut left `dropped: 0` in
conformance.json. None of these tests changes which inputs a backend draws: the recorded
`measurement_basis` strings pin that, and the surrogate test checks the pin holds.
"""
import os

import pytest

from conftest import SCRIPTS, load


@pytest.fixture(scope="module")
def backends():
    return load(os.path.join(SCRIPTS, "runtime_backends.py"), "af_runtime_backends_robustness")


# ------------------------------------------------------------------ case cap parsing

def test_case_cap_helper_blank_means_default(differential):
    """Unset or blank is the default, never `int("")`."""
    assert differential.positive_int_from_env("AUTOFORM_CASE_CAP", None, 600) == 600
    assert differential.positive_int_from_env("AUTOFORM_CASE_CAP", "", 600) == 600
    assert differential.positive_int_from_env("AUTOFORM_CASE_CAP", "   ", 600) == 600


def test_case_cap_helper_parses_a_positive_integer(differential):
    assert differential.positive_int_from_env("AUTOFORM_CASE_CAP", "12", 600) == 12
    assert differential.positive_int_from_env("AUTOFORM_CASE_CAP", " 2405 ", 600) == 2405


@pytest.mark.parametrize("raw", ["abc", "0", "-5", "1.5", "0x10"])
def test_case_cap_helper_refuses_anything_else(differential, raw):
    """`0` silently dropped every case and a negative value trimmed the tail of the list;
    a non-integer raised a bare ValueError. All are refused with the variable named."""
    with pytest.raises(SystemExit) as e:
        differential.positive_int_from_env("AUTOFORM_CASE_CAP", raw, 600)
    assert "AUTOFORM_CASE_CAP" in str(e.value)
    assert repr(raw) in str(e.value)


def test_blank_case_cap_cannot_break_import(monkeypatch):
    """`AUTOFORM_CASE_CAP=""` (an `export` without a value, a CI matrix cell left empty)
    used to raise at import time -- in differential.py, synth_specs.py and every test
    that imports either. It is now the default, and the raw setting is kept for the
    `case_cap` record."""
    monkeypatch.setenv("AUTOFORM_NO_REEXEC", "1")
    monkeypatch.setenv("AUTOFORM_CASE_CAP", "")
    mod = load(os.path.join(SCRIPTS, "differential.py"), "af_differential_blank_cap")
    assert mod.MAX_TOTAL_CASES == 600
    assert mod.CASE_CAP_SETTING == ""


def test_explicit_case_cap_is_recorded_raw(monkeypatch):
    monkeypatch.setenv("AUTOFORM_NO_REEXEC", "1")
    monkeypatch.setenv("AUTOFORM_CASE_CAP", "12")
    mod = load(os.path.join(SCRIPTS, "differential.py"), "af_differential_cap_12")
    assert mod.MAX_TOTAL_CASES == 12
    assert mod.CASE_CAP_SETTING == "12"


@pytest.mark.parametrize("raw", ["abc", "0"])
def test_invalid_case_cap_refuses_at_import_with_a_message(monkeypatch, raw):
    monkeypatch.setenv("AUTOFORM_NO_REEXEC", "1")
    monkeypatch.setenv("AUTOFORM_CASE_CAP", raw)
    with pytest.raises(SystemExit) as e:
        load(os.path.join(SCRIPTS, "differential.py"), "af_differential_bad_cap_" + raw)
    assert "AUTOFORM_CASE_CAP" in str(e.value)


def test_lean_chunk_timeout_is_read_the_same_way(monkeypatch):
    monkeypatch.setenv("AUTOFORM_NO_REEXEC", "1")
    monkeypatch.delenv("AUTOFORM_LEAN_CHUNK_TIMEOUT", raising=False)
    mod = load(os.path.join(SCRIPTS, "differential.py"), "af_differential_default_chunk_timeout")
    assert mod.LEAN_CHUNK_TIMEOUT == 1800
    monkeypatch.setenv("AUTOFORM_LEAN_CHUNK_TIMEOUT", "90")
    mod = load(os.path.join(SCRIPTS, "differential.py"), "af_differential_chunk_timeout_90")
    assert mod.LEAN_CHUNK_TIMEOUT == 90


# ------------------------------------------------------------ surrogate literals

def _fn(name, strings, file="a.java"):
    body = {"k": "block", "ss": [{"k": "exprS", "e": {"k": "call", "a": [{"k": "str", "v": s}]}}
                                 for s in strings]}
    return {"name": name, "file": file, "params": [], "body": body}


def test_mined_literals_drops_lone_surrogates_and_counts_them(backends):
    """The JVM planner base64-encodes each drawn string with `str.encode()`, which raises
    UnicodeEncodeError on a lone surrogate; the whole run died. Such a literal is now
    dropped and counted, and the rest of the set is untouched."""
    f = _fn("f", ["hub", "\ud83d", ":", "lo\udc00ne"])
    stats = {}
    strings, ints = backends.mined_literals(f, stats=stats)
    assert strings == ["hub", ":"]
    assert stats == {"literals_unencodable": 2}
    for s in strings:
        s.encode("utf-8")                       # what the planner does; must not raise
    # The count accumulates across functions when one dict is threaded through.
    backends.mined_literals(_fn("g", ["\ud800"]), stats=stats)
    assert stats["literals_unencodable"] == 3


def test_mined_literals_without_surrogates_is_unchanged(backends):
    """The filter must not move the pin: for a literal set without surrogates the result
    is byte-identical to the unfiltered computation (dedup, 64-char bound, cap) and the
    count is zero. CommonsLang3's literal set is such a set."""
    lits = ["a", "b", "a", "x" * 65, "ü", "日本", ""] + ["l%d" % i for i in range(20)]
    f = _fn("f", lits)
    g = _fn("g", ["from-g", "a"])
    stats = {}
    strings, ints = backends.mined_literals(f, [f, g], extra=["head-only"], stats=stats)
    expected = [s for s in dict.fromkeys(lits + ["head-only", "from-g", "a"]) if len(s) <= 64]
    assert strings == expected[:backends.MAX_MINED_LITERALS]
    assert stats == {"literals_unencodable": 0}
    assert backends.mined_literals(f, [f, g], extra=["head-only"]) == (strings, ints)


def test_utf8_encodable(backends):
    assert backends.utf8_encodable("plain") and backends.utf8_encodable("ü日本")
    assert not backends.utf8_encodable("\ud800")
    assert not backends.utf8_encodable("ok\udfffok")


# ------------------------------------------------------------ C plan cap accounting

def _plan(*names):
    return [({"name": n}, ()) for n in names]


def test_c_plan_cap_record_counts_the_tail_and_names_its_functions(differential):
    """`plan[:cap]` kept the head and said nothing about the rest. The record counts the
    dropped calls, names every function that lost a call, and separately those that lost
    every call -- computed before the cut and changing nothing about it."""
    plan = _plan("a", "a", "b", "c", "c", "d")
    rec = differential.c_plan_cap_record(plan, 4)
    assert rec == {"dropped_c_plan": 2,
                   "functions_affected_c_plan": ["c", "d"],   # c keeps one call, d none
                   "functions_dropped_c_plan": ["d"]}
    assert plan[:4] == _plan("a", "a", "b", "c")   # the cut itself is the plain head
    assert differential.c_plan_cap_record(plan, 2)["functions_dropped_c_plan"] == ["b", "c", "d"]


def test_c_plan_cap_record_is_empty_when_the_plan_fits(differential):
    assert differential.c_plan_cap_record(_plan("a", "b"), 2) == {
        "dropped_c_plan": 0, "functions_affected_c_plan": [], "functions_dropped_c_plan": []}
    assert differential.c_plan_cap_record([], 600)["dropped_c_plan"] == 0


# ------------------------------------------------------------------- output tails

def test_output_tail_accepts_what_timeouts_carry(backends):
    """`TimeoutExpired.stderr` is None or bytes (a killed process's partial output stays
    bytes even under text=True); `CompletedProcess.stderr` is str."""
    assert backends.output_tail(None) == ""
    assert backends.output_tail(b"abc\xff") == "abc\ufffd"
    assert backends.output_tail("x" * 3000, 2000) == "x" * 2000
    assert backends.output_tail("short") == "short"
