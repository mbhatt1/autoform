"""The Rust path's ledger, hole labelling and value encoding, with NO toolchain.

Every input here is a real tool output recorded from the fixture crate
(`tests/fixtures/rust_proto/recorded/`: rustdoc JSON from `cargo rustdoc --output-format
json`, the Aeneas Lean file and log, and `#print axioms` output from the scratch project),
so the parsers are tested on the formats the pinned tools actually emit. The end-to-end
run is `tests/test_rust_aeneas.py`, gated on the toolchain.
"""
import json
import os
import re
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import rust_aeneas as R  # noqa: E402

REC = ROOT / "tests" / "fixtures" / "rust_proto" / "recorded"


@pytest.fixture(scope="module")
def recorded():
    doc = json.loads((REC / "rustdoc.json").read_text())
    funcs, decls_listing = R.public_functions(doc)
    ns, decls = R.parse_aeneas((REC / "Proto.lean").read_text())
    alog = R.parse_aeneas_log((REC / "aeneas.log").read_text())
    axioms = R.parse_print_axioms((REC / "axioms.txt").read_text())
    mapping = R.map_functions(funcs, decls, doc)
    classes = R.classify(funcs, mapping, decls, ns, axioms, alog, R.parse_charon_log(""), doc)
    return dict(doc=doc, funcs=funcs, decls_listing=decls_listing, ns=ns, decls=decls,
                alog=alog, axioms=axioms, mapping=mapping, classes=classes)


def by_name(rec):
    return {rec["classes"][f["id"]]["rust"]: (f, rec["classes"][f["id"]]) for f in rec["funcs"]}


def test_every_public_function_is_enumerated_from_rustdoc(recorded):
    names = set(by_name(recorded))
    assert len(names) == 23
    assert {"proto::gcd", "proto::fact", "proto::halve", "proto::read_raw", "proto::larger",
            "<proto::Counter>::new", "<proto::Counter>::get", "<u16 as proto::Shape>::area",
            "proto::Shape::double_area"} <= names
    # A required trait method has no body: it is listed as a declaration, not counted.
    assert recorded["decls_listing"] == ["proto::Shape::area"]


def test_every_public_function_maps_to_one_aeneas_definition(recorded):
    unmapped = {recorded["classes"][fid]["rust"]: why for fid, (d, why) in recorded["mapping"].items() if d is None}
    assert unmapped == {}
    lean = {n: c["lean"] for n, (f, c) in by_name(recorded).items()}
    assert lean["<u16 as proto::Shape>::area"] == "proto.U16.Insts.ProtoShape.area"
    assert lean["<proto::Counter>::new"] == "proto.Counter.new"
    assert lean["proto::Shape::double_area"] == "proto.Shape.double_area.default"


def test_holes_are_named_from_the_tools_own_messages(recorded):
    holes = {n: c["holes"] for n, (f, c) in by_name(recorded).items() if c["holes"]}
    assert holes == {
        "proto::halve": ["aeneas:error:Improperly typed constant value"],
        "proto::read_raw": ["aeneas:error:Aeneas does not yet support dereferencing raw pointers."],
        "proto::first_byte": ["aeneas:external-axiom:core::str::{str}::as_bytes"],
        "proto::count_ones_u32": ["aeneas:external-axiom:core::num::{u32}::count_ones"],
    }
    cats = {n: c["category"] for n, (f, c) in by_name(recorded).items() if c["holes"]}
    assert cats == {"proto::halve": "float", "proto::read_raw": "raw-pointer/unsafe",
                    "proto::first_byte": "string", "proto::count_ones_u32": "external-std"}


def test_a_hole_in_a_callee_is_a_hole_in_the_caller():
    text = (REC / "Proto.lean").read_text() + "\n"
    ns, decls = R.parse_aeneas(text)
    # A synthetic caller of `halve` (whose body is `sorry`): `#print axioms` says sorryAx.
    decls.append(dict(path="proto::uses_halve", suffix="", lean="uses_halve", keyword="def", attrs="",
                      body="def uses_halve (x : F64) : Result F64 := do\n  halve x", line=0, end=0,
                      partial_fixpoint=False, sorry=False, reducible=False))
    f = {"id": "x", "name": "uses_halve", "kind": "free", "path": ["proto", "uses_halve"],
         "sig": {"inputs": [], "output": None}, "header": {}}
    classes = R.classify([f], {"x": (decls[-1], None)}, decls, ns,
                         {"proto.uses_halve": ["propext", "sorryAx"]},
                         R.parse_aeneas_log((REC / "aeneas.log").read_text()), R.parse_charon_log(""), {"paths": {}})
    assert classes["x"]["holes"] == ["aeneas:calls-untranslated:proto::halve"]


def test_unreadable_axioms_are_a_hole_not_a_pass(recorded):
    f = next(f for f in recorded["funcs"] if f["name"] == "clamp")
    classes = R.classify([f], recorded["mapping"], recorded["decls"], recorded["ns"], {},
                         recorded["alog"], R.parse_charon_log(""), recorded["doc"])
    assert classes[f["id"]]["holes"] == ["lean:axioms-unreadable"]


def test_global_failures_make_every_function_a_named_hole(recorded):
    classes = R.classify(recorded["funcs"], {}, [], None, {}, R.parse_aeneas_log(""),
                         R.parse_charon_log(""), recorded["doc"], global_failure="aeneas:crash:boom")
    assert all(c["holes"] == ["aeneas:crash:boom"] for c in classes.values())
    assert len(classes) == 23


def test_ledger_has_the_shape_check_docs_and_pr_mode_read(recorded):
    led = R.ledger_json("Proto", recorded["funcs"], recorded["classes"], recorded["decls_listing"], {})
    reference = json.loads((ROOT / "tests/fixtures/ledger-lean/LinuxLcm.json").read_text())["ledger"]
    assert set(reference) <= set(led), set(reference) - set(led)
    assert led["functions"] == 23 and led["holeFree"] == 19 and led["holes"] == 4
    assert led["verifiableCore"] == led["closedByTranslation"] == 19
    assert sum(h["count"] for h in led["holesByLabel"]) == led["holes"]
    assert len(led["functionsDetail"]) == led["functions"]
    assert {d["status"] for d in led["functionsDetail"]} == {"translated", "hole"}


def test_aeneas_log_parsing(recorded):
    be = recorded["alog"]["body_errors"]
    assert be["proto::halve"] == "Improperly typed constant value"
    assert be["proto::read_raw"].startswith("Aeneas does not yet support dereferencing raw pointers")
    assert recorded["alog"]["crash"] is None
    crash = R.parse_aeneas_log("[Error] Internal error, please file an issue\nSource: 'x'\n"
                               "Uncaught exception:\n  \n  Aeneas.Errors.CFailure(_)\n")
    assert "Internal error" in crash["crash"]


def test_charon_log_parsing():
    log = ("error: Floats are not supported\n --> src/lib.rs:3:1\n"
           "error: Item `demo::f` caused errors; ignoring.\n")
    c = R.parse_charon_log(log)
    assert c["items"] == {"demo::f": "Floats are not supported"}


def test_print_axioms_parsing_handles_wrapped_lists():
    text = ("'a.b' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]\n"
            "'a.c' does not depend on any axioms\n")
    assert R.parse_print_axioms(text) == {"a.b": ["propext", "Classical.choice", "Quot.sound"], "a.c": []}


def test_parse_aeneas_structure(recorded):
    d = {x["lean"]: x for x in recorded["decls"]}
    assert recorded["ns"] == "proto"
    assert d["halve"]["sorry"] and d["read_raw"]["sorry"] and not d["clamp"]["sorry"]
    assert d["fact"]["partial_fixpoint"] and not d["gcd"]["partial_fixpoint"]
    assert d["gcd"]["reducible"] and not d["clamp"]["reducible"]
    assert d["gcd_loop"]["suffix"] == "loop 0"
    assert R.header_path("/-- [a::{impl a::T<u8> for [T]}::get]: loop 0:") == ("a::{impl a::T<u8> for [T]}::get", "loop 0")
    assert R.aeneas_key("gcd::{impl gcd::Gcd for core::num::nonzero::NonZero<u8, x::NonZeroU8Inner>}::gcd") == \
        ("timpl", "Gcd", "nonzerou8nonzerou8inner", "gcd")


def test_oracle_signatures_and_reasons(recorded):
    sig = {}
    for n, (f, c) in by_name(recorded).items():
        if c["status"] != "translated":
            continue
        try:
            sig[n] = R.oracle_signature(f)
        except R.Unencodable as exc:
            sig[n] = str(exc)
    assert sig["proto::swap_pair"] == ([("tuple", [("int", "i8"), ("bool",)])], ("tuple", [("bool",), ("int", "i8")]))
    assert sig["proto::sum3"] == ([("array", ("int", "u8"), 3)], ("int", "u16"))
    assert sig["proto::max_ref"] == ([("ref", ("int", "i64")), ("ref", ("int", "i64"))], ("int", "i64"))
    assert sig["<u16 as proto::Shape>::area"] == ([("ref", ("int", "u16"))], ("int", "u32"))
    assert sig["proto::bump"].startswith("mutable reference")
    assert sig["proto::larger"].startswith("generic parameter T")
    assert sig["proto::Shape::double_area"].startswith("provided trait method")
    assert "Counter" in sig["<proto::Counter>::new"]
    f = next(f for f in recorded["funcs"] if f["name"] == "area")
    assert R.rust_callee(f, recorded["doc"]) == "<u16 as proto::Shape>::area"


@pytest.mark.parametrize("ty,value,rust,lean,debug", [
    (("int", "i8"), -128, "-128i8", "((-128)#i8)", "-128"),
    (("int", "u128"), 2 ** 128 - 1, "%du128" % (2 ** 128 - 1), "((%d)#u128)" % (2 ** 128 - 1), str(2 ** 128 - 1)),
    (("bool",), True, "true", "true", "true"),
    (("tuple", [("int", "u8"), ("bool",), ("int", "i16")]), (1, False, -2), "(1u8, false, -2i16)",
     "(((1)#u8), false, ((-2)#i16))", "(1, false, -2)"),
    (("array", ("int", "u8"), 3), (1, 2, 3), "[1u8, 2u8, 3u8]",
     "(Aeneas.Std.Array.make 3#usize [((1)#u8), ((2)#u8), ((3)#u8)])", "[1, 2, 3]"),
    (("ref", ("int", "i64")), -5, "&-5i64", "((-5)#i64)", None),
])
def test_value_encoding(ty, value, rust, lean, debug):
    assert R.rust_lit(ty, value) == rust
    assert R.lean_lit(ty, value) == lean
    if debug is not None:
        assert R.parse_debug(ty, debug) == value


def test_usize_literals_are_bitvectors_because_the_hash_notation_caps_at_u32():
    assert R.lean_lit(("int", "usize"), 2 ** 64 - 1) == "({ bv := BitVec.ofNat _ (%d) } : Std.Usize)" % (2 ** 64 - 1)
    assert R.lean_lit(("int", "isize"), -1) == "({ bv := BitVec.ofInt _ (-1) } : Std.Isize)"


def test_lean_printer_matches_rust_debug_layout():
    ty = ("tuple", [("int", "u8"), ("bool",), ("int", "i16")])
    show = R.lean_show(ty, "v")
    assert "(v.1)" in show and "(v.2.1)" in show and "(v.2.2)" in show
    assert '", "' in show
    arr = R.lean_show(("array", ("int", "u8"), 2), "v")
    assert ".val.map" in arr and '"["' in arr


@pytest.mark.parametrize("t,reason", [
    ({"primitive": "f64"}, "float"),
    ({"primitive": "str"}, "string"),
    ({"borrowed_ref": {"is_mutable": True, "type": {"primitive": "u8"}}}, "mutable reference"),
    ({"generic": "T"}, "generic"),
    ({"resolved_path": {"path": "Vec", "id": 1, "args": None}}, "Vec"),
    ({"array": {"type": {"primitive": "u8"}, "len": "N"}}, "array length"),
    ({"array": {"type": {"primitive": "u8"}, "len": "64"}}, "array length"),
    ({"raw_pointer": {"is_mutable": False, "type": {"primitive": "u8"}}}, "raw pointer"),
    ({"slice": {"primitive": "u8"}}, "slice"),
])
def test_unencodable_types_name_their_reason(t, reason):
    with pytest.raises(R.Unencodable, match=reason):
        R.encode_type(t)


def test_parse_debug_rejects_what_the_type_cannot_hold():
    for ty, s in [(("int", "u8"), "256"), (("int", "u8"), "-1"), (("bool",), "1"),
                  (("tuple", [("int", "u8"), ("bool",)]), "(1)"), (("array", ("int", "u8"), 2), "[1, 2, 3]")]:
        with pytest.raises(ValueError):
            R.parse_debug(ty, s)


def test_compare_maps_panic_to_fail_and_div_to_inconclusive():
    assert R.compare("ok 3", "ok 3") == ("agree", None)
    assert R.compare("ok 3", "ok 4")[0] == "diverge"
    assert R.compare("panic", "fail integerOverflow") == ("agree", None)
    assert R.compare("panic", "ok 0")[0] == "diverge"
    assert R.compare("ok 0", "fail integerOverflow")[0] == "diverge"
    assert R.compare("ok 0", "div")[0] == "inconclusive"
    assert R.compare(None, "ok 0")[0] == "inconclusive"
    assert R.compare("ok 0", None)[0] == "inconclusive"


def test_cases_are_deterministic_and_include_boundaries():
    import random
    a = R.cases_for([("int", "u8"), ("bool",)], random.Random(1), cap=10, nrand=5)
    b = R.cases_for([("int", "u8"), ("bool",)], random.Random(1), cap=10, nrand=5)
    assert a == b and len(a) <= 15
    full = R.cases_for([("int", "i8")], random.Random(1), cap=100, nrand=0)
    assert {-128, 127, 0, -1} <= {c[0] for c in full}


def test_theorem_source_is_rfl_only(recorded):
    src, spans = R.theorem_source("AutoformRust.Proto", ["proto.clamp"], 64,
                                  [("case_0", "proto.clamp ((1)#i32) ((0)#i32) ((3)#i32)",
                                    "(Aeneas.Std.Result.ok ((1)#i32) : Aeneas.Std.Result Std.I32)")],
                                  std_refs=["core.num.I16.saturating_sub"])
    assert "native_decide" not in src and "sorry" not in src and "axiom " not in src.replace("#print axioms", "")
    assert "<;> rfl" in src and "#print axioms case_0" in src and "loop_eq_loopK _ 64" in src
    assert "(try unfold core.num.I16.saturating_sub)" in src
    lo, hi = spans["case_0"]
    assert src.splitlines()[lo - 1].startswith("theorem case_0 ")


def test_case_theorem_rhs_uses_native_value_or_the_agreed_fail_kind():
    assert R.lean_result_lit(("int", "u8"), "ok 7", "ok 7") == \
        "(Aeneas.Std.Result.ok ((7)#u8) : Aeneas.Std.Result Std.U8)"
    assert R.lean_result_lit(("int", "u8"), "panic", "fail divisionByZero") == \
        "(Aeneas.Std.Result.fail .divisionByZero : Aeneas.Std.Result Std.U8)"


def test_eval_helper_is_axiom_free_and_sorry_free():
    src = (ROOT / "scripts" / "rust_eval.lean.tmpl").read_text()
    code = re.sub(r"/-.*?-/", "", src, flags=re.S)
    assert "sorry" not in code and "native_decide" not in code
    assert not re.search(r"^\s*axiom\s", code, re.M)
    assert "theorem loop_eq_loopK" in code and "theorem bind_eq_bindK" in code


def test_pruning_removes_rejected_declarations_and_names_their_dependents():
    text = "\n".join([
        "namespace demo", "",
        "/-- [demo::A]: -/", "structure A where", "  x : Nat", "  x : Nat", "",
        "/-- [demo::f]: -/", "def f (a : A) : Nat := a.x", "",
        "/-- [demo::g]: -/", "def g (n : Nat) : Nat := n", "",
        "end demo", ""])
    def build(t):
        lines = t.splitlines()
        errs = []
        for i, line in enumerate(lines, 1):
            if "structure A" in t and line == "  x : Nat" and lines[i - 2] == "  x : Nat":
                errs.append("error: X.lean:%d:2: Field `x` has already been declared" % i)
            if line.startswith("def f"):
                errs.append("error: X.lean:%d:0: %s" % (i, "elabDoMatch: `sorryAx` is not a matcher"
                                                        if "structure A" in t else "Unknown identifier `A`"))
        return (not errs), "\n".join(errs)
    built, rejected, rounds = R.prune_until_builds(build, text)
    assert "def g" in built and "def f" not in built and "structure A" not in built
    assert rejected["A"][0] == "lean:rejected:demo::A: Field `x` has already been declared"
    assert rejected["f"][0] == "lean:depends-on-rejected:demo::A: Field `x` has already been declared"
    assert "g" not in rejected and rounds == 1


def test_pruning_refuses_errors_outside_declarations():
    with pytest.raises(R.RustPathError) as exc:
        R.prune_until_builds(lambda t: (False, "error: X.lean:1:0: unknown package"), "namespace x\n/-- [x::f]: -/\ndef f := 1\n")
    assert exc.value.name == "lean-build-failed"


def test_lean_error_parsing_accepts_lean_and_lake_formats():
    out = R.parse_lean_errors("f.lean:3:1: error: bad\n  more\nerror: f.lean:7:0: worse\n12 ok 3\n")
    assert out == {3: "bad more", 7: "worse"}


def test_harness_source_shape():
    src = R.harness_source([("proto::gcd", ["1u64", "2u64"]), ("<u16 as proto::Shape>::area", ["&3u16"])])
    assert '0 => run(|| format!("{:?}", proto::gcd(1u64, 2u64))),' in src
    assert '1 => run(|| format!("{:?}", <u16 as proto::Shape>::area(&3u16))),' in src
    assert "catch_unwind" in src and "for i in start..2" in src


def test_failure_classes():
    assert R.failure_class("anything", True).startswith("recursion")
    assert R.failure_class("The left-hand side AutoformRust.loopK (fun x", False).startswith("loop did not finish")
    assert R.failure_class("System.Platform.numBits", False).startswith("usize/isize")


def test_pins_file_and_workflow_agree():
    pins = json.loads((ROOT / "rust-pins.json").read_text())
    wf = (ROOT / ".github" / "workflows" / "rust.yml").read_text()
    asset = "aeneas-linux-x86_64.tar.gz"
    assert pins["assets"][asset] in wf
    assert "AENEAS_RELEASE: %s" % pins["aeneas_release"] in wf and "AENEAS_ASSET: %s" % asset in wf
    assert "releases/download/${AENEAS_RELEASE}" in wf and "sha256sum -c" in wf
    assert pins["rust_toolchain"] in wf
    assert "AUTOFORM_RUST_REQUIRED" in wf
    # every third-party action pinned by full commit SHA
    for use in re.findall(r"uses:\s*(\S+)", wf):
        assert re.fullmatch(r"[\w.-]+/[\w.-]+@[0-9a-f]{40}", use), use


def test_cli_detects_cargo_libraries(tmp_path):
    sys.path.insert(0, str(ROOT / "src"))
    from autoform.cli import is_cargo_library
    assert is_cargo_library(ROOT / "tests" / "fixtures" / "rust_proto")
    (tmp_path / "Cargo.toml").write_text("[workspace]\nmembers = []\n")
    assert not is_cargo_library(tmp_path)
    assert not is_cargo_library(ROOT)
