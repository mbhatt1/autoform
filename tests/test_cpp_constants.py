"""C++ named integer constants, through Joern, against the C++ compiler.

c2cpg gives a translated body no binding for a `static const` data member or a
namespace-scope `const`: `Double::kSignificandSize` was exported as a field read on a
class name (`field:kSignificandSize:non-object` at runtime) and a bare member read as an
unbound name, so every scalar C++ function that named a constant holed when it ran, and
the native oracle never compared it (`double-conversion`'s `EstimatePower` and
`Double::SignificandSizeForOrderOfMagnitude`). `SourceCompiler.cxxConstRead` /
`cxxConstField` now read such a constant as its value. This exports a fixture, checks
the values are inlined only where C++ fixes them, and compares the Lean model with the
natively compiled functions -- including a free function in a namespace and a static
member function, the two shapes the native oracle calls. Needs Joern
(`AUTOFORM_TEST_JOERN=1`), `c++` and `lake`; each missing piece is a named SKIP.
"""
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]

HEADER = r"""
#pragma once
namespace num {
static const int kWidth = 0x10 + 4;            // namespace-scope constant, hex literal
constexpr long long kBig = 1LL << 40;
class Wide {
 public:
  static const int kBias = 1023;
  static const int kPhysical = 52;
  static const int kExponentBias = kBias + kPhysical;
  static const int kDenormal = -kExponentBias + 1;
  static const unsigned kMask = ~0u >> 4;
  static int Size(int order) {
    if (order >= kDenormal + kPhysical) return kPhysical;
    if (order <= kDenormal) return 0;
    return order - kDenormal;
  }
  int Offset(int x) const { return x + base_ + kBias; }
  int base_ = 3;                                 // not static: never inlined
  static int counter;                            // not const: never inlined
};
class Narrow {
 public:
  static const int kBias = 127;                  // same name, other class
  static int Size(int order) { return order + kBias; }
};
}
"""
SOURCE = r"""
#include "wide.h"
namespace num {
static int Estimate(int e) { return e * Wide::kPhysical / 8 + Narrow::kBias - kWidth; }
static long long Scaled(long long x) { return x / kBig + Wide::kMask; }
int Shadow(int kWidth) { return kWidth + 1; }   // a parameter shadows the constant
}
"""
CALLS = [("num.Wide.Size:int(int)", "num::Wide::Size", [-2000, -1074, -1073, -1022, -1021, 0, 7]),
         ("num.Narrow.Size:int(int)", "num::Narrow::Size", [0, -127, 5]),
         ("num.Estimate:int(int)", "num::Estimate", [0, 8, -8, 100]),
         ("num.Scaled:longlong(longlong)", "num::Scaled", [0, 1 << 41, -(1 << 41)]),
         ("num.Shadow:int(int)", "num::Shadow", [0, 41])]


def _joern():
    home = Path(os.environ.get("JOERN_HOME", Path.home() / "joern"))
    return home / "joern-cli" if (home / "joern-cli").is_dir() else home


def _run(args, cwd, timeout=600):
    r = subprocess.run([str(a) for a in args], cwd=str(cwd), capture_output=True, text=True,
                       timeout=timeout)
    assert r.returncode == 0, (r.stdout + r.stderr)[-3000:]
    return r.stdout


@pytest.fixture(scope="module")
def exported(tmp_path_factory):
    if os.environ.get("AUTOFORM_TEST_JOERN") != "1":
        pytest.skip("set AUTOFORM_TEST_JOERN=1 to export C++ through Joern")
    joern = _joern()
    if not (joern / "joern").is_file():
        pytest.skip("Joern not found (JOERN_HOME)")
    tmp = tmp_path_factory.mktemp("cpp-constants")
    src = tmp / "src"
    src.mkdir()
    (src / "wide.h").write_text(HEADER)
    (src / "wide.cc").write_text(SOURCE)
    _run([joern / "joern-parse", src, "--output", tmp / "cpg.bin"], tmp)
    _run([joern / "joern", "--script", ROOT / "cartographer/export_ast.sc",
          "--param", "cpgPath=%s" % (tmp / "cpg.bin"), "--param", "out=%s" % (tmp / "ast.json"),
          "--param", "dataModel=lp64"], tmp)
    return tmp, {f["name"]: f for f in json.loads((tmp / "ast.json").read_text())}


def test_constants_are_read_as_their_values_only_where_cpp_fixes_them(exported):
    _, by_name = exported
    for name, _, _ in CALLS:
        body = json.dumps(by_name[name]["body"])
        assert '"hole' not in body, (name, body[:600])
    size = json.dumps(by_name["num.Wide.Size:int(int)"]["body"])
    assert '"kDenormal"' not in size and '"kPhysical"' not in size and "-1074" in size
    estimate = json.dumps(by_name["num.Estimate:int(int)"]["body"])
    assert "non-object" not in estimate and '"kBias"' not in estimate
    # A parameter named like a constant is the parameter; a non-static member is a field.
    assert '"kWidth"' in json.dumps(by_name["num.Shadow:int(int)"]["body"])
    assert '"base_"' in json.dumps(by_name["num.Wide.Offset:int(int)<const>"]["body"])


def test_model_agrees_with_cxx(exported):
    tmp, _ = exported
    cxx = shutil.which("c++")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    if cxx is None:
        pytest.skip("no C++ compiler (c++) on PATH")
    if not Path(lake).exists():
        pytest.skip("lake not found")
    main = '#include "src/wide.cc"\n#include <cstdio>\nint main() {\n'
    for _, call, inputs in CALLS:
        for n in inputs:
            main += '  std::printf("%%lld\\n", (long long)%s(%dLL));\n' % (call, n)
    main += "  return 0;\n}\n"
    (tmp / "native.cc").write_text(main)
    _run([cxx, "-O0", "-o", tmp / "native", tmp / "native.cc"], tmp)
    native = _run([tmp / "native"], tmp).split()
    model = tmp / "CppConstants.lean"
    _run([sys.executable, ROOT / "cartographer/render_lean.py", tmp / "ast.json", model, "CppConstants"], ROOT)
    driver = model.read_text() + "\nopen Autoform.Core Autoform.Generated.CppConstants\n"
    for name, _, inputs in CALLS:
        for n in inputs:
            driver += ('#eval IO.println (match runFunc program 4000 "%s" [.int (%d)] with '
                       '| .val (.int v) => toString v | r => "unexpected " ++ reprStr r)\n' % (name, n))
    (tmp / "Drive.lean").write_text(driver)
    lean = _run([lake, "env", "lean", tmp / "Drive.lean"], ROOT, timeout=1200).split("\n")
    lean = [l for l in lean if l.strip()]
    cases = [(name, n) for name, _, inputs in CALLS for n in inputs]
    assert len(lean) == len(native) == len(cases), (len(lean), len(native), lean[-5:])
    bad = [(c, w, g) for c, w, g in zip(cases, native, lean) if w != g]
    assert bad == [], bad
