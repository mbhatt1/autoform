"""The native oracle calls C++ entry points by their qualified identity, and refuses the
ones it cannot call with a reason instead of failing their whole translation unit.

Before: every C++ thunk named its callee by the bare source name at global scope, so a
function in a namespace did not compile (`use of undeclared identifier`), an instance
method failed its file's unit and took every other entry point in it along, and a
function defined in a header was never a translation unit at all. On a real C++ library
no translation unit executed and no changed C++ function was compared across revisions.
"""
import shutil
from pathlib import Path

import pytest

from conftest import SCRIPTS, load


@pytest.fixture
def native(differential):
    if not shutil.which('c++'):
        pytest.skip('C++ compiler unavailable')
    import native_c
    return native_c


def function(name, file, params=(), ret='int', tags=None, rtag='i32', source=None):
    tags = ['i32'] * len(params) if tags is None else tags
    return dict(name=name, file=file, sourceName=source or name.split(':')[0].split('.')[-1],
                params=['a%d' % i for i in range(len(params))], paramTypes=list(params),
                paramIntegerTypes=tags, returnType=ret, returnIntegerType=rtag)


def corpus(tmp_path, files):
    source = tmp_path / 'source'
    source.mkdir()
    for name, text in files.items():
        (source / name).write_text(text)
    return source


LIBRARY = {
    'bits.h': '''
#pragma once
namespace num {
class Bits {
 public:
  static int Width(int order) { return order >= 0 ? 32 : 0; }
  int Offset(int x) const { return x + base_; }
  static int Twice(int x) { return x * 2; }
  static int Twice(long long x) { return 7; }
 private:
  static int Hidden(int x) { return x; }
  int base_ = 3;
};
typedef unsigned short code;
inline int Code(code c) { return c + 1; }
inline int Code(char c) { return 9; }
}
''',
    'bits.cc': '''
#include "bits.h"
namespace num {
static int Clamp(int e) { return e > 100 ? 100 : (e < -100 ? -100 : e); }
int Add(int a, int b) { return a + b; }
namespace {
int Hidden(int x) { return x - 1; }
}
struct Box { int Get(int x) { return x; } };
}
int Global(int x) { return -x; }
''',
}


def test_cpp_entry_points_are_called_by_qualified_identity(tmp_path, native):
    source = corpus(tmp_path, LIBRARY)
    fs = [function('num.Clamp:int(int)', 'bits.cc', ['int']),
          function('num.Add:int(int,int)', 'bits.cc', ['int', 'int']),
          function('num.Hidden:int(int)', 'bits.cc', ['int']),          # anonymous namespace
          function('Global:int(int)', 'bits.cc', ['int']),
          function('num.Bits.Width:int(int)', 'bits.h', ['int']),       # static member, header
          function('num.Bits.Twice:int(int)', 'bits.h', ['int']),      # one of two overloads
          function('num.Bits.Twice:int(long long)', 'bits.h', ['long long'], tags=['i64'])]
    library = native.compile_sources(source, fs, tmp_path / 'work')
    assert library.skipped == {}, library.skipped
    assert library(fs[0])(500) == 100 and library(fs[0])(-7) == -7
    assert library(fs[1])(2, 3) == 5
    assert library(fs[2])(5) == 4
    assert library(fs[3])(4) == -4
    assert library(fs[4])(1) == 32 and library(fs[4])(-1) == 0
    # The exact-type cast selects each overload, not whichever the call resolves to.
    assert library(fs[5])(21) == 42 and library(fs[6])(21) == 7


def test_uncallable_cpp_entry_points_are_refused_with_reasons_and_spare_their_unit(tmp_path, native):
    source = corpus(tmp_path, LIBRARY)
    fs = [function('num.Bits.Offset:int(int)<const>', 'bits.h', ['int']),
          function('num.Box.Get:int(int)', 'bits.cc', ['int']),
          function('num.Bits.Hidden:int(int)', 'bits.h', ['int']),
          # A typedef'd parameter has no global spelling, so it is called by name, and
          # the name has two overloads in the export: refused, never resolved by luck.
          function('num.Code:int(code)', 'bits.h', ['code'], tags=['u16']),
          function('num.Code:int(char)', 'bits.h', ['char'], tags=['']),
          function('num.Twin<duplicate>0:int(int)', 'bits.cc', ['int'], source='Twin'),
          function('num.Clamp:int(int)', 'bits.cc', ['int']),
          function('num.Bits.Width:int(int)', 'bits.h', ['int'])]
    library = native.compile_sources(source, fs[:4] + fs[5:], tmp_path / 'work', population=fs)
    member = 'C++ non-static member function: the native oracle has no receiver to call it on'
    assert library.skipped == {
        fs[0]['name']: member, fs[1]['name']: member,
        fs[2]['name']: 'C++ member is not accessible from a thunk (private or protected)',
        fs[3]['name']: 'ambiguous conditional or overloaded entry point',
        fs[5]['name']: 'ambiguous conditional or overloaded entry point'}
    # The refused thunks did not take their translation units down with them.
    assert library(fs[6])(-500) == -100 and library(fs[7])(4) == 32


def test_a_cpp_header_that_does_not_compile_refuses_only_its_own_entry_points(tmp_path, native):
    source = corpus(tmp_path, {'broken.hpp': 'inline int Broken(int x) { return undeclared(x); }\n',
                               'ok.cc': 'int Ok(int x) { return x + 1; }\n'})
    fs = [function('Broken:int(int)', 'broken.hpp', ['int']), function('Ok:int(int)', 'ok.cc', ['int'])]
    library = native.compile_sources(source, fs, tmp_path / 'work')
    assert library.skipped == {fs[0]['name']: 'translation unit compile failed: broken.hpp'}
    assert library(fs[1])(1) == 2


def test_a_c_corpus_keeps_the_c_path(tmp_path, differential):
    """Guarded by language: a `.h` in a C project is still not a translation unit, and a
    C function is still called by its source name with no C++ in sight."""
    if not shutil.which('cc'):
        pytest.skip('C compiler unavailable')
    import native_c
    source = corpus(tmp_path, {'m.h': 'static inline int Half(int x) { return x / 2; }\n',
                               'm.c': '#include "m.h"\nint twice(int x) { return 2 * Half(x) + x % 2 * 2; }\n'})
    assert not native_c.cpp_corpus(source)
    fs = [dict(name='Half', sourceName='Half', file='m.h', params=['x'],
               paramIntegerTypes=['i32'], returnIntegerType='i32'),
          dict(name='twice', sourceName='twice', file='m.c', params=['x'],
               paramIntegerTypes=['i32'], returnIntegerType='i32')]
    library = native_c.compile_sources(source, fs, tmp_path / 'work')
    assert library.skipped == {'Half': 'entry point is not in a source translation unit'}
    assert library(fs[1])(5) == 6
    assert '.cpp' not in str(library.info['combined_build']['command'])


def test_a_header_only_cpp_library_is_a_cpp_corpus(tmp_path, native):
    """No translation unit at all: a `.h` with a C++-only declaration makes the corpus C++
    (a header-only library), a `.h` without one does not, and any `.c` keeps it C."""
    source = corpus(tmp_path, {'digits.h': 'namespace d {\ninline int Count(unsigned n) '
                                           '{ return n < 10 ? 1 : 2; }\n}\n'})
    assert native.cpp_corpus(source)
    f = function('d.Count:int(unsigned)', 'digits.h', ['unsigned'], tags=['u32'])
    assert native.compile_sources(source, [f], tmp_path / 'work')(f)(42) == 2
    plain = tmp_path / 'plain'
    plain.mkdir()
    (plain / 'p.h').write_text('static inline int half(int x) { return x / 2; }\n')
    assert not native.cpp_corpus(plain)
    (source / 'main.c').write_text('int main(void) { return 0; }\n')
    assert not native.cpp_corpus(source)


def test_cpp_callee_identity():
    native_c = load(str(Path(SCRIPTS) / 'native_c.py'), 'af_native_c_identity')
    f = function('a.B.c:int(int,unsigned long)', 'x.cc', ['const int', 'unsigned long'], tags=['i32', 'u64'])
    assert native_c.cpp_callee(f) == ('::a::B::c', 'int (*)(int, unsigned long)')
    assert native_c.cpp_callee(function('g:int()', 'x.cc')) == ('::g', 'int (*)(void)')
    assert native_c.cpp_callee(function('a.h:int(uc16)', 'x.cc', ['uc16'])) == ('::a::h', None)
    assert native_c.cpp_callee(function('a.T<int>.h:int(int)', 'x.cc', ['int'])) == \
        'source callable identity unavailable'


def test_pr_mode_routes_cpp_to_the_native_leg(tmp_path, monkeypatch):
    """C++ is a row of the routing table (`runtime_backends.CROSS_REVISION_INPUTS['cpp']`,
    toolchain `c++`); a `.h` is C++ only in a C++ corpus, and a `.c` stays on the C row."""
    pr_mode = load(str(Path(SCRIPTS) / 'pr_mode.py'), 'af_pr_mode_cpp')
    backends = pr_mode._backends()
    assert [pr_mode.source_language(p) for p in ('a.cc', 'a.cpp', 'a.cxx', 'a.hpp', 'a.h', 'a.c')] == \
        ['cpp', 'cpp', 'cpp', 'cpp', 'c-header', 'c']
    header = dict(name='n.C.f:int(int)', file='ieee.h', path='src/ieee.h')
    assert pr_mode.function_language(header) == 'c-header'
    assert pr_mode.function_language(header, cpp_headers=True) == 'cpp'
    monkeypatch.setattr(backends.shutil, 'which', lambda tool: '/usr/bin/' + tool)
    assert pr_mode.behaviour_plan([header], cpp_headers=True) == ('cpp', {})
    assert pr_mode.behaviour_plan([dict(header, file='a.cc', path='a.cc')]) == ('cpp', {})
    language, notes = pr_mode.behaviour_plan([header])
    assert language is None and 'shared by C and C++' in notes[header['name']]
    monkeypatch.setattr(backends.shutil, 'which', lambda tool: None)
    language, notes = pr_mode.behaviour_plan([dict(header, file='a.cc', path='a.cc')])
    assert language is None and 'c++ not on PATH' in notes[header['name']]
    assert 'C ABI thunks' in backends.CROSS_REVISION_INPUTS['cpp']
    assert backends.TOOLCHAIN['cpp'] == ['c++']
    # In a C++ corpus a `.h` is C++; a tree with a `.c` unit is a C corpus.
    cpp = tmp_path / 'cpp'
    cpp.mkdir()
    (cpp / 'ieee.h').write_text('namespace n {\nclass C { public: static int f(int x) { return x; } };\n}\n')
    assert pr_mode._native_c().cpp_corpus(cpp)
    (cpp / 'shim.c').write_text('int g(int x) { return x; }\n')
    assert not pr_mode._native_c().cpp_corpus(cpp)
