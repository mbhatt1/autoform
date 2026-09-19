"""Regressions exposed by running the public CLI on a real kernel tree."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest
from conftest import ROOT, SCRIPTS, load


def scalar(name, file, args=()):
    return dict(name=name, sourceName=name, file=file, params=list(args),
                paramIntegerTypes=['i32'] * len(args), returnIntegerType='i32')


def test_native_translation_unit_failure_preserves_working_static_function(tmp_path, differential):
    (tmp_path / 'good.c').write_text('static int good(int x) { return x + 7; }\n')
    (tmp_path / 'bad.c').write_text('#include "missing.h"\nint bad(void) { return 1; }\n')
    f, g = scalar('good', 'good.c', ['x']), scalar('bad', 'bad.c')
    result = differential.c_runtime(str(tmp_path), [f, g])
    assert result(f)(4) == 11
    assert result(g) is None
    assert result.info['files_compiled'] == 1
    assert 'compile/load failed' in result.skipped['bad']
    assert any('missing.h' in u['diagnostics'] for u in result.info['units'])


def test_native_keeps_cross_file_void_dependency(tmp_path, differential):
    (tmp_path / 'a.h').write_text('extern int g; void bump(void);\n')
    (tmp_path / 'b.h').write_text('#define INITIAL 4\n')
    (tmp_path / 'a.c').write_text('#include "a.h"\nint run(void) { bump(); return g; }\n')
    (tmp_path / 'b.c').write_text('#include "b.h"\nint g=INITIAL; void bump(void) { ++g; }\n')
    f = scalar('run', 'a.c')
    result = differential.c_runtime(str(tmp_path), [f])
    assert result(f)() == 5
    assert result.info['files_compiled'] == 2
    assert str(tmp_path / 'a.h') in result.info['dependencies_sha256']
    assert str(tmp_path / 'b.h') in result.info['dependencies_sha256']


def test_native_reports_complete_compile_failure(tmp_path, differential):
    (tmp_path / 'bad.c').write_text('#include "missing.h"\nint bad(void) { return 0; }\n')
    f = scalar('bad', 'bad.c')
    result = differential.c_runtime(str(tmp_path), [f])
    assert result(f) is None
    assert result.info['status'].startswith('unsupported:')
    assert result.info['units'][0]['exit_code'] != 0


def test_cpp_defines_reach_native_compiler(tmp_path, differential, monkeypatch):
    (tmp_path / 'f.c').write_text('int flag(void) { return FLAG; }\n')
    monkeypatch.setenv('CPP_DEFINES', 'FLAG=29')
    f = scalar('flag', 'f.c')
    assert differential.c_runtime(str(tmp_path), [f])(f)() == 29


def test_c_case_plan_detects_equality_mutant_and_preserves_abi(tmp_path, differential):
    import ctypes
    (tmp_path / 'compare.c').write_text('''
int original(int a, unsigned int b) { return a < b; }
int mutant(int a, unsigned int b) { return a <= b; }
''')
    fs = [scalar(name, 'compare.c', ['a', 'b']) for name in ('original', 'mutant')]
    for f in fs:
        f['paramIntegerTypes'] = ['i32', 'u32']
    library = differential.c_runtime(str(tmp_path), fs)
    # A random stream that never generates equal operands must still expose the
    # injected comparison bug. The same vector is passed to both native versions.
    stream = iter([2, 3, 4, 5, 6, 7, 8, 9])
    cases = list(differential.c_argument_cases(library(fs[0]).argtypes, 5, lambda: next(stream)))
    assert len(cases) == 5
    assert any(library(fs[0])(*args) != library(fs[1])(*args) for args, _ in cases)
    assert cases[0][1] == 'boundary-zero'
    wide = list(differential.c_argument_cases([ctypes.c_uint64, ctypes.c_int8], 2, lambda: -1))
    assert wide[1][0] == [18446744073709551615, -1]


def make_kernel(root):
    for name in ('Kbuild', 'Kconfig', 'Makefile', 'include/linux/kernel.h'):
        p = root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text('')
    (root / 'lib').mkdir()
    return root / 'lib'


def test_linux_profile_is_explicit_and_respects_user_defines(tmp_path, differential, monkeypatch):
    import source_context
    source = make_kernel(tmp_path)
    monkeypatch.setenv('CPP_DEFINES', 'BITS_PER_LONG=32,CONFIG_TEST=1')
    ctx = source_context.profile(source)
    assert ctx['kernel_root'] == str(tmp_path)
    assert ctx['configuration'] == 'portable-userspace'
    assert 'BITS_PER_LONG=32' in ctx['defines'] and 'BITS_PER_LONG=64' not in ctx['defines']
    assert '__init=' in ctx['defines']
    assert ctx['limitations']


def test_target_database_does_not_use_host_portability_oracle(tmp_path, differential, monkeypatch):
    source = make_kernel(tmp_path)
    database = tmp_path / 'compile_commands.json'
    database.write_text('[]')
    f = scalar('f', 'f.c')
    (source / 'f.c').write_text('int f(void) { return 1; }')
    result = differential.c_runtime(str(source), [f])
    assert result.info['context']['compilation_database'] == str(database)
    assert result(f) is None
    assert 'matching runtime adapter' in result.info['status']


def test_assure_parse_failure_still_emits_final_report_and_drops_stale_data(tmp_path):
    workspace = tmp_path / 'workspace'
    scripts = workspace / 'scripts'
    scripts.mkdir(parents=True)
    bundle = load(str(Path(ROOT) / 'build_support.py'), 'af_failure_bundle').runtime_files()
    for name, content in bundle.items():
        if name == 'autoform.sh' or name.startswith(('scripts/', 'cartographer/')):
            target = workspace / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
    source = tmp_path / 'source'
    source.mkdir()
    (source / 'f.c').write_text('int f(void) { return 1; }')
    report = workspace / 'artifacts/pipeline/Check'
    report.mkdir(parents=True)
    for name in ('specs.json', 'audit.json', 'mutation.json', 'ast-Check.json', 'ledger-Check.json'):
        (report / name).write_text('{"stale":true}')
    env = dict(os.environ, JOERN_HOME=str(tmp_path / 'absent'))
    proc = subprocess.run([sys.executable, scripts / 'assure.py', source, 'Check'],
                          env=env, capture_output=True, text=True, timeout=30)
    assert proc.returncode != 0, proc.stdout + proc.stderr
    run = json.loads((report / 'run.json').read_text())
    assert run['execution_status'] == 'completed_with_gaps'
    assert not run['verification_complete']
    assert run['stages']['mutation']['status'] == 'blocked'
    assert run['stages']['assurance']['status'] == 'completed'
    assert (report / 'assurance.md').is_file() and (report / 'summary.md').is_file()
    assert not (report / 'specs.json').exists() and not (report / 'audit.json').exists()
    assert not (report / 'ast-Check.json').exists()


def test_deep_hole_report_does_not_overflow_stack():
    sacm = load(str(Path(SCRIPTS) / 'sacm.py'), 'linux_sacm_depth')
    node = dict(k='holeS', label='effect:kernel-sync:spin_lock')
    for _ in range(2000):
        node = dict(k='seq', a=dict(k='skip'), b=node)
    out = []
    sacm.walk_holes(node, out)
    assert out == [('effect:kernel-sync:spin_lock', 'holeS')]


def test_joern_kernel_annotations_conditional_body_and_lock_effect(tmp_path, differential):
    if not os.environ.get('AUTOFORM_TEST_JOERN'):
        pytest.skip('set AUTOFORM_TEST_JOERN=1 to exercise the real frontend')
    import source_context
    source = make_kernel(tmp_path / 'kernel')
    (source / 'helpers.c').write_text('''
void spin_lock(int *p);
static int dark_body(unsigned int w) {
#if defined(AUTOFORM_UNAVAILABLE_BRANCH)
    return (int)w;
#endif
}
int __init init_helper(int x) { return x + 1; }
int lock_helper(int x) { spin_lock(&x); return x; }
''')
    joern = Path(os.environ.get('JOERN_HOME', Path.home() / 'joern'))
    if (joern / 'joern-cli').is_dir():
        joern /= 'joern-cli'
    ctx = source_context.profile(source)
    for command in (
        [joern / 'joern-parse', source, '--language', 'C', '--output', 'cpg.bin',
         *ctx['frontend_args']],
        [joern / 'joern', '--script', Path(ROOT) / 'cartographer/export_ast.sc',
         '--param', 'cpgPath=cpg.bin', '--param', 'out=ast.json', '--param', 'dataModel=lp64'],
    ):
        result = subprocess.run(command, cwd=tmp_path, capture_output=True, text=True, timeout=600)
        assert result.returncode == 0, result.stdout + result.stderr
    fs = {f['name']: f for f in json.loads((tmp_path / 'ast.json').read_text())}
    assert 'init_helper' in fs
    assert 'dark_body' in fs, 'a real conditional function must not disappear as a declaration'
    assert 'holeS' in json.dumps(fs['dark_body']['body'])
    assert 'effect:kernel-sync:spin_lock' in json.dumps(fs['lock_helper']['body'])
    metadata = json.loads((tmp_path / 'ast.json.meta.json').read_text())
    assert not metadata['sourceCensusComplete']
    assert metadata['truncatedByMethodLimit'] == 0
