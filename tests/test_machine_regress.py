"""`scripts/machine_regress.py` and `autoform regress --machine`.

A two-commit C history whose second commit reorders `a * b / d` into `a / d * b`,
the same shape as the kernel's lcm fix (74a5fef7cb08). The search has to find an
input where the first version overflows, both lifted models have to reproduce the
two results, and Lean has to prove each one.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys

import pytest

from conftest import ROOT, load

ROOT = Path(ROOT)
regress = load(str(ROOT / 'scripts' / 'machine_regress.py'), 'af_machine_regress')

BEFORE = '''#include <linux/kernel.h>
unsigned long scale(unsigned long a, unsigned long b)
{
	unsigned long d = a > b ? b : a;
	if (!d)
		return 0;
	return (a * b) / d;
}
'''
AFTER = BEFORE.replace('(a * b) / d', '(a / d) * b')
SAME = '''#include <linux/kernel.h>
unsigned long twice(unsigned long a) { return a + a; }
'''


def have_toolchain():
    try:
        regress.tool('clang')
        regress.tool('ld.lld', '/opt/homebrew/bin/ld.lld', '/usr/local/opt/lld/bin/ld.lld')
    except regress.RegressError:
        return False
    probe = subprocess.run(['clang', '-target', 'aarch64-unknown-linux-gnu', '-x', 'c', '-c', '-',
                            '-o', os.devnull], input='int f(void){return 0;}', text=True,
                           capture_output=True)
    return probe.returncode == 0


needs_toolchain = pytest.mark.skipif(not have_toolchain(),
                                     reason='clang with the AArch64 target and ld.lld are required')
needs_lean = pytest.mark.skipif(shutil.which('lake') is None
                                and not (Path.home() / '.elan/bin/lake').exists(),
                                reason='Lean (lake) is required for the kernel checks')


def tree(root, text, extra=SAME):
    root.mkdir(parents=True)
    (root / 'scale.c').write_text(text)
    (root / 'twice.c').write_text(extra)
    return root


def test_call_setup_follows_each_calling_convention():
    sig = regress.read_signature.__globals__['Signature']
    value = regress.read_signature.__globals__['Value']
    two = sig(name='f', params=[value('a', 8, False, 'int'), value('b', 4, False, 'int')],
              ret=value(None, 8, False, 'int'))
    registers, memory, result = regress.call_setup('aarch64', two, [1 << 63, (1 << 32) + 5])
    assert registers['x0'] == 1 << 63 and registers['x1'] == 5
    assert registers['x30'] == regress.RETURN and registers['sp'] == regress.STACK
    assert all(registers[f'x{i}'] == 0 for i in range(19, 30)) and not memory and result == ['x0']
    registers, memory, result = regress.call_setup('x86_64', two, [7, 9])
    assert registers['RDI'] == 7 and registers['RSI'] == 9 and result == ['RAX']
    assert memory == {f'ram:{regress.STACK}:8': regress.RETURN}
    one = sig(name='g', params=[value('x', 8, False, 'int')], ret=value(None, 4, False, 'int'))
    registers, memory, result = regress.call_setup('i386', one, [(3 << 32) | 4])
    assert (registers['EAX'], registers['EDX']) == (4, 3) and result == ['EAX']
    assert memory == {f'ram:{regress.STACK}:4': regress.RETURN}
    with pytest.raises(regress.RegressError, match='takes 1 arguments'):
        regress.call_setup('aarch64', one, [1, 2])


def test_candidates_start_with_boundaries_and_are_reproducible():
    sig = regress.read_signature.__globals__['Signature']
    value = regress.read_signature.__globals__['Value']
    two = sig(name='f', params=[value('a', 8, False, 'int')] * 2, ret=value(None, 8, False, 'int'))
    first = regress.candidates(two, 50000, seed=1)
    assert first == regress.candidates(two, 50000, seed=1)
    assert (0, 0) in first and ((1 << 64) - 1, (1 << 63)) in first
    assert len(set(first)) == len(first)


@needs_toolchain
def test_build_links_across_files_and_reads_dwarf(tmp_path):
    source = tree(tmp_path / 'src', BEFORE)
    elf, commands = regress.build(source, ['scale.c', 'twice.c'], 'aarch64', tmp_path / 'out')
    symbols = regress.function_symbols(elf)
    assert {'scale', 'twice'} <= set(symbols)
    signature = regress.read_signature(elf, 'scale')
    assert [p.size for p in signature.params] == [8, 8] and signature.ret.size == 8
    assert any('ld.lld' in c[0] for c in commands)
    with pytest.raises(regress.RegressError, match='not found in this tree'):
        regress.build(source, ['missing.c'], 'aarch64', tmp_path / 'out2')


@needs_toolchain
@needs_lean
def test_divergence_is_found_confirmed_on_both_models_and_kernel_checked(tmp_path):
    base, head = tree(tmp_path / 'base', BEFORE), tree(tmp_path / 'head', AFTER)
    native = platform.machine() in ('arm64', 'aarch64')
    report = regress.run(base, head, ['scale.c', 'twice.c'], [], out=tmp_path / 'out',
                         native=native, limit=3000)
    records = {r['subject']: r for r in report['functions']}
    # Only the function whose code changed is compared by default.
    assert set(records) == {'scale'}
    record = records['scale']
    assert record['status'] == 'diverges', record
    witness = next(w for w in record['witnesses'] if w['kernel_checked'])
    a, b = witness['inputs']
    d = min(a, b)
    assert witness['base'] == ((a * b) % (1 << 64)) // d
    assert witness['head'] == ((a // d) * b) % (1 << 64)
    assert witness['native_confirmed'] is native
    for path in witness['lean_checks'].values():
        text = Path(path).read_text()
        assert 'theorem checked_0' in text and 'by rfl' in text
    assert report['verdict'] == 'behavior-changed'
    assert report['behavior_changes'][0]['kernel_checked'] is True
    assert (tmp_path / 'out' / 'regression.md').read_text().startswith('# Machine regression report')


@needs_toolchain
@needs_lean
def test_unchanged_function_reports_no_divergence_not_equivalence(tmp_path):
    base, head = tree(tmp_path / 'base', BEFORE), tree(tmp_path / 'head', BEFORE)
    report = regress.run(base, head, ['scale.c', 'twice.c'], ['twice'], out=tmp_path / 'out',
                         native=False, limit=40)
    record = report['functions'][0]
    assert record['status'] == 'no-divergence-found'
    assert record['search']['method'] == 'lean-model' and record['search']['exhaustive'] is False
    assert report['verdict'] == 'no-divergence-found' and not report['behavior_changes']


def git(*args, cwd):
    return subprocess.run(['git', *args], cwd=cwd, check=True, text=True, capture_output=True,
                          env=dict(os.environ, GIT_AUTHOR_NAME='t', GIT_AUTHOR_EMAIL='t@t',
                                   GIT_COMMITTER_NAME='t', GIT_COMMITTER_EMAIL='t@t')).stdout.strip()


@needs_toolchain
@needs_lean
def test_cli_regress_machine_on_a_local_repository(tmp_path, monkeypatch, capsys):
    repo = tree(tmp_path / 'repo', BEFORE)
    git('init', '-q', '-b', 'main', cwd=repo)
    git('add', '.', cwd=repo)
    git('commit', '-q', '-m', 'before', cwd=repo)
    git('tag', 'before', cwd=repo)
    (repo / 'scale.c').write_text(AFTER)
    git('commit', '-q', '-am', 'after', cwd=repo)
    monkeypatch.syspath_prepend(str(ROOT / 'src'))
    import autoform.cli as cli
    workspace = tmp_path / 'ws'
    assert cli.main(['--workspace', str(workspace), 'init']) == 0
    # The workspace is its own Lean project; without a build cache `lake` would fetch
    # dependencies from the network. Seed it with a copy-on-write clone of this one.
    if subprocess.run(['cp', '-Rc', str(ROOT / '.lake'), str(workspace / '.lake')],
                      capture_output=True).returncode:
        pytest.skip('copy-on-write cloning of the build cache is unavailable here')
    code = cli.main(['--workspace', str(workspace), 'regress', str(repo), 'Probe', '--base', 'before',
                     '--machine', '--files', 'scale.c', 'twice.c', '--functions', 'scale'])
    assert code == 1, capsys.readouterr()
    out = workspace / 'artifacts/regression/Probe'
    report = json.loads((out / 'machine' / 'regression.json').read_text())
    runs = json.loads((out / 'runs.json').read_text())
    assert report['verdict'] == 'behavior-changed'
    assert report['base']['label'] == runs['base']['commit'] == git('rev-parse', 'before', cwd=repo)
    assert report['head']['label'] == git('rev-parse', 'HEAD', cwd=repo)
    sources = workspace / 'sources'
    assert not sources.exists() or not any(sources.iterdir())


def test_cli_refuses_machine_without_files(tmp_path, monkeypatch, capsys):
    monkeypatch.syspath_prepend(str(ROOT / 'src'))
    import autoform.cli as cli
    with pytest.raises(SystemExit):
        cli.main(['--workspace', str(tmp_path / 'ws'), 'regress', str(tmp_path), 'Probe',
                  '--base', 'x', '--machine'])
    assert '--machine needs --files' in capsys.readouterr().err
