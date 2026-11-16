"""One oversized, oddly named or slow file must not sink, or silently shrink, a run.

Each test here pins a failure seen or reproducible on large, messy repositories: a
generated multi-megabyte file handed to Joern, a path with spaces or non-ASCII names
dropped between inventory and scope, and a run stopped by `--timeout` that recorded
itself as passed.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from conftest import ROOT, SCRIPTS, load


@pytest.fixture
def inventory():
    return load(str(Path(SCRIPTS) / 'repository_inventory.py'), 'af_robust_inventory')


@pytest.fixture
def repository_scope():
    return load(str(Path(SCRIPTS) / 'repository_scope.py'), 'af_robust_scope')


def populate(root, files):
    for relative, content in files.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding='utf-8')


def test_oversized_source_is_a_recorded_exclusion_and_stays_a_coverage_gap(
        tmp_path, inventory, repository_scope):
    populate(tmp_path, {'a.py': 'def f(): return 1\n', 'generated.py': 'X = 1\n' * 100,
                        'notes.md': '#' * 1000})
    report = inventory.discover(tmp_path, max_bytes=100)
    files = {f['path']: f for f in report['files']}
    # Kept in the population and hashed, so source stability still covers it ...
    assert files['generated.py']['sha256'] and not files['generated.py']['supported']
    # ... and named as excluded with its reason. Non-source files are not capped.
    assert report['excluded'] == [{'path': 'generated.py', 'reason': 'max_file_bytes'}]
    assert report['max_file_bytes'] == 100 and report['scan_complete']
    ast = tmp_path / 'ast.json'
    ast.write_text(json.dumps([{'name': 'f', 'file': 'a.py'}]))
    rows = {r['path']: r['status'] for r in repository_scope.coverage(report, report, ast, {})['files']}
    assert rows['generated.py'] == 'unsupported' and rows['a.py'] == 'represented'

    uncapped = inventory.discover(tmp_path, max_bytes=0)
    assert uncapped['excluded'] == [] and uncapped['max_file_bytes'] is None
    assert uncapped['fingerprint'] != report['fingerprint']


def test_file_cap_comes_from_the_environment_and_a_bad_value_is_an_error(tmp_path, inventory, monkeypatch):
    populate(tmp_path, {'big.py': 'x = 1\n' * 50})
    monkeypatch.setenv('AUTOFORM_MAX_FILE_BYTES', '10')
    assert inventory.discover(tmp_path)['excluded'] == [{'path': 'big.py', 'reason': 'max_file_bytes'}]
    monkeypatch.delenv('AUTOFORM_MAX_FILE_BYTES')
    assert inventory.discover(tmp_path)['max_file_bytes'] == inventory.DEFAULT_MAX_FILE_BYTES
    monkeypatch.setenv('AUTOFORM_MAX_FILE_BYTES', '10MB')
    report = inventory.discover(tmp_path)
    assert not report['scan_complete'] and 'AUTOFORM_MAX_FILE_BYTES' in report['errors'][0]['reason']


def run_context(tmp_path, source, **env):
    context, args = tmp_path / 'context.json', tmp_path / 'args'
    environment = {k: v for k, v in os.environ.items() if k not in ('CPP_DEFINES', 'AUTOFORM_LANGUAGE')}
    subprocess.run([sys.executable, str(Path(SCRIPTS) / 'source_context.py'), str(source),
                    str(context), '--args-file', str(args)],
                   env={**environment, **env}, check=True, capture_output=True, text=True)
    return json.loads(context.read_text()), [a for a in args.read_bytes().decode().split('\0') if a]


def test_frontend_is_told_to_skip_oversized_files_with_one_argument_separator(tmp_path):
    source = tmp_path / 'source'
    populate(source, {'ok.c': 'int f(void){return 1;}\n', 'amalgamation.c': '/**/\n' * 100,
                      'odd,name.c': '/**/\n' * 100, 'data.json': ' ' * 1000})
    context, args = run_context(tmp_path, source, AUTOFORM_MAX_FILE_BYTES='100',
                                AUTOFORM_LANGUAGE='c', AUTOFORM_FRONTEND='C', CPP_DEFINES='DEBUG')
    # Joern forwards everything after the first --frontend-args, so there must be one.
    assert args == ['--frontend-args', '--define', 'DEBUG',
                    '--exclude', str((source / 'amalgamation.c').resolve())]
    assert [(e['path'], e['frontend_excluded']) for e in context['excluded_files']] == [
        ('amalgamation.c', True), ('odd,name.c', False)]
    # Non-C partitions drop the C defines but keep the exclusions.
    _, args = run_context(tmp_path, source, AUTOFORM_MAX_FILE_BYTES='100',
                          AUTOFORM_LANGUAGE='python', AUTOFORM_FRONTEND='PYTHONSRC', CPP_DEFINES='DEBUG')
    assert args == ['--frontend-args', '--exclude', str((source / 'amalgamation.c').resolve())]
    context, args = run_context(tmp_path, source, AUTOFORM_MAX_FILE_BYTES='0')
    assert args == [] and context['excluded_files'] == [] and context['max_file_bytes'] is None


def test_spaces_unicode_and_deep_trees_survive_inventory_and_scope(tmp_path, inventory, repository_scope):
    deep = '/'.join(['d'] * 120)
    names = ['dir with spaces/mod ule.py', 'ünïcødé/数据.py', 'emoji/\U0001F600.py',
             deep + '/leaf.py', 'quote\'s/a"b.py']
    source = tmp_path / 'checkout dir'
    populate(source, {name: 'def f(): return 1\n' for name in names})
    report = inventory.discover(source)
    assert report['scan_complete'], report['errors']
    assert sorted(f['path'] for f in report['files']) == sorted(names)
    assert all(f['supported'] and f['sha256'] for f in report['files'])
    ast = tmp_path / 'ast.json'
    # Joern names files relative to the source root or absolutely; both must resolve.
    ast.write_text(json.dumps([{'name': 'f%d' % i, 'file': name if i % 2 else str(source / name)}
                               for i, name in enumerate(names)]))
    selection = repository_scope.select_ast(ast, source, 'python', tmp_path / 'selection.json')
    assert selection['kept_files'] == sorted(names) and not selection['excluded_functions']
    coverage = repository_scope.coverage(report, inventory.discover(source), ast, {}, 'python')
    assert coverage['counts']['represented'] == len(names) and coverage['source_stable']
    assert coverage['unexpected_ast_files'] == []


@pytest.mark.skipif(shutil.which('bash') is None, reason='needs bash')
def test_timeout_records_the_stage_it_stopped_in_and_passes_heap_and_exclusions_to_joern(tmp_path):
    """`autoform source --timeout` used to leave `"status": "passed"` in pipeline.json."""
    root = tmp_path / 'root'
    for name in ('autoform.sh', 'scripts/integrity_guard.sh', 'scripts/source_context.py',
                 'scripts/repository_inventory.py'):
        (root / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(Path(ROOT) / name, root / name)
    joern = tmp_path / 'joern' / 'joern-cli'
    joern.mkdir(parents=True)
    seen = tmp_path / 'seen'
    (joern / 'joern-parse').write_text('#!/bin/sh\nprintf "%s\\n" "$JAVA_OPTS" "$@" > "' + str(seen)
                                       + '"\nexec sleep 60\n')
    (joern / 'joern-parse').chmod(0o755)
    source = tmp_path / 'source'
    populate(source, {'a.py': 'def f(): return 1\n', 'generated.py': 'X = 1\n' * 100})
    env = dict(os.environ, JOERN_HOME=str(tmp_path / 'joern'), AUTOFORM_PYTHON=sys.executable,
               AUTOFORM_JOERN_XMX='3g', AUTOFORM_MAX_FILE_BYTES='100', JAVA_OPTS='-Dcaller=1')
    sys.path.insert(0, str(Path(ROOT) / 'src'))
    try:
        from autoform import cli
    finally:
        sys.path.pop(0)
    code = cli._run_command(['bash', str(root / 'autoform.sh'), str(source), 'Probe'], env=env, timeout=3)
    assert code == 143
    record = json.loads((root / 'artifacts/pipeline/Probe/pipeline.json').read_text())
    assert record['stage'] == 'parse' and record['status'] == 'failed'
    assert record['exit_code'] == 143 and record['interrupted_by_signal'] == 15
    lines = seen.read_text().splitlines()
    assert lines[0].split() == ['-Dcaller=1', '-Xmx3g']
    assert lines[-2:] == ['--exclude', str((source / 'generated.py').resolve())]
    context = json.loads((root / 'artifacts/pipeline/Probe/context.json').read_text())
    assert [e['path'] for e in context['excluded_files']] == ['generated.py']


def test_invalid_heap_setting_is_refused_before_joern_starts(tmp_path):
    source = tmp_path / 'source'
    populate(source, {'a.py': 'x = 1\n'})
    root = tmp_path / 'root'
    for name in ('autoform.sh', 'scripts/integrity_guard.sh'):
        (root / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(Path(ROOT) / name, root / name)
    joern = tmp_path / 'joern' / 'joern-cli'
    joern.mkdir(parents=True)
    (joern / 'joern-parse').write_text('#!/bin/sh\nexit 0\n')
    (joern / 'joern-parse').chmod(0o755)
    result = subprocess.run(['bash', str(root / 'autoform.sh'), str(source), 'Probe'],
                            env=dict(os.environ, JOERN_HOME=str(tmp_path / 'joern'),
                                     AUTOFORM_PYTHON=sys.executable, AUTOFORM_JOERN_XMX='lots'),
                            capture_output=True, text=True, timeout=60)
    assert result.returncode == 2 and 'AUTOFORM_JOERN_XMX' in result.stderr


def run_cli(*args, env=None):
    environment = dict(os.environ, PYTHONPATH=str(Path(ROOT) / 'src'), **(env or {}))
    return subprocess.run([sys.executable, '-m', 'autoform', *args], cwd=ROOT, env=environment,
                          text=True, capture_output=True, timeout=120)


def test_cli_limits_are_validated_and_doctor_reports_memory(tmp_path):
    for command in ('source', 'assure'):
        refused = run_cli(command, str(tmp_path), '--max-file-bytes', '-1')
        assert refused.returncode == 2 and '--max-file-bytes' in refused.stderr
        refused = run_cli(command, str(tmp_path), '--timeout', '0')
        assert refused.returncode == 2 and '--timeout' in refused.stderr
    report = json.loads(run_cli('doctor', '--json', env={'AUTOFORM_JOERN_XMX': ''}).stdout)
    assert report['memory']['host_memory_bytes'] > 0 and report['memory']['joern_xmx'] is None
    assert report['memory']['hint'].startswith('Joern heap: JVM default')
    report = json.loads(run_cli('doctor', '--json', env={'AUTOFORM_JOERN_XMX': 'lots'}).stdout)
    assert 'not a JVM heap size' in report['memory']['hint']


# ------------------------------------------------- Lombok: never an empty CPG

def _context():
    return load(str(Path(SCRIPTS) / 'source_context.py'), 'af_robust_context')


def test_a_java_majority_tree_parses_originals_and_never_depends_on_delombok(tmp_path, monkeypatch):
    monkeypatch.delenv('AUTOFORM_FRONTEND', raising=False)
    monkeypatch.delenv('AUTOFORM_DELOMBOK_MODE', raising=False)
    context = _context()
    (tmp_path / 'src/main/java/p').mkdir(parents=True)
    for name in ('A', 'B'):
        (tmp_path / f'src/main/java/p/{name}.java').write_text('import lombok.Data;\n@Data class %s {}\n' % name)
    (tmp_path / 'tool.py').write_text('')
    (tmp_path / '.hidden').mkdir()
    for i in range(5):
        (tmp_path / f'.hidden/x{i}.py').write_text('')   # hidden trees do not vote
    assert context.guessed_frontend(tmp_path) == 'JAVASRC'
    assert context.jvm_frontend_args(tmp_path) == ['--delombok-mode', 'types-only']
    monkeypatch.setenv('AUTOFORM_DELOMBOK_MODE', 'no-delombok')
    assert context.jvm_frontend_args(tmp_path) == ['--delombok-mode', 'no-delombok']
    for i in range(3):
        (tmp_path / f'm{i}.py').write_text('')
    assert context.guessed_frontend(tmp_path) == 'PYTHONSRC' and context.jvm_frontend_args(tmp_path) == []
    monkeypatch.setenv('AUTOFORM_FRONTEND', 'javasrc')
    assert context.jvm_frontend_args(tmp_path) == ['--delombok-mode', 'no-delombok']


@pytest.mark.skipif(shutil.which('git') is None, reason='git is not installed')
def test_pr_treats_an_empty_ast_from_joern_as_a_failed_export(tmp_path, monkeypatch):
    sys.path.insert(0, SCRIPTS)
    import pr_fixture
    pr_mode = load(str(Path(SCRIPTS) / 'pr_mode.py'), 'af_robust_pr')
    history = pr_fixture.make_history(tmp_path / 'repo')
    monkeypatch.setattr(pr_mode, 'export_ast', lambda source, out, *rest: Path(out).write_text('[]'))
    out = tmp_path / 'out'
    code = pr_mode.main([history['repo'], '--base', 'base', '--head', 'head', '--module', 'PullRequestEmpty',
                         '--out', str(out), '--no-behaviour'])
    report = json.loads((out / 'pr.json').read_text())
    assert code == 2
    assert report['stages']['export'] == {
        'status': 'failed', 'reason': 'the exporter produced an empty AST (0 functions); see parse.log'}


# ------------------------------- Kotlin: the dataflow overlay must not sink a run

OVERLAY_CRASH = ('ERROR ReachingDefPass Pass io.joern.dataflowengineoss.passes.reachingdef.ReachingDefPass '
                 'failed\njava.util.NoSuchElementException: key not found: MethodRef')


def fake_joern(tmp_path, failure):
    """A JOERN_HOME whose default `joern-parse` fails printing `failure`, whose
    `--nooverlays` parse succeeds, and whose `joern --script` stands in for each script.
    Every call is appended to the returned `calls` file, one line per call."""
    joern = tmp_path / 'joern' / 'joern-cli'
    joern.mkdir(parents=True)
    calls = tmp_path / 'calls'
    (joern / 'joern-parse').write_text(f'''#!/bin/sh
echo "joern-parse $*" >> "{calls}"
for a in "$@"; do [ "$a" = --nooverlays ] && {{ echo "parsed without overlays"; exit 0; }}; done
cat <<'LOG'
{failure}
LOG
exit 1
''')
    (joern / 'joern').write_text(f'''#!/bin/sh
echo "joern $*" >> "{calls}"
out=; script=
for a in "$@"; do case "$a" in out=*) out="${{a#out=}}";; *.sc) script="$a";; esac; done
case "$script" in
  */prepare_cpg.sc) echo "prepared cpg without dataflowOss; overlays: base,dataflowOss"; : > "$out";;
  */formalization_graph.sc) echo '{{}}' > "$out";;
  */export_ast.sc) echo '[{{"name": "f", "file": "A.java"}}]' > "$out"
                   echo "exported 1 functions + 0 module initializers to $out";;
esac
''')
    for name in ('joern-parse', 'joern'):
        (joern / name).chmod(0o755)
    return calls


def java_tree(tmp_path):
    source = tmp_path / 'source'
    populate(source, {'src/main/java/p/A.java': 'package p;\nclass A { int f() { return 1; } }\n'})
    return source


def run_pipeline(tmp_path, failure):
    root = tmp_path / 'root'
    for name in ('autoform.sh', 'scripts/integrity_guard.sh', 'scripts/source_context.py',
                 'scripts/repository_inventory.py'):
        (root / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(Path(ROOT) / name, root / name)
    calls = fake_joern(tmp_path, failure)
    env = {k: v for k, v in os.environ.items()
           if k not in ('AUTOFORM_FRONTEND', 'AUTOFORM_DELOMBOK_MODE', 'AUTOFORM_LANGUAGE')}
    result = subprocess.run(['bash', str(root / 'autoform.sh'), str(java_tree(tmp_path)), 'Probe'],
                            env=dict(env, JOERN_HOME=str(tmp_path / 'joern'), AUTOFORM_PYTHON=sys.executable),
                            capture_output=True, text=True, timeout=120)
    report = root / 'artifacts/pipeline/Probe'
    return result, json.loads((report / 'pipeline.json').read_text()), report, calls.read_text().splitlines()


@pytest.mark.skipif(shutil.which('bash') is None, reason='needs bash')
def test_pipeline_skips_only_a_crashing_dataflow_overlay_and_records_it(tmp_path):
    result, record, report, calls = run_pipeline(tmp_path, OVERLAY_CRASH)
    # Past parse and graph; the stub tree has no repository_scope.py, which stops it there.
    assert record['stage'] == 'export', result.stderr
    assert record['overlays'].startswith('dataflowOss skipped:')
    assert record['overlays'].endswith('the exporter reads no dataflow')
    log = (report / 'parse.log').read_text()
    assert 'ReachingDefPass' in log and 'autoform: dataflowOss skipped' in log
    parses = [c for c in calls if c.startswith('joern-parse')]
    assert len(parses) == 2 and '--nooverlays' not in parses[0] and '--nooverlays' in parses[1]
    # The second attempt keeps the first one's frontend arguments.
    assert all('--frontend-args --delombok-mode types-only' in c for c in parses)
    assert any('prepare_cpg.sc' in c for c in calls)


@pytest.mark.skipif(shutil.which('bash') is None, reason='needs bash')
def test_pipeline_has_no_fallback_for_any_other_parse_failure(tmp_path):
    result, record, report, calls = run_pipeline(
        tmp_path, 'ERROR kotlin2cpg: could not parse Main.kt\nError: frontend failed')
    assert result.returncode == 1
    assert record['stage'] == 'parse' and record['status'] == 'failed' and 'overlays' not in record
    assert 'dataflowOss skipped' not in (report / 'parse.log').read_text()
    assert len(calls) == 1 and calls[0].startswith('joern-parse')


def test_pr_export_skips_only_a_crashing_dataflow_overlay_and_records_it(tmp_path, monkeypatch):
    monkeypatch.delenv('AUTOFORM_FRONTEND', raising=False)
    monkeypatch.delenv('AUTOFORM_DELOMBOK_MODE', raising=False)
    # The export passes source_context's whole frontend list; no ambient C setting may join it.
    for name in ('CPP_DEFINES', 'AUTOFORM_COMPILE_COMMANDS', 'AUTOFORM_LANGUAGE'):
        monkeypatch.delenv(name, raising=False)
    pr_mode = load(str(Path(SCRIPTS) / 'pr_mode.py'), 'af_robust_pr_overlay')
    calls = fake_joern(tmp_path, OVERLAY_CRASH)
    monkeypatch.setenv('JOERN_HOME', str(tmp_path / 'joern'))
    logs = tmp_path / 'logs'
    logs.mkdir()
    notes = pr_mode.export_ast(java_tree(tmp_path), tmp_path / 'ast.json', logs, 60)
    assert notes['overlays'].startswith('dataflowOss skipped:')
    assert notes['overlays'].endswith('the exporter reads no dataflow')
    assert 'autoform: dataflowOss skipped' in (logs / 'parse.log').read_text()
    parses = [c for c in calls.read_text().splitlines() if c.startswith('joern-parse')]
    assert len(parses) == 2 and '--nooverlays' in parses[1]
    assert all('--frontend-args --delombok-mode types-only' in c for c in parses)

    other = tmp_path / 'other'
    other.mkdir()
    calls = fake_joern(other, 'Error: frontend failed')
    monkeypatch.setenv('JOERN_HOME', str(other / 'joern'))
    with pytest.raises(pr_mode.PrError, match=r'joern-parse failed \(exit 1\)'):
        pr_mode.export_ast(java_tree(other), other / 'ast.json', logs, 60)
    assert len(calls.read_text().splitlines()) == 1


@pytest.mark.skipif(shutil.which('git') is None, reason='git is not installed')
def test_pr_report_carries_the_skipped_overlay_on_the_exporter_record(tmp_path, monkeypatch):
    sys.path.insert(0, SCRIPTS)
    import pr_fixture
    pr_mode = load(str(Path(SCRIPTS) / 'pr_mode.py'), 'af_robust_pr_overlay_report')
    history = pr_fixture.make_history(tmp_path / 'repo')
    note = 'dataflowOss skipped: a test; the exporter reads no dataflow'
    ast = [{'name': 'numbers.py:<module>.unrelated', 'file': 'numbers.py', 'params': [], 'body': None}]

    def export(source, out, *rest):
        Path(out).write_text(json.dumps(ast))
        return {'overlays': note}
    monkeypatch.setattr(pr_mode, 'export_ast', export)
    out = tmp_path / 'out'
    pr_mode.main([history['repo'], '--base', 'base', '--head', 'head', '--module', 'PullRequestOverlay',
                  '--out', str(out), '--no-behaviour'])
    report = json.loads((out / 'pr.json').read_text())
    assert report['exporter']['overlays'] == note
    assert report['stages']['export']['overlays'] == note


# The smallest Kotlin found that crashes Joern 4.0.606's ReachingDefPass
# (`key not found: MethodRef`): a lambda in a getter that reads a file-private const,
# plus an extension function on the class. Without the const, it parses.
KOTLIN_OVERLAY_CRASH = '''package p

private const val PREFIX = 3

class Account(val value: Long) {
    val group
        get() = "$value".take(PREFIX).toInt().let { g -> g + 1 }
}

fun Account.probe(): Long = value
'''


def test_real_joern_exports_kotlin_whose_dataflow_overlay_crashes(tmp_path, monkeypatch):
    if os.environ.get('AUTOFORM_TEST_JOERN') != '1':
        pytest.skip('set AUTOFORM_TEST_JOERN=1 to parse Kotlin through Joern')
    pr_mode = load(str(Path(SCRIPTS) / 'pr_mode.py'), 'af_robust_pr_kotlin')
    if not (pr_mode.joern_home() / 'joern-parse').is_file():
        pytest.skip('Joern not found (JOERN_HOME)')
    populate(tmp_path / 'src', {'A.kt': KOTLIN_OVERLAY_CRASH})
    notes = pr_mode.export_ast(tmp_path / 'src', tmp_path / 'ast.json', tmp_path, 900)
    assert 'ReachingDefPass' in (tmp_path / 'parse.log').read_text()
    assert notes['overlays'].startswith('dataflowOss skipped:')
    data = json.loads((tmp_path / 'ast.json').read_text())
    names = [f['name'] for f in (data['functions'] if isinstance(data, dict) else data)]
    assert any(name.startswith('p.probe:') for name in names), names
