"""What `autoform pr` forwards to `scripts/pr_mode.py`, parsed but never run.

Two flags used to disagree with their documentation. `--cases` was always forwarded
with the CLI's own default of 5, so pr_mode.py's `$AUTOFORM_CASES` fallback -- the one
`docs/cli.md` documents -- could never apply to `autoform pr`. `--behaviour-cases` was
documented as a `pr` option (`docs/evidence-levels.md`) and implemented by pr_mode.py,
but the CLI did not accept it. These tests pin the forwarding through `cli.build_parser()`
and `cli._pr` with the subprocess launcher replaced, so no workspace, Joern or Lean is
needed and nothing is executed.
"""
from __future__ import annotations

from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from autoform import cli  # noqa: E402


def forwarded_argv(monkeypatch, tmp_path, *flags):
    """Parse `pr <local repo> --base HEAD~1 <flags>` and return the argv `_pr` would run."""
    repo = tmp_path / 'repo'
    (repo / '.git').mkdir(parents=True)          # `_pr` only checks that the directory exists
    workspace = tmp_path / 'ws'
    workspace.mkdir()
    captured = {}

    def fake_run(command, *, env, timeout=None, **_):
        captured['command'] = [str(part) for part in command]
        captured['timeout'] = timeout
        return 0

    monkeypatch.setattr(cli, '_run_command', fake_run)
    args = cli.build_parser().parse_args(['pr', str(repo), '--base', 'HEAD~1', *flags])
    assert cli._pr(args, workspace, cli.environment()) == 0
    return captured['command']


def value_after(argv, flag):
    assert argv.count(flag) == 1, (flag, argv)
    return argv[argv.index(flag) + 1]


def test_pr_without_cases_omits_the_flag_so_the_env_var_fallback_applies(monkeypatch, tmp_path):
    argv = forwarded_argv(monkeypatch, tmp_path)
    assert argv[1].endswith('scripts/pr_mode.py')
    assert '--cases' not in argv
    assert '--behaviour-cases' not in argv
    # The flags that always travel still do.
    assert value_after(argv, '--mutants') == '0'
    assert float(value_after(argv, '--stage-timeout')) == 1800.0


def test_pr_cases_is_forwarded_when_given(monkeypatch, tmp_path):
    argv = forwarded_argv(monkeypatch, tmp_path, '--cases', '3')
    assert value_after(argv, '--cases') == '3'
    assert '--behaviour-cases' not in argv


def test_pr_behaviour_cases_is_accepted_and_forwarded(monkeypatch, tmp_path):
    argv = forwarded_argv(monkeypatch, tmp_path, '--behaviour-cases', '7')
    assert value_after(argv, '--behaviour-cases') == '7'
    assert '--cases' not in argv


def test_pr_parser_defaults_leave_both_counts_unset():
    args = cli.build_parser().parse_args(['pr', 'repo', '--base', 'main'])
    assert args.cases is None
    assert args.behaviour_cases is None


@pytest.mark.parametrize('flags', [['--cases', '0'], ['--behaviour-cases', '0']])
def test_pr_main_rejects_a_non_positive_count(flags, capsys):
    """The validation in `main` runs before any workspace is touched: argparse exits 2."""
    with pytest.raises(SystemExit) as exit_info:
        cli.main(['pr', 'repo', '--base', 'main', *flags])
    assert exit_info.value.code == 2
    assert flags[0] in capsys.readouterr().err


def test_pr_help_names_both_flags_and_the_env_fallback():
    pr = next(action for action in cli.build_parser()._actions
              if isinstance(action, cli.argparse._SubParsersAction)).choices['pr']
    text = pr.format_help()
    assert '--behaviour-cases' in text
    assert 'AUTOFORM_CASES' in text
