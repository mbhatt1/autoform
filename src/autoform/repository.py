"""Resolve a local source directory or acquire a Git revision for one run."""
from __future__ import annotations

import datetime
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from urllib.parse import urlsplit, urlunsplit


def is_git_url(value):
    # Detection must be total: urlsplit raises for malformed bracketed hosts.
    # Validate recognized URLs during acquisition so failures get a run record.
    return (bool(re.match(r"(?i)^(?:https?|ssh|git|file):", value))
            or bool(re.fullmatch(r"[^/\s:@]+@[^/\s:]+:.+", value)))


def display_url(value):
    if not re.match(r"(?i)^(?:https?|ssh|git|file):", value):
        return value
    try:
        parsed = urlsplit(value)
    except ValueError:
        return '<invalid Git URL>'
    if parsed.scheme in {"http", "https", "ssh", "git", "file"}:
        # Authentication belongs in the user's credential helper, never a report.
        return urlunsplit((parsed.scheme, parsed.netloc.rsplit('@', 1)[-1],
                           parsed.path, "", ""))
    return value


def redact_git_output(text, source):
    # Git may normalize a URL (e.g. remove its query) in diagnostics, and
    # submodules can report URLs other than the requested root repository.
    text = text.replace(source, display_url(source))
    return re.sub(r"(?i)(?:https?|ssh|git|file)://[^\s'\"<>]+",
                  lambda match: display_url(match.group()), text)


def resolve_source(value, workspace, module, *, ref=None, subdir=None):
    workspace = Path(workspace)
    report = workspace / 'artifacts/pipeline' / module
    report.mkdir(parents=True, exist_ok=True)
    record = dict(input=display_url(value), ref=ref, subdir=subdir or '.',
                  status='acquiring', started_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
    manifest = report / 'repository.json'

    def save():
        manifest.write_text(json.dumps(record, indent=2) + '\n')

    def git(*args, cwd=None):
        command = ['git', '-c', 'core.hooksPath=/dev/null', *map(str, args)]
        env = dict(os.environ, GIT_TERMINAL_PROMPT='0')
        try:
            result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=900)
        except subprocess.TimeoutExpired as exc:
            # TimeoutExpired.__str__ includes the full argv, including URL credentials.
            raise ValueError('Git checkout timed out after 900 seconds') from exc
        with (report / 'checkout.log').open('a') as stream:
            stream.write(redact_git_output(result.stdout, value))
        if result.returncode:
            raise ValueError('Git checkout failed; see ' + str(report / 'checkout.log'))
        return result.stdout.strip()

    save()
    (report / 'checkout.log').write_text('')
    # A clone that fails partway used to leave its temporary tree under
    # `<workspace>/sources/` forever; whoever created it has to remove it.
    created = None
    try:
        if ref and (ref.startswith('-') or any(c.isspace() for c in ref)):
            raise ValueError('Git ref must be a branch, tag or commit without leading options or whitespace')
        remote = is_git_url(value)
        if remote:
            if re.match(r"(?i)^(?:https?|ssh|git|file):", value):
                parsed = urlsplit(value)
                if parsed.scheme != 'file' and not parsed.hostname:
                    raise ValueError('Git URL must include a hostname')
                # Accessing port validates malformed or out-of-range port syntax.
                _ = parsed.port
            sources = workspace / 'sources'
            sources.mkdir(exist_ok=True)
            created = Path(tempfile.mkdtemp(prefix=module + '-', dir=sources))
            checkout = created / 'checkout'
            print('==> checkout ' + display_url(value), flush=True)
            git('clone', '--depth', '1', '--filter=blob:none', '--no-checkout', '--', value, checkout)
            if ref:
                git('fetch', '--depth', '1', 'origin', ref, cwd=checkout)
            revision = 'FETCH_HEAD' if ref else 'HEAD'
            commit = git('rev-parse', '--verify', revision + '^{commit}', cwd=checkout)
            # Keep the full checkout even when analysis targets a subdirectory:
            # Linux lib/test_bitmap.c includes a sibling tools/testing header.
            # Omitting sibling trees can silently change frontend discovery.
            git('checkout', '--detach', commit, cwd=checkout)
            git('submodule', 'update', '--init', '--recursive', '--depth', '1', cwd=checkout)
            record.update(kind='git', checkout=str(checkout), commit=commit,
                          submodules=git('submodule', 'status', '--recursive', cwd=checkout).splitlines())
        else:
            if ref:
                raise ValueError('--ref requires a Git URL; local directories are used as they are')
            checkout = Path(value).resolve()
            if not checkout.is_dir():
                raise ValueError('source directory does not exist: ' + str(checkout))
            record.update(kind='local', checkout=str(checkout))
        source = (checkout / (subdir or '.')).resolve()
        if not source.is_relative_to(checkout.resolve()) or not source.is_dir():
            raise ValueError('--subdir must select an existing directory inside the checkout')
        record.update(status='ready', source=str(source))
        save()
        return source, record
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as exc:
        if created is not None:
            shutil.rmtree(created, ignore_errors=True)
        record.update(status='failed', error=redact_git_output(str(exc), value))
        save()
        raise ValueError(record['error']) from exc
