"""One sandbox for every process that runs the code under test.

The differential oracle (its own re-execution and its Node/JVM/Go drivers), the native C
worker, and the nl stages (tracer, runtime runner, coverage fuzzer, emitted-test pytest)
all launch the subject through `sandboxed(cmd, cwd=, env=, work=, writable=, read_only=)`.
It returns the wrapped argv and environment; the caller keeps its own `subprocess` call,
its deadline and its process group. Every mechanism here either execs the command in place
(`sandbox-exec`, `unshare`) or dies with its parent (`bwrap --die-with-parent`), so the
caller's `os.killpg` on the session still reaches the subject.

What the sandbox is, per host:

  macOS   `/usr/bin/sandbox-exec` with a generated seatbelt profile: `(deny network*)`,
          `(deny file-write*)` except `work`, `writable` and the device nodes a process
          needs; anything readable on the host stays readable.
  Linux   `bwrap` when it runs: the host tree bound read-only, `work` and `writable`
          bound read-write, a new (empty) network namespace. Otherwise `unshare -rn`
          for the network with each `read_only` path bind-mounted read-only; writes
          elsewhere are NOT limited and the record says so.
  none    the launch FAILS (`SandboxUnavailable` names what to install). The explicit
          opt-out is `AUTOFORM_SANDBOX=off`; it is written into every artifact a run
          produces (`sandbox: {mechanism: "off", enforced: false}`), never implied.

`TMPDIR` of the sandboxed process is `<work>/tmp`, so the ordinary temp directory is not
a writable hole, and a launch that already runs inside the sandbox (`AUTOFORM_SANDBOX_ACTIVE`
in its environment) is passed through unchanged and reported as inherited.

The record every artifact carries:

    {"mechanism": "seatbelt" | "bwrap" | "unshare" | "off" | "none",
     "enforced": bool, "network": "denied" | "unrestricted",
     "filesystem": {...} | "unrestricted", "reason": <why not enforced>}

What it is not: not a container, not a syscall filter, not a defence against a kernel or
sandbox-exec bug, and not a limit on CPU, memory or file descriptors (the callers' deadlines
and the native worker's core limit do that). It stops the two things the trust model
promises the code under test cannot do: talk to the network and write outside its work
directory.
"""
from __future__ import annotations

import functools
import json
import os
import shutil
import subprocess
import sys

ENV = 'AUTOFORM_SANDBOX'                  # unset/on (required), off (recorded opt-out), or a mechanism
ACTIVE = 'AUTOFORM_SANDBOX_ACTIVE'        # JSON record in the environment of a sandboxed process
MECHANISMS = ('seatbelt', 'bwrap', 'unshare')
PROBE_TIMEOUT = 30

INSTALL = {
    'darwin': '`/usr/bin/sandbox-exec` ships with macOS; it is missing or refused to run',
    'linux': ('install bubblewrap (`apt-get install bubblewrap` / `dnf install bubblewrap`), or '
              'util-linux `unshare` with unprivileged user namespaces enabled '
              '(`sysctl kernel.unprivileged_userns_clone=1`, and on Ubuntu 24.04 '
              '`kernel.apparmor_restrict_unprivileged_userns=0`)'),
}


class SandboxUnavailable(RuntimeError):
    """No mechanism can confine the code under test and the opt-out was not given."""


class Launch:
    """The wrapped command: pass `argv`, `cwd`, `env` to your own subprocess call."""
    __slots__ = ('argv', 'cwd', 'env', 'record')

    def __init__(self, argv, cwd, env, record):
        self.argv, self.cwd, self.env, self.record = list(argv), cwd, env, record

    def run(self, **kwargs):
        return subprocess.run(self.argv, cwd=self.cwd, env=self.env, **kwargs)

    def popen(self, **kwargs):
        return subprocess.Popen(self.argv, cwd=self.cwd, env=self.env, **kwargs)

    def __iter__(self):
        return iter((self.argv, self.env, self.record))


def policy(environ=None) -> str:
    value = ((environ if environ is not None else os.environ).get(ENV) or 'on').strip().lower()
    if value in ('on', 'off') or value in MECHANISMS:
        return value
    raise ValueError('%s=%r: expected on, off or one of %s' % (ENV, value, ', '.join(MECHANISMS)))


def active(environ=None):
    """The record of the sandbox this process already runs inside, or None."""
    raw = (environ if environ is not None else os.environ).get(ACTIVE)
    if not raw:
        return None
    try:
        record = json.loads(raw)
    except ValueError:
        return None
    return record if isinstance(record, dict) and record.get('mechanism') else None


def off_record(reason='%s=off' % ENV) -> dict:
    return dict(mechanism='off', enforced=False, network='unrestricted', filesystem='unrestricted',
                reason=reason)


def none_record(reason) -> dict:
    return dict(mechanism='none', enforced=False, network='unrestricted', filesystem='unrestricted',
                reason=reason)


# ---------------------------------------------------------------- detection

def _true():
    return '/usr/bin/true' if os.path.exists('/usr/bin/true') else '/bin/true'


@functools.lru_cache(maxsize=None)
def _probe(mechanism):
    """(path of the wrapper, '') if the mechanism confines a trivial command, else (None, why)."""
    if mechanism == 'seatbelt':
        if sys.platform != 'darwin':
            return None, 'sandbox-exec is macOS only'
        path = shutil.which('sandbox-exec') or '/usr/bin/sandbox-exec'
        argv = [path, '-p', '(version 1)(allow default)(deny network*)', _true()]
    elif mechanism == 'bwrap':
        path = shutil.which('bwrap')
        if path is None:
            return None, 'bwrap is not on PATH'
        argv = [path, '--ro-bind', '/', '/', '--dev', '/dev', '--proc', '/proc', '--unshare-net',
                '--die-with-parent', '--', _true()]
    elif mechanism == 'unshare':
        path = shutil.which('unshare')
        if path is None or sys.platform != 'linux':
            return None, 'unshare is not on PATH' if sys.platform == 'linux' else 'unshare is Linux only'
        argv = [path, '-r', '-n', '-m', '--', _true()]
    else:
        return None, 'unknown mechanism ' + str(mechanism)
    try:
        proc = subprocess.run(argv, capture_output=True, text=True, timeout=PROBE_TIMEOUT)
    except (OSError, subprocess.TimeoutExpired) as exc:
        return None, '%s: %s' % (argv[0], exc)
    if proc.returncode:
        return None, '%s exited %d: %s' % (argv[0], proc.returncode, (proc.stderr or proc.stdout).strip()[-400:])
    return path, ''


def detect(environ=None):
    """(mechanism, wrapper path) for this host under the policy, or (None, message)."""
    wanted = policy(environ)
    if wanted == 'off':
        return None, ENV + '=off'
    if wanted in MECHANISMS:
        candidates = [wanted]
    elif sys.platform == 'darwin':
        candidates = ['seatbelt']
    elif sys.platform == 'linux':
        candidates = ['bwrap', 'unshare']
    else:
        candidates = []
    reasons = []
    for mechanism in candidates:
        path, why = _probe(mechanism)
        if path:
            return mechanism, path
        reasons.append('%s: %s' % (mechanism, why))
    hint = INSTALL.get(sys.platform, 'no sandbox mechanism is known for ' + sys.platform)
    return None, ('no sandbox mechanism works on this host (%s). %s. Set %s=off to run the code '
                  'under test unsandboxed; the opt-out is recorded in every artifact.'
                  % ('; '.join(reasons) or 'none probed', hint, ENV))


def report(environ=None) -> dict:
    """The record a process should write into its artifacts: the sandbox it runs inside,
    the opt-out, the mechanism its launches use, or the reason none is enforced."""
    inherited = active(environ)
    if inherited:
        return dict(inherited, inherited=True)
    if policy(environ) == 'off':
        return off_record()
    mechanism, detail = detect(environ)
    if mechanism is None:
        return none_record(detail)
    return dict(mechanism=mechanism, enforced=True, network='denied',
                filesystem=_filesystem_claim(mechanism, ['<work of each launch>'], []))


def _filesystem_claim(mechanism, writable, read_only):
    if mechanism in ('seatbelt', 'bwrap'):
        return dict(writable=list(writable), elsewhere='read-only')
    return dict(read_only=list(read_only), elsewhere='unrestricted (unshare limits the network only)')


# ---------------------------------------------------------------- the launch

def _quote(path):
    return '"' + path.replace('\\', '\\\\').replace('"', '\\"') + '"'


def seatbelt_profile(writable) -> str:
    rules = ['(version 1)', '(allow default)', '(deny network*)', '(deny file-write*)',
             '(allow file-write* (literal "/dev/null") (literal "/dev/zero") (literal "/dev/random")'
             ' (literal "/dev/urandom") (literal "/dev/dtracehelper") (literal "/dev/ptmx")'
             ' (regex #"^/dev/tty") (regex #"^/dev/pty") (regex #"^/dev/fd/"))']
    if writable:
        rules.append('(allow file-write* ' + ' '.join('(subpath %s)' % _quote(p) for p in writable) + ')')
    return '\n'.join(rules) + '\n'


def sandboxed(cmd, *, cwd=None, env=None, work, writable=(), read_only=()) -> Launch:
    """Wrap `cmd` so that it cannot reach the network or write outside `work`/`writable`.

    `work` is created if missing and receives the process's TMPDIR. `read_only` matters
    only to the `unshare` fallback, which cannot deny writes in general. Raises
    SandboxUnavailable when nothing can confine the command and `AUTOFORM_SANDBOX` is not
    `off`."""
    argv = [str(a) for a in cmd]
    base = dict(os.environ if env is None else env)
    work = os.path.realpath(str(work))
    os.makedirs(work, exist_ok=True)
    inherited = active(base)
    if inherited:
        return Launch(argv, cwd, base, dict(inherited, inherited=True))
    if policy(base) == 'off':
        return Launch(argv, cwd, base, off_record())
    mechanism, detail = detect(base)
    if mechanism is None:
        raise SandboxUnavailable(detail)
    wrapper = detail
    tmp = os.path.join(work, 'tmp')
    os.makedirs(tmp, exist_ok=True)
    writable_paths = []
    for p in [work, *writable]:
        p = os.path.realpath(str(p))
        if p not in writable_paths and os.path.isdir(p):
            writable_paths.append(p)
    read_only_paths = [os.path.realpath(str(p)) for p in read_only]
    child = dict(base, TMPDIR=tmp, TMP=tmp, TEMP=tmp)
    # pytest's hypothesis plugin keeps its example database under the cwd, which is the
    # subject's tree; point it at the work directory so a hypothesis-using suite still runs.
    child.setdefault('HYPOTHESIS_STORAGE_DIRECTORY', os.path.join(work, '.hypothesis'))
    record = dict(mechanism=mechanism, enforced=True, network='denied',
                  filesystem=_filesystem_claim(mechanism, writable_paths, read_only_paths),
                  tmpdir=tmp)
    if mechanism == 'seatbelt':
        wrapped = [wrapper, '-p', seatbelt_profile(writable_paths), *argv]
    elif mechanism == 'bwrap':
        wrapped = [wrapper, '--ro-bind', '/', '/', '--dev', '/dev', '--proc', '/proc', '--tmpfs', '/dev/shm']
        for p in writable_paths:
            wrapped += ['--bind', p, p]
        wrapped += ['--unshare-net', '--die-with-parent']
        if cwd is not None:
            wrapped += ['--chdir', os.path.abspath(str(cwd))]
        wrapped += ['--', *argv]
    else:   # unshare: network namespace, read-only binds of the named trees, exec in place
        script = 'set -e\n'
        for p in read_only_paths:
            script += 'mount --bind -o ro %s %s\n' % (_sh_quote(p), _sh_quote(p))
        script += 'exec "$@"\n'
        wrapped = [wrapper, '-r', '-n', '-m', '--kill-child', '--', '/bin/sh', '-c', script, 'sh', *argv]
    child[ACTIVE] = json.dumps(record)
    return Launch(wrapped, cwd, child, record)


def _sh_quote(s):
    return "'" + s.replace("'", "'\\''") + "'"


def require(environ=None):
    """Fail now, with the install message, if no launch could be confined."""
    if active(environ) or policy(environ) == 'off':
        return
    mechanism, detail = detect(environ)
    if mechanism is None:
        raise SandboxUnavailable(detail)


if __name__ == '__main__':
    print(json.dumps(report(), indent=1))
