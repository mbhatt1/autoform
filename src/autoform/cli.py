"""Installed entry points for the existing Joern and p-code pipelines."""
from __future__ import annotations

import argparse
import fcntl
import hashlib
from importlib import resources
import io
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
import zipfile

from . import __version__
from .repository import is_git_url, resolve_source


def runtime_payload():
    resource = resources.files("autoform").joinpath("runtime.zip")
    if resource.is_file():
        return resource.read_bytes()
    # Editable installs retain the same resource selection as wheel builds.
    root = Path(__file__).resolve().parents[2]
    if not (root / "build_support.py").is_file():
        raise ValueError("package is missing runtime.zip; reinstall autoform-lean")
    import importlib.util
    spec = importlib.util.spec_from_file_location("autoform_build_support", root / "build_support.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, content in sorted(module.runtime_files(root).items()):
            archive.writestr(name, content)
    return buffer.getvalue()


def _open_workspace_lock(path):
    # A user-supplied workspace must not make lock acquisition follow links or
    # block indefinitely while opening a FIFO. The stable inode is kept on disk.
    descriptor = os.open(path, os.O_CREAT | os.O_APPEND | os.O_WRONLY |
                         os.O_NOFOLLOW | os.O_NONBLOCK, 0o600)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ValueError(f'workspace lock is not a regular file: {path}')
        return os.fdopen(descriptor, 'a')
    except BaseException:
        os.close(descriptor)
        raise


def prepare_workspace(destination):
    """Initialize atomically, and refuse changes to existing proof inputs."""
    destination = Path(destination).resolve()
    with zipfile.ZipFile(io.BytesIO(runtime_payload())) as archive:
        entries = {}
        for info in archive.infolist():
            name = info.filename
            path = PurePosixPath(name)
            if (not name or path.is_absolute() or '..' in path.parts or
                    path.as_posix() != name or '\\' in name or info.is_dir() or
                    stat.S_IFMT(info.external_attr >> 16) not in (0, stat.S_IFREG) or
                    name == '.autoform-package.json' or name in entries):
                raise ValueError(f"invalid package resource: {name}")
            entries[name] = archive.read(info)
    if not entries:
        raise ValueError("package runtime archive is empty; reinstall autoform-lean")
    for name in entries:
        if any(parent.as_posix() in entries for parent in PurePosixPath(name).parents):
            raise ValueError(f"invalid package resource: conflicting parent of {name}")
    manifest = {name: hashlib.sha256(content).hexdigest() for name, content in entries.items()}

    def regular_resource(name):
        # Matching current bytes is insufficient if a packaged input points
        # outside the workspace or aliases another file via a symbolic link.
        path = destination
        try:
            for part in PurePosixPath(name).parts:
                path /= part
                if path.is_symlink():
                    return False
            return stat.S_ISREG(path.lstat().st_mode)
        except OSError:
            return False

    destination.parent.mkdir(parents=True, exist_ok=True)
    # Keep a stable lock inode outside the directory being installed. Removing a
    # lock file after unlock would allow racing callers to lock different inodes.
    lock_path = destination.with_name('.' + destination.name + '.autoform-init.lock')
    with _open_workspace_lock(lock_path) as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError('workspace initialization is already in progress') from exc
        marker = destination / ".autoform-package.json"
        if marker.exists() or marker.is_symlink():
            if not regular_resource(marker.name):
                raise ValueError(f"workspace manifest is not a regular file: {marker}")
            previous = json.loads(marker.read_text())
            if not isinstance(previous, dict) or previous.get("files") != manifest:
                raise ValueError(f"{destination} uses a different package; choose a new --workspace")
            for name, digest in manifest.items():
                path = destination / name
                if not regular_resource(name) or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                    raise ValueError(f"workspace resource changed: {path}; choose a new --workspace")
            return destination
        if destination.exists() and (not destination.is_dir() or any(destination.iterdir())):
            raise ValueError(f"workspace is not empty: {destination}; choose a new --workspace")
        # A failed extraction leaves the destination absent (or still empty), so
        # retrying does not require deleting a half-written proof project.
        with tempfile.TemporaryDirectory(prefix='.autoform-init-', dir=destination.parent) as tmp:
            staging = Path(tmp)
            for name, content in entries.items():
                path = staging / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
                if path.suffix == ".sh":
                    path.chmod(0o755)
            (staging / "Autoform/Generated").mkdir(parents=True, exist_ok=True)
            (staging / "Autoform/SpecsGen").mkdir(parents=True, exist_ok=True)
            (staging / '.autoform-package.json').write_text(
                json.dumps(dict(version=__version__, files=manifest), indent=2) + '\n')
            os.replace(staging, destination)
    return destination


def environment():
    env = dict(os.environ)
    env["AUTOFORM_PYTHON"] = sys.executable
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    return env


def _run_command(command, *, env, cleanup_timeout=10, timeout=None):
    """Keep the caller's run lock until cancellation cleanup has finished."""
    process, cancellation, deadline, forwarded = None, None, None, False

    def forward():
        nonlocal forwarded
        if process is not None and cancellation is not None and not forwarded:
            forwarded = True
            try:
                os.killpg(process.pid, cancellation)
            except ProcessLookupError:
                pass

    def cancel(signum, _frame):
        nonlocal cancellation, deadline
        # Repeated interrupts must not abort the child's restoration halfway through.
        if cancellation is None:
            cancellation, deadline = signum, time.monotonic() + cleanup_timeout
            forward()

    previous = {signum: signal.signal(signum, cancel) for signum in (signal.SIGINT, signal.SIGTERM)}
    # `autoform.sh` has no deadline of its own on joern-parse, the Joern script or
    # `lake build`, so without this an arbitrary large repository can hang the run
    # indefinitely with no way to bound it. Expiry takes the same path as a Ctrl-C.
    limit = None if timeout is None else time.monotonic() + timeout
    try:
        process = subprocess.Popen(command, env=env, start_new_session=True)
        forward()  # Cancellation may have arrived while starting the child.
        while True:
            try:
                code = process.wait(timeout=0.1)
                return 128 + cancellation if cancellation is not None else code
            except subprocess.TimeoutExpired:
                if limit is not None and cancellation is None and time.monotonic() >= limit:
                    print(f'autoform: run exceeded --timeout of {timeout:g}s; stopping',
                          file=sys.stderr)
                    cancel(signal.SIGTERM, None)
                if deadline is not None and time.monotonic() >= deadline:
                    return 128 + cancellation  # The finally block enforces the bound.
    finally:
        try:
            if process is not None:
                # Also release descendants that outlive their parent in this group.
                # Detached sessions are outside this cleanup boundary.
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
        finally:
            for signum, handler in previous.items():
                signal.signal(signum, handler)


_JOERN_JAR = re.compile(r'^io\.joern\.joern-cli-(.+)\.jar$')
# Required to get from a checkout/URL to a kernel-checked result. Everything else is
# needed only for a particular source language or for the machine-code frontend.
_REQUIRED = ('python', 'git', 'lake', 'lean', 'leanchecker', 'joern')

# Which source languages an OPTIONAL runtime gates. A missing entry here is a
# warning, never an error: translation and the kernel proofs still run, and only the
# differential oracle for these languages is unavailable -- which the report says by
# name, because "optional" on its own tells a first-time user nothing.
_DISABLES = {
    'java': ('Java', 'Kotlin'), 'javac': ('Java', 'Kotlin'),
    'go': ('Go',), 'node': ('JavaScript', 'TypeScript'),
    'cc': ('C',), 'clang': ('C++', 'assembling .s inputs for the machine frontend'),
    'kotlinc': ('Kotlin — Joern bundles a Kotlin compiler, so this is only for the native oracle',),
    'ld.lld': ('autoform regress --machine',),
    'pypcode': ('the machine-code frontend',), 'pyelftools': ('the machine-code frontend',),
    'macholib': ('the machine-code frontend',), 'pefile': ('the machine-code frontend',),
}


def _os_flavor():
    if sys.platform == 'darwin':
        return 'macos'
    if sys.platform.startswith('linux'):
        return 'linux'
    return 'other'


def install_hint(name, lean_toolchain=None, joern_pin=None):
    """One actionable line for a missing tool on this OS. Points at docs for the rest."""
    flavor = _os_flavor()
    mac, linux = flavor == 'macos', flavor == 'linux'
    lean_line = ("curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain "
                 + (lean_toolchain or '$(cat lean-toolchain)')
                 + "   # then: export PATH=$HOME/.elan/bin:$PATH")
    joern_v = joern_pin or '<pinned version in joern-version>'
    joern_line = (f"curl -L -o joern-cli.zip https://github.com/joernio/joern/releases/download/v{joern_v}/joern-cli.zip "
                  "&& mkdir -p ~/joern && unzip -q joern-cli.zip -d ~/joern   "
                  "# needs a JDK (temurin 21); see docs/running.md §1")
    jdk = ('brew install --cask temurin@21' if mac else
           'sudo apt-get install -y temurin-21-jdk  (or openjdk-21-jdk)' if linux else 'install a JDK 21')
    hints = {
        'git': 'brew install git' if mac else 'sudo apt-get install -y git' if linux else 'install git from https://git-scm.com',
        'lake': lean_line, 'lean': lean_line,
        'leanchecker': lean_line + '   # leanchecker ships with the toolchain (v4.28.0+)',
        'joern': joern_line, 'java': jdk, 'javac': jdk,
        'go': 'brew install go' if mac else 'sudo apt-get install -y golang-go' if linux else 'install Go from https://go.dev/dl',
        'node': 'brew install node@22' if mac else 'sudo apt-get install -y nodejs' if linux else 'install Node 22 from https://nodejs.org',
        'cc': 'xcode-select --install' if mac else 'sudo apt-get install -y build-essential' if linux else 'install a C compiler',
        'clang': 'xcode-select --install' if mac else 'sudo apt-get install -y clang' if linux else 'install clang',
        'kotlinc': 'brew install kotlin' if mac else 'sdk install kotlin  (SDKMAN) or your distribution package' if linux else 'install kotlinc',
        'ld.lld': 'brew install lld' if mac else 'sudo apt-get install -y lld' if linux else 'install LLVM lld',
        'python': 'install Python 3.10 or newer and reinstall autoform-lean into it',
    }
    if name in ('pypcode', 'pyelftools', 'macholib', 'pefile'):
        return "python -m pip install 'autoform-lean[machine]'"
    return hints.get(name, 'see docs/running.md §1')


def packaged_pin(name):
    """Read a pinned-version file (`lean-toolchain`, `joern-version`) from the package."""
    try:
        with zipfile.ZipFile(io.BytesIO(runtime_payload())) as archive:
            return archive.read(name).decode('utf-8', 'replace').strip()
    except (KeyError, ValueError, OSError, zipfile.BadZipFile):
        return None


def version_banner():
    """`autoform <version>` plus the two external pins every result depends on.

    A bug report that says "autoform 0.1.0" alone is not reproducible: the neutral AST
    is a function of the Joern build and every proof of the Lean toolchain, so both
    pins belong beside the package version wherever it is printed.
    """
    lean = packaged_pin('lean-toolchain') or 'lean-toolchain unavailable'
    joern = packaged_pin('joern-version') or 'joern-version unavailable'
    return f"autoform {__version__} (lean-toolchain {lean}, joern {joern})"


class _VersionAction(argparse.Action):
    def __init__(self, option_strings, dest, **kwargs):
        super().__init__(option_strings, dest, nargs=0, **kwargs)

    def __call__(self, parser, namespace, values, option_string=None):
        print(version_banner())
        parser.exit(0)


def tool_version(command, env):
    """First line of `<tool> --version`, or None if it cannot be run."""
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=60, env=env)
    except (OSError, subprocess.SubprocessError):
        return None
    output = (result.stdout or '') + (result.stderr or '')
    lines = [line for line in output.splitlines() if line.strip()]
    return lines[0].strip() if lines else None


def joern_report(env):
    """Locate Joern and read its version from its jar names, as provenance.py does."""
    home = Path(env.get('JOERN_HOME', str(Path.home() / 'joern')))
    lib = home / 'joern-cli' / 'lib'
    if not lib.is_dir() and (home / 'lib').is_dir():
        lib, home = home / 'lib', home.parent
    launcher = lib.parent / 'joern'
    if not lib.is_dir():
        return None, None, f'no Joern at {lib} (set JOERN_HOME; default ~/joern)'
    try:
        names = os.listdir(lib)
    except OSError as exc:
        return None, None, f'cannot read {lib}: {exc}'
    found = sorted({m.group(1) for m in (_JOERN_JAR.match(n) for n in names) if m})
    path = str(launcher) if launcher.is_file() else str(lib.parent)
    if not found:
        return path, None, f'{lib} has no io.joern.joern-cli-<version>.jar; incomplete distribution'
    if len(found) > 1:
        # Never guess: which jar wins is unpredictable, and the AST is a function of it.
        return path, None, f'{lib} contains several joern-cli versions ({", ".join(found)}); remove the stale one'
    return path, found[0], None


def doctor_report(env):
    """Everything `doctor` knows, as data. Printing and the exit code are separate.

    This used to print a name->path map and `return 0` unconditionally, so a machine
    with no Lean and no Joern passed its own health check. Every version this needs is
    already pinned in the repository (`lean-toolchain`, `joern-version`, the
    `[machine]` extras in pyproject), and the pins are load-bearing: the neutral AST is
    a function of the Joern build, so a silently different frontend changes artifacts
    for reasons unrelated to the source being analyzed.
    """
    toolchain = packaged_pin('lean-toolchain')
    joern_pin = packaged_pin('joern-version')
    lean_pin = toolchain.split(':v')[-1] if toolchain and ':v' in toolchain else None
    tools, problems, warnings = {}, [], []

    def record(name, path, found=None, expected=None, note=None, status=None):
        required = name in _REQUIRED
        if status is None:
            if path is None:
                status = 'missing'
            elif expected is not None and found is not None:
                status = 'ok' if found == expected else 'version-mismatch'
            elif found is None and expected is not None:
                status = 'unknown-version'
            else:
                status = 'ok'
        entry = dict(path=path, required=required, status=status)
        if found is not None:
            entry['found_version'] = found
        if expected is not None:
            entry['expected_version'] = expected
        if note:
            entry['note'] = note
        if status != 'ok':
            entry['hint'] = install_hint(name, toolchain, joern_pin)
            if not required:
                entry['disables'] = list(_DISABLES.get(name, ()))
            (problems if required else warnings).append(
                f'{name}: {status}' + (f' ({note})' if note else ''))
        tools[name] = entry
        return status

    version = '.'.join(str(part) for part in sys.version_info[:3])
    if sys.version_info >= (3, 10):
        record('python', sys.executable, found=version)
    else:
        record('python', sys.executable, found=version, expected='3.10+',
               note='autoform requires Python 3.10+', status='version-mismatch')

    for name in ('git', 'lake', 'lean', 'leanchecker'):
        path = shutil.which(name, path=env['PATH'])
        found = expected = None
        if path is not None and name in ('lean', 'lake'):
            banner = tool_version([path, '--version'], env)
            # `lean` prints "Lean (version 4.30.0-rc1, ...)" and `lake` prints
            # "Lake version 5.0.0-src+... (Lean version 4.30.0-rc1)". Accept both.
            match = re.search(r'Lean (?:\(version |version )([^,)]+)', banner or '')
            found, expected = (match.group(1) if match else None), lean_pin
        record(name, path, found=found, expected=expected,
               note=None if path else f'{name} is not on PATH')

    path, found, note = joern_report(env)
    record('joern', path, found=found, expected=joern_pin, note=note)

    # Optional: needed only to run the differential oracle for a given language.
    for name in ('java', 'javac', 'go', 'node', 'cc', 'clang', 'kotlinc'):
        found = shutil.which(name, path=env['PATH'])
        record(name, found, note=None if found else 'only needed for that source language')
    # Optional: `regress --machine` links each commit's objects with LLVM's ELF linker.
    lld = shutil.which('ld.lld', path=env['PATH']) or next(
        (p for p in ('/opt/homebrew/bin/ld.lld', '/usr/local/opt/lld/bin/ld.lld') if Path(p).is_file()), None)
    record('ld.lld', lld, note=None if lld else 'only needed for autoform regress --machine')

    # Optional: the machine-code frontend, pinned in pyproject's [machine] extra.
    for dist, pin in (('pypcode', '3.3.3'), ('pyelftools', '0.33'),
                      ('macholib', '1.16.4'), ('pefile', '2024.8.26')):
        try:
            from importlib import metadata
            installed = metadata.version(dist)
        except Exception:
            installed = None
        record(dist, sys.executable if installed else None, found=installed, expected=pin,
               note=None if installed else "install with: pip install 'autoform-lean[machine]'")

    return dict(schema_version=1, autoform=__version__, platform=sys.platform,
                pins=dict(lean_toolchain=toolchain, joern=joern_pin),
                tools=tools, problems=problems, warnings=warnings)


def doctor(env, strict=False, as_json=False):
    """Report tool availability AND version agreement, and fail when it matters.

    Exit 0: every required tool is present and matches its pin. Exit 1: a required
    tool is missing or mismatched -- or, with --strict, an optional one is. Exit 2 is
    returned by the caller when the check itself could not run (unreadable package).
    A missing OPTIONAL runtime is a warning: it disables one language's differential
    oracle, which the report names, and nothing else.
    """
    report = doctor_report(env)
    problems, warnings = report['problems'], report['warnings']
    code = 1 if problems or (strict and warnings) else 0
    report['exit_code'] = code
    if as_json:
        print(json.dumps(report, indent=2))
    else:
        tools = report['tools']
        required_ok = sum(1 for t in tools.values() if t['required'] and t['status'] == 'ok')
        print(f"autoform doctor: {required_ok}/{len(_REQUIRED)} required ok, "
              f"{len(problems)} problem(s), {len(warnings)} optional warning(s)  "
              f"[{report['platform']}, autoform {__version__}]")
        pins = report['pins']
        print(f"  pins: lean-toolchain={pins['lean_toolchain'] or '?'}  joern={pins['joern'] or '?'}")
        for name, entry in tools.items():
            status = entry['status']
            if status == 'ok':
                mark = 'ok      '
            elif status == 'version-mismatch':
                mark = 'MISMATCH' if entry['required'] else 'mismatch'
            elif status == 'unknown-version':
                mark = 'UNKNOWN ' if entry['required'] else 'unknown '
            else:
                mark = 'MISSING ' if entry['required'] else 'missing '
            detail = entry.get('found_version') or entry.get('path') or ''
            expected = entry.get('expected_version')
            if expected and entry.get('found_version') != expected:
                detail += f"  (pin {expected})"
            print(f"  {mark} {name:<12s} {detail}")
            if status != 'ok':
                kind = 'required' if entry['required'] else 'optional'
                extra = kind
                if entry.get('disables'):
                    extra += '; disables: ' + '; '.join(entry['disables'])
                print(f"             {extra}")
                if entry.get('note'):
                    print(f"             {entry['note']}")
                print(f"             install: {entry['hint']}")
        print("  exit codes: 0 all required present and pinned; 1 a required tool is missing or "
              "mismatched (with --strict, also an optional one); 2 the check itself could not run.")
    if problems:
        print('\nautoform doctor: ' + str(len(problems)) + ' required check(s) failed:',
              file=sys.stderr)
        for line in problems:
            print('  - ' + line, file=sys.stderr)
    elif warnings and strict:
        print('\nautoform doctor: ' + str(len(warnings)) + ' optional check(s) failed (--strict):',
              file=sys.stderr)
        for line in warnings:
            print('  - ' + line, file=sys.stderr)
    return code


def discard_checkout(repository, keep=False):
    """Delete a clone this run created, unless the caller asked to keep it.

    Every Git-URL run used to `mkdtemp` a fresh full checkout under
    `<workspace>/sources/` and nothing ever removed it, so re-running against the
    same URL accumulated a complete copy of the repository each time. Only clones
    *this* process made are removed: a local source directory was never ours to
    delete, and `kind` distinguishes the two. The evidence stays reproducible
    because `repository.json` records the exact commit, which identifies the tree
    far better than a temporary path does.
    """
    if keep or not isinstance(repository, dict) or repository.get('kind') != 'git':
        return
    checkout = repository.get('checkout')
    if not checkout:
        return
    # `checkout` is `<workspace>/sources/<Module>-XXXXXXXX/checkout`; the mkdtemp
    # directory is its parent and is what needs to go.
    shutil.rmtree(Path(checkout).parent, ignore_errors=True)


def _discard_previous_report(report, module):
    for name in ('run.json', 'summary.md', 'guarantee.json', 'guarantee.md',
                 'pipeline.json', 'conformance.json', 'specs.json', 'audit.json',
                 'core-oracle.json', 'mutation.json', 'ledger.json', 'frontend.json',
                 'context.json', 'native-build.json', 'formalization-graph.json',
                 'assurance.md', f'ast-{module}.json', f'ledger-{module}.json',
                 'properties.json', 'security-claims.json', 'security-mutation.json',
                 'security-audit.json', 'security.json', 'security.md',
                 'inventory.json', 'inventory-after.json', 'source-coverage.json', 'selection.json',
                 'repository-summary.json', 'repository.json', 'checkout.log',
                 f'sacm-{module}.json', f'contracts-{module}.json'):
        (report / name).unlink(missing_ok=True)


def _regress(args, workspace, report, env):
    """Run `autoform.sh` at two commits of one repository and compare the proofs.

    Each run writes the ordinary report under `artifacts/pipeline/<Module>/`; it is
    copied to `artifacts/regression/<Module>/{base,head}/` before the next run
    overwrites it, and `scripts/regression.py compare` diffs the two copies. The
    comparison is by recorded facts (holes, theorems, runtime cases), never by
    source text, so the same module name is used for both commits on purpose:
    theorem identifiers are per function and must line up across the runs.
    """
    source = args.source
    if not is_git_url(source):
        local = Path(source)
        if local.is_dir() and (local / '.git').exists():
            source = local.resolve().as_uri()
        else:
            raise ValueError('regress compares two commits, so the source must be a Git URL '
                             'or a local checkout with a .git directory')
    out = workspace / 'artifacts/regression' / args.module
    out.mkdir(parents=True, exist_ok=True)
    if args.machine:
        return _regress_machine(args, workspace, source, out, env)
    runs = {}
    for label, ref in (('base', args.base), ('head', args.head)):
        _discard_previous_report(report, args.module)
        print(f'==> {label}: {ref or "HEAD"}', flush=True)
        repository = None
        try:
            checkout, repository = resolve_source(source, workspace, args.module,
                                                  ref=ref, subdir=args.subdir)
            code = _run_command(['bash', str(workspace / 'autoform.sh'), str(checkout), args.module],
                                env=env, timeout=args.timeout)
        finally:
            discard_checkout(repository, keep=args.keep_checkout)
        copy = out / label
        shutil.rmtree(copy, ignore_errors=True)
        shutil.copytree(report, copy, ignore=shutil.ignore_patterns('.run.lock'))
        runs[label] = dict(ref=ref, commit=(repository or {}).get('commit'), exit_code=code)
        if code >= 128:
            return code  # interrupted or timed out: nothing to compare yet
    (out / 'runs.json').write_text(json.dumps(runs, indent=2) + '\n')
    result = subprocess.run([sys.executable, str(workspace / 'scripts/regression.py'), 'compare',
                             str(out / 'base'), str(out / 'head'), '--module', args.module,
                             '--out', str(out / 'regression.json'),
                             '--markdown', str(out / 'regression.md')], env=env)
    if result.returncode == 2:
        # A run that never reached translation leaves nothing to compare; say which.
        for label in ('base', 'head'):
            if runs[label]['exit_code'] != 0:
                print(f"autoform: the {label} run ({runs[label]['ref'] or 'HEAD'}) exited "
                      f"{runs[label]['exit_code']}; see {out / label / 'pipeline.json'}", file=sys.stderr)
        return 1
    print(f'regression report: {out / "regression.md"}')
    return result.returncode


def _regress_machine(args, workspace, source, out, env):
    """Check out both commits, then let `scripts/machine_regress.py` compare them."""
    trees, records = {}, {}
    try:
        for label, ref in (('base', args.base), ('head', args.head)):
            print(f'==> {label}: {ref or "HEAD"}', flush=True)
            tree, record = resolve_source(source, workspace, args.module, ref=ref, subdir=args.subdir)
            trees[label], records[label] = tree, record
        command = [sys.executable, str(workspace / 'scripts/machine_regress.py'),
                   str(trees['base']), str(trees['head']), '--target', args.target,
                   '--out', str(out / 'machine'),
                   '--base-label', records['base'].get('commit') or str(args.base),
                   '--head-label', records['head'].get('commit') or str(args.head or 'HEAD')]
        command += [arg for name in args.files for arg in ('--file', name)]
        command += [arg for name in args.functions for arg in ('--function', name)]
        code = _run_command(command, env=env, timeout=args.timeout)
        (out / 'runs.json').write_text(json.dumps(
            {label: dict(ref=getattr(args, label), commit=records[label].get('commit'))
             for label in records}, indent=2) + '\n')
        if code in (0, 1):
            print(f'regression report: {out / "machine" / "regression.md"}')
        return code
    finally:
        for record in records.values():
            discard_checkout(record, keep=args.keep_checkout)


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Formalize source or machine code and check it with Lean.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=("A Git URL alone runs the full workflow: "
                "autoform https://host/owner/repo.git [Module] [--ref REF] [--subdir PATH]\n"
                "Two commits of one repository are compared by what can be proven about each: "
                "autoform regress <repo> [Module] --base REF [--head REF]\n\n"
                "exit codes (docs/running.md §7):\n"
                "  0      completed; for `assure`, every required check passed; for `regress`,\n"
                "         nothing that held at --base is lost at --head\n"
                "  1      a stage failed, `assure` finished with unresolved verification gaps, or\n"
                "         `regress` found a regression or a proven behavior change\n"
                "  2      invocation, setup or orchestration failure: bad module name, missing\n"
                "         Joern, busy workspace, unreadable package, or a refused dirty tree\n"
                "  128+N  interrupted by signal N; `--timeout` expiry is 143 (SIGTERM)\n"
                "Start with `autoform doctor`: it names every missing prerequisite and how to install it."))
    parser.add_argument("--version", action=_VersionAction,
                        help="print the package version with the pinned Lean and Joern versions")
    parser.add_argument("--workspace", type=Path, default=Path(".autoform-work"),
                        help="writable Lean project and evidence directory (default: .autoform-work)")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("init", help="extract the bundled Lean project and tools")
    health = sub.add_parser("doctor",
                            help="check external tools and their versions against this package's pins")
    health.add_argument("--strict", action="store_true",
                        help="also fail when an optional tool or [machine] extra is unavailable")
    health.add_argument("--json", action="store_true",
                        help="machine-readable report on stdout (schema_version 1) instead of the summary")
    for name in ("source", "assure"):
        command = sub.add_parser(name, help="translate and prove native observations" if name == "source" else "run the full assurance pipeline")
        command.add_argument("source", help="source directory or Git URL")
        command.add_argument("module", nargs="?", default="Translated")
        command.add_argument("--ref", help="Git branch, tag or commit to check out")
        command.add_argument("--subdir", help="directory inside the source checkout to analyze")
        command.add_argument("--keep-checkout", action="store_true",
                             help="keep the cloned source tree under <workspace>/sources "
                                  "after the run instead of deleting it")
        if name == "source":
            command.add_argument("--timeout", type=float,
                                 help="overall wall-clock limit in seconds for the whole run "
                                      "(default: no limit). `source` runs autoform.sh, which "
                                      "has no per-stage deadline of its own.")
        if name == "assure":
            command.add_argument("--stage-timeout", type=float, default=7200,
                                 help="maximum seconds for each assurance stage (default: 7200)")
            command.add_argument("--properties", type=Path,
                                 help="independent Lean security properties (default: autoform.properties.json in selected source directory)")
    regress = sub.add_parser("regress",
                             help="run the pipeline at two commits and report what could be proven "
                                  "at --base but not at --head")
    regress.add_argument("source", help="Git URL, or a local checkout with a .git directory")
    regress.add_argument("module", nargs="?", default="Translated")
    regress.add_argument("--base", required=True, help="the earlier branch, tag or commit")
    regress.add_argument("--head", help="the later branch, tag or commit (default: the repository's HEAD)")
    regress.add_argument("--subdir", help="directory inside the checkout to analyze at both commits")
    regress.add_argument("--timeout", type=float,
                         help="wall-clock limit in seconds for EACH of the two pipeline runs")
    regress.add_argument("--keep-checkout", action="store_true",
                         help="keep both cloned trees under <workspace>/sources after the run")
    regress.add_argument("--machine", action="store_true",
                         help="compare compiled machine code instead of running the source pipeline: "
                              "search for inputs where the two commits' functions return different "
                              "values and kernel-check each on the SLEIGH-lifted code")
    regress.add_argument("--files", nargs="+", default=[],
                         help="with --machine: source files (relative to --subdir) compiled at both commits")
    regress.add_argument("--functions", nargs="+", default=[],
                         help="with --machine: functions to compare (default: those whose code changed)")
    regress.add_argument("--target", choices=("aarch64", "x86_64", "i386"), default="aarch64",
                         help="with --machine: the Linux target to compile for (default: aarch64)")
    sub.add_parser("formalize", add_help=False,
                   help="infer candidate claims, rank them with a SemIf judge, verify in Lean (formalize --help)")
    machine = sub.add_parser("machine", add_help=False, help="binary/assembly frontend (machine --help for options)")
    machine.add_argument("args", nargs=argparse.REMAINDER)
    # Let the machine frontend own its flags, including --help and --list-languages.
    values = list(sys.argv[1:] if argv is None else argv)
    if values[:1] == ['formalize']:
        # The claim/judge/verify harness owns its own flags (autoform/harness/cli.py).
        from .harness.cli import main as formalize
        return formalize(values[1:])
    # A URL alone is the full assurance workflow; explicit subcommands still work.
    index = 0
    while index < len(values):
        if values[index] == '--workspace':
            index += 2
        elif values[index].startswith('--workspace='):
            index += 1
        else:
            if is_git_url(values[index]):
                values.insert(index, 'assure')
            break
    args, unknown = parser.parse_known_args(values)
    if args.command == "machine":
        args.args = unknown + args.args
    elif unknown:
        parser.error("unrecognized arguments: " + " ".join(unknown))
    if args.command == 'regress' and args.machine and not args.files:
        parser.error('--machine needs --files: the source files to compile at both commits')
    if args.command == 'regress' and not args.machine and (args.files or args.functions):
        parser.error('--files and --functions apply only with --machine')
    if args.command == 'assure' and (not math.isfinite(args.stage_timeout) or args.stage_timeout <= 0):
        parser.error('--stage-timeout must be a finite positive number')
    if args.command in ('source', 'regress') and args.timeout is not None and (
            not math.isfinite(args.timeout) or args.timeout <= 0):
        parser.error('--timeout must be a finite positive number')
    env = environment()
    if args.command == "doctor":
        try:
            return doctor(env, strict=args.strict, as_json=args.json)
        except (ValueError, OSError, RuntimeError, zipfile.BadZipFile) as exc:
            print(f"autoform: {exc}", file=sys.stderr)
            return 2
    run_lock = workspace_lock = repository = None
    try:
        workspace = prepare_workspace(args.workspace)
        if args.command == "init":
            print(workspace)
            return 0
        workspace_lock = _open_workspace_lock(workspace / '.autoform-run.lock')
        try:
            fcntl.flock(workspace_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError('a run in this workspace is already in progress; use a separate --workspace') from None
        if args.command == "machine":
            # Preserve the caller's cwd so relative input and --out paths keep their meaning.
            command = [sys.executable, str(workspace / "scripts/formalize_machine.py"), *args.args]
        else:
            if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', args.module):
                raise ValueError('module must be a Lean identifier beginning with an uppercase letter')
            manifest = json.loads((workspace / ".autoform-package.json").read_text())
            target = f"Autoform/Generated/{args.module}.lean"
            if target in manifest["files"]:
                raise ValueError(f"module {args.module} is bundled with the library; choose another module name")
            report = workspace / 'artifacts/pipeline' / args.module
            report.mkdir(parents=True, exist_ok=True)
            run_lock = _open_workspace_lock(report / '.run.lock')
            try:
                fcntl.flock(run_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise ValueError('a run for this workspace and module is already in progress') from exc
            if args.command == 'regress':
                return _regress(args, workspace, report, env)
            property_input, property_error, property_path = None, None, None
            if args.command == 'assure' and args.properties is not None:
                try:
                    if not args.properties.is_file():
                        raise ValueError('security property input must be a readable regular file')
                    property_input = args.properties.read_bytes()
                except (OSError, RuntimeError, ValueError) as exc:
                    property_error = str(exc)
            # Acquisition can fail before the pipeline starts. Never leave a prior
            # proof verdict at the output path for this new invocation.
            _discard_previous_report(report, args.module)
            if property_error:
                (report / 'run.json').write_text(json.dumps(dict(module=args.module,
                    execution_status='property_input_failed', verification_complete=False,
                    security_requested=True, error=property_error), indent=2) + '\n')
                (report / 'guarantee.json').write_text(json.dumps(dict(status='unverified',
                    whole_program_correctness=False, claims=[], reason='Security property input unavailable.'),
                    indent=2) + '\n')
                raise ValueError('security property input: ' + property_error)
            if property_input is not None:
                property_path = workspace / '.autoform-inputs' / (args.module + '.properties.json')
                property_path.parent.mkdir(parents=True, exist_ok=True)
                property_path.write_bytes(property_input)
            try:
                source, repository = resolve_source(args.source, workspace, args.module,
                                                    ref=args.ref, subdir=args.subdir)
            except ValueError as exc:
                failure = dict(module=args.module, execution_status='acquisition_failed',
                               verification_complete=False, error=str(exc),
                               stages={'checkout': {'status': 'failed', 'reason': str(exc)}})
                (report / 'run.json').write_text(json.dumps(failure, indent=2) + '\n')
                (report / 'guarantee.json').write_text(json.dumps(dict(
                    status='unverified', whole_program_correctness=False,
                    claims=[], reason='Source acquisition failed.'), indent=2) + '\n')
                (report / 'summary.md').write_text('# Source acquisition failed\n\n' + str(exc) +
                                                 '\n\nNo proof or guarantee was produced for this invocation.\n')
                raise
            env['AUTOFORM_REPOSITORY_REPORT'] = str(report / 'repository.json')
            script = "assure.sh" if args.command == "assure" else "autoform.sh"
            command = ["bash", str(workspace / script), str(source), args.module]
            if args.command == "assure" and args.properties is not None:
                command += ['--properties', str(property_path)]
            if args.command == "assure":
                command += ['--stage-timeout', str(args.stage_timeout)]
        try:
            return _run_command(command, env=env, timeout=getattr(args, 'timeout', None))
        finally:
            discard_checkout(repository, keep=getattr(args, 'keep_checkout', False))
    except (ValueError, OSError, RuntimeError, zipfile.BadZipFile) as exc:
        print(f"autoform: {exc}", file=sys.stderr)
        return 2
    finally:
        if run_lock:
            run_lock.close()
        if workspace_lock:
            workspace_lock.close()
