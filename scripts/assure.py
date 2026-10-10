"""Collect scoped assurance evidence, including a final report on failed runs."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import math
import os
import re
import signal
import stat
import subprocess
import sys
import time

import guarantee
import deep_json
import security_specs

ROOT = Path(__file__).resolve().parents[1]


class SignalInterrupt(KeyboardInterrupt):
    """Route termination through the same cleanup path as keyboard cancellation."""

    def __init__(self, signum):
        self.signum = signum
        super().__init__(signal.Signals(signum).name)


def interrupt_exit_code(exc):
    return 128 + getattr(exc, 'signum', signal.SIGINT)


def read(path):
    try:
        data = deep_json.load(path)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def write(path, data):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


class Assurance:
    def __init__(self, source, module, root=ROOT, properties=None, stage_timeout=7200,
                 language=None, inventory=None, inventory_exclude=(), route_properties=False,
                 frozen_properties=None):
        try:
            timeout = float(stage_timeout)
        except (TypeError, ValueError, OverflowError):
            raise ValueError('stage timeout must be a finite positive number') from None
        if isinstance(stage_timeout, bool) or not math.isfinite(timeout) or timeout <= 0:
            raise ValueError('stage timeout must be a finite positive number')
        self.stage_timeout = timeout
        self.root, self.source, self.module = Path(root), Path(source).resolve(), module
        self.report = self.root / 'artifacts/pipeline' / module
        self.report.mkdir(parents=True, exist_ok=True)
        self.env = dict(os.environ, AUTOFORM_PYTHON=sys.executable, PYTHONUNBUFFERED='1')
        self.env['PATH'] = str(Path.home() / '.elan/bin') + ':' + self.env.get('PATH', '')
        self.stages = {}
        self.explicit_properties = Path(properties).absolute() if properties is not None else None
        self.properties = self.explicit_properties
        self.property_selection = dict(mode='explicit' if properties is not None else 'none')
        self.language, self.inventory = language, inventory
        self.inventory_exclude = tuple(inventory_exclude)
        self.route_properties = route_properties
        self.frozen_properties = frozen_properties
        if language is not None:
            import repository_inventory
            self.env.update(AUTOFORM_LANGUAGE=language,
                            AUTOFORM_FRONTEND=repository_inventory.ADAPTERS[language]['frontend'],
                            PYTHONDONTWRITEBYTECODE='1')

    def snapshot_properties(self):
        """Freeze requirements before executing source, within the selected scope."""
        self.properties = self.explicit_properties
        self.property_selection = dict(mode='explicit' if self.properties is not None else 'none')
        if self.frozen_properties is not None:
            self.property_selection = dict(mode='repository_partition', path=str(self.properties),
                sha256=hashlib.sha256(self.frozen_properties).hexdigest())
            return self.frozen_properties, None
        if self.properties is None:
            candidate = self.source / 'autoform.properties.json'
            try:
                candidate.lstat()
            except FileNotFoundError:
                return None, None
            except OSError:
                # An inaccessible candidate cannot silently disable security checks.
                pass
            self.properties = candidate
            self.property_selection['mode'] = 'repository'
        self.property_selection['path'] = str(self.properties)
        try:
            resolved = self.properties.resolve(strict=True)
            if self.explicit_properties is None and not resolved.is_relative_to(self.source):
                raise ValueError('automatic property manifest escapes the selected source directory')
            # A FIFO or device must not hang the assurance driver while reading input.
            descriptor = os.open(resolved, os.O_RDONLY | os.O_NONBLOCK)
            with os.fdopen(descriptor, 'rb') as stream:
                if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                    raise ValueError('security property input must be a regular file')
                content = stream.read()
            self.property_selection['sha256'] = hashlib.sha256(content).hexdigest()
            return content, None
        except (OSError, RuntimeError, ValueError) as exc:
            self.property_selection['error'] = str(exc)
            return None, str(exc)

    def checkpoint(self, status='running'):
        data = dict(module=self.module, source=str(self.source), execution_status=status,
                    security_requested=self.properties is not None,
                    stage_timeout_seconds=self.stage_timeout,
                    property_selection=self.property_selection,
                    stages=self.stages, updated_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
        write(self.report / 'run.json', data)
        return data

    def run(self, name, command, accepted=(0,)):
        print('==> ' + name, flush=True)
        log = self.report / (name + '.log')
        self.stages[name] = dict(status='running', command=list(map(str, command)), log=log.name,
                                 timeout_seconds=self.stage_timeout)
        self.checkpoint()
        start = time.monotonic()
        timed_out, interrupted = False, None
        try:
            with log.open('w') as stream:
                process = subprocess.Popen(command, cwd=self.root, env=self.env,
                                           stdout=stream, stderr=subprocess.STDOUT,
                                           start_new_session=True)
                try:
                    code, error = process.wait(timeout=self.stage_timeout), None
                except subprocess.TimeoutExpired:
                    timed_out = True
                    code, error = 124, f'stage exceeded its {self.stage_timeout:g}-second deadline'
                except KeyboardInterrupt as exc:
                    interrupted = exc
                    code, error = interrupt_exit_code(exc), 'stage interrupted'
                finally:
                    if (timed_out or interrupted) and process.poll() is None:
                        # Let our mutation/proof drivers restore source and terminate
                        # their own child sessions before forcing this group to exit.
                        try:
                            os.killpg(process.pid, signal.SIGINT)
                        except (ProcessLookupError, PermissionError):
                            pass
                        try:
                            process.wait(timeout=2)
                        except subprocess.TimeoutExpired:
                            pass
                    # Also clean up descendants after a successful parent exits. This
                    # covers this process group, not processes escaping into new sessions.
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except (ProcessLookupError, PermissionError):
                        pass
                    process.wait()
        except OSError as exc:
            code, error = 127, str(exc)
        status = ('timed_out' if timed_out else 'interrupted' if interrupted else
                  'completed' if code in accepted else 'failed')
        self.stages[name].update(status=status, timed_out=timed_out,
                                 exit_code=code, seconds=round(time.monotonic() - start, 2))
        if error:
            self.stages[name]['error'] = error
            with log.open('a') as stream:
                stream.write('\n' + error + '\n')
        self.checkpoint()
        print('    exit %s; %s' % (code, log), flush=True)
        if interrupted is not None:
            raise interrupted
        return code

    def blocked(self, name, reason):
        self.stages[name] = dict(status='blocked', reason=reason)
        self.checkpoint()

    def clear_outputs(self):
        # Never consume yesterday's evidence if today's source or setup fails.
        for name in ('run.json', 'summary.md', 'pipeline.json', 'conformance.json', 'specs.json',
                     'guarantee.json', 'guarantee.md',
                     'ledger.json', 'audit.json', 'core-oracle.json', 'mutation.json', 'context.json',
                     'frontend.json', 'native-build.json', 'formalization-graph.json', 'assurance.md',
                     'sacm-' + self.module + '.json', 'contracts-' + self.module + '.json',
                     'ast-' + self.module + '.json', 'ledger-' + self.module + '.json',
                     'inventory.json', 'inventory-after.json', 'source-coverage.json', 'selection.json',
                     'repository-summary.json',
                     *security_specs.OUTPUTS):
            (self.report / name).unlink(missing_ok=True)

    def execute(self):
        property_input, property_error = self.snapshot_properties()
        self.clear_outputs()
        if self.inventory is not None:
            write(self.report / 'inventory.json', self.inventory)
        self.checkpoint()
        if property_error:
            for stage in ('source', 'security-properties', 'security-mutation',
                          'security-restore', 'security-audit'):
                self.blocked(stage, 'Security property input unavailable: ' + property_error)
            return self.finish()
        code = self.run('source', ['bash', str(self.root / 'autoform.sh'), str(self.source), self.module])
        pipeline = read(self.report / 'pipeline.json')
        conf, specs = read(self.report / 'conformance.json'), read(self.report / 'specs.json')
        fresh_model = pipeline.get('stage') in ('runtime', 'ledger', 'proofs', 'complete')
        if self.route_properties and self.properties is not None and fresh_model:
            from repository_assurance import property_request
            try:
                request = property_request(property_input)
                functions = deep_json.load(self.report / ('ast-' + self.module + '.json'))
                names = {f.get('name') for f in functions if isinstance(f, dict)}
                selected = [c for c in request['claims'] if c['subject'] in names]
                self.property_selection['routed_claim_ids'] = [c['id'] for c in selected]
                self.property_selection['original_sha256'] = self.property_selection.get('sha256')
                if selected:
                    property_input = (json.dumps(dict(schema_version=1, claims=selected), indent=2) + '\n').encode()
                    self.property_selection['sha256'] = hashlib.sha256(property_input).hexdigest()
                else:
                    self.properties = None
            except (OSError, ValueError, TypeError) as exc:
                property_error = str(exc)
        if fresh_model and conf.get('total', 0) and not conf.get('divergences'):
            self.run('core-oracle', [sys.executable, 'scripts/core_oracle.py',
                'ast-' + self.module + '.json', self.module, str(self.source),
                '--conformance', str(self.report / 'conformance.json'), '--inputs', '0',
                '--scratch', str(self.report), '--out', str(self.report / 'core-oracle.json')])
        else:
            self.blocked('core-oracle', 'No fresh, agreeing native observations.')
        proofs_ready = code == 0 and specs.get('build_clean') and specs.get('proved', 0) > 0
        build = None
        if proofs_ready:
            limit = os.environ.get('AUTOFORM_MUTANTS', str(max(8, 2 * specs['proved'])))
            self.run('mutation', [sys.executable, 'scripts/mutate.py',
                'Autoform/Generated/' + self.module + '.lean', 'Autoform.Generated.' + self.module,
                '--spec-file', 'Autoform/SpecsGen/' + self.module + '.lean',
                '--spec-module', 'Autoform.SpecsGen.' + self.module,
                '--spec-report', str(self.report / 'specs.json'), '--max-mutants', limit,
                '--json', str(self.report / 'mutation.json')])
            build = self.run('restore-build', ['lake', 'build', 'Autoform.SpecsGen.' + self.module,
                                              'Autoform.Contracts'])
            if build != 0:
                self.blocked('audit', 'Restored proof module failed to rebuild.')
        else:
            self.blocked('mutation', 'No freshly built native-observation proof module.')
            self.blocked('audit', 'No freshly built native-observation proof module.')
        if self.properties is not None:
            if property_error:
                for stage in ('security-properties', 'security-mutation', 'security-restore', 'security-audit'):
                    self.blocked(stage, 'Security property routing failed: ' + property_error)
            elif not fresh_model:
                for stage in ('security-properties', 'security-mutation', 'security-restore', 'security-audit'):
                    self.blocked(stage, 'No fresh source model for independent properties.')
            else:
                (self.report / 'properties.json').write_bytes(property_input)
                self.check_security(proofs_ready)
        # Replay only after both mutation stages have restored the original model.
        if build == 0:
            self.run('audit', [sys.executable, 'scripts/audit_all.py', '--strict',
                '--module', 'Autoform.SpecsGen.' + self.module, '--output', str(self.report / 'audit.json'),
                *[arg for name in ('specs.json', 'conformance.json', 'mutation.json',
                                   'core-oracle.json', 'context.json', 'ast-' + self.module + '.json')
                  for arg in ('--evidence', str(self.report / name))], *self.scope_evidence()])
        self.run('contracts', [sys.executable, 'scripts/emit_contracts.py', self.module,
                              '--out', str(self.report / ('contracts-' + self.module + '.json'))])
        self.run('assurance', [sys.executable, 'scripts/sacm.py', '--module', self.module,
                 '--root', str(self.report), '--markdown', str(self.report / 'assurance.md'), '--quiet'],
                 accepted=(0, 1))
        return self.finish()

    def scope_evidence(self):
        return [arg for name in ('inventory.json', 'selection.json')
                if (self.report / name).is_file()
                for arg in ('--evidence', str(self.report / name))]

    def check_security(self, conformance_ready):
        self.run('security-properties', [sys.executable, 'scripts/security_specs.py',
            str(self.source), self.module, str(self.report / 'properties.json')])
        specs = read(self.report / 'security-claims.json')
        claims = [c for c in specs.get('claims', []) if c.get('proved')]
        if not claims:
            for stage in ('security-mutation', 'security-restore', 'security-audit'):
                self.blocked(stage, 'No proved independent properties; see open obligations.')
            return
        proof_module = 'Autoform.Security.' + self.module
        self.run('security-mutation', [sys.executable, 'scripts/mutate.py',
            'Autoform/Generated/' + self.module + '.lean', 'Autoform.Generated.' + self.module,
            '--spec-file', 'Autoform/Security/' + self.module + '.lean', '--spec-module', proof_module,
            '--theorems', ','.join('property_' + c['id'] for c in claims),
            '--decls', ','.join(sorted({c['definition'] for c in claims})),
            '--subject', ';'.join('property_' + c['id'] + '=' + c['definition'] for c in claims),
            '--max-mutants', os.environ.get('AUTOFORM_MUTANTS', str(max(8, 2 * len(claims)))),
            '--json', str(self.report / 'security-mutation.json')])
        modules = [proof_module] + (['Autoform.SpecsGen.' + self.module] if conformance_ready else [])
        if self.run('security-restore', ['lake', 'build', *modules]) != 0:
            self.blocked('security-audit', 'Security proof module failed to rebuild after mutation.')
            return
        self.run('security-audit', [sys.executable, 'scripts/audit_all.py', '--strict',
            '--module', proof_module, '--output', str(self.report / 'security-audit.json'),
            *[arg for name in ('properties.json', 'security-claims.json', 'security-mutation.json',
                               'context.json', 'ast-' + self.module + '.json')
              for arg in ('--evidence', str(self.report / name))], *self.scope_evidence()])

    def finish(self):
        scope = None
        if self.inventory is not None:
            import repository_inventory
            import repository_scope
            after = repository_inventory.discover(self.source, exclude=self.inventory_exclude)
            write(self.report / 'inventory-after.json', after)
            scope = repository_scope.coverage(self.inventory, after,
                self.report / ('ast-' + self.module + '.json'), read(self.report / 'frontend.json'), self.language)
            write(self.report / 'source-coverage.json', scope)
        conf, ledger = read(self.report / 'conformance.json'), read(self.report / 'ledger.json')
        specs = read(self.report / 'specs.json')
        issues = [name for name, item in self.stages.items()
                  if item['status'] != 'completed' or (name == 'assurance' and item.get('exit_code'))]
        if scope is not None:
            issues.append('repository-coverage')
        data = self.checkpoint('completed_with_gaps' if issues else 'completed')
        data.update(verification_complete=not issues, issues=issues,
                    comparisons=conf.get('total', 0), divergences=conf.get('divergences', 0),
                    proofs=specs.get('proved', 0), open_obligations=specs.get('open_obligations'),
                    holes=ledger.get('holes'), source_pipeline=read(self.report / 'pipeline.json'),
                    context=read(self.report / 'context.json'))
        security_claims = read(self.report / 'security-claims.json') if self.properties is not None else {}

        def counts(report):
            return {key: value if type(value) is int and value >= 0 else None
                    for key, value in (('proofs', report.get('proved')),
                                       ('open_obligations', report.get('open_obligations')))}

        # Retain the legacy counters' conformance scope. Independent requested
        # properties must remain visible even when no property report was produced.
        data['proof_counts_scope'] = 'conformance'
        data['proof_summary'] = dict(conformance=counts(specs),
                                     security=dict(requested=self.properties is not None,
                                                   **counts(security_claims)))
        repository = None
        acquisition = self.env.get('AUTOFORM_REPOSITORY_REPORT')
        if acquisition:
            candidate = read(acquisition)
            if candidate.get('status') == 'ready' and candidate.get('source') == str(self.source):
                repository = candidate
        data['repository'] = repository
        if scope is not None:
            data['source_coverage'] = scope
        certificate = guarantee.emit(self.root, self.report, self.module, self.source,
                                     self.stages, repository, self.properties is not None,
                                     **({'source_scope': scope} if scope is not None else {}))
        if certificate['status'] != 'verified_scoped':
            issues.append('guarantee')
            data.update(execution_status='completed_with_gaps', verification_complete=False)
        data['guarantee_status'] = certificate['status']
        if self.properties is not None:
            data['security_status'] = certificate.get('security', {}).get('status', 'unverified')
        write(self.report / 'run.json', data)
        def count_text(value):
            return 'unknown (not reported)' if value is None else str(value)

        conformance_counts = data['proof_summary']['conformance']
        lines = ['# Assurance run: ' + self.module, '',
                 'Execution: **' + data['execution_status'] + '**. '
                 'Verification complete: **' + str(data['verification_complete']).lower() + '**.', '',
                 f"Compared cases: {data['comparisons']}; divergences: {data['divergences']}; "
                 f"translation holes: {data['holes']}.", '',
                 'Conformance specifications: ' + count_text(conformance_counts['proofs']) +
                 ' proved; ' + count_text(conformance_counts['open_obligations']) + ' open obligations.', '']
        if self.properties is not None:
            security_counts = data['proof_summary']['security']
            lines += ['Independent security properties: ' + count_text(security_counts['proofs']) +
                      ' proved; ' + count_text(security_counts['open_obligations']) + ' open obligations.', '']
        if scope is not None:
            lines += ['Source files represented in the model: ' + str(scope['counts']['represented']) +
                      '; supported files absent from it: ' + str(scope['counts']['unrepresented']) +
                      '; unsupported files: ' + str(scope['counts']['unsupported']) + '.', '',
                      'File presence does not prove complete parsing or translation. '
                      '[All files and source stability](source-coverage.json).', '']
        lines += ['| Stage | Status | Detail |', '|---|---|---|']
        for name, item in self.stages.items():
            detail = item.get('reason', item.get('error', 'exit ' + str(item.get('exit_code'))))
            if item.get('log'):
                detail += '; [log](' + item['log'] + ')'
            lines.append('| ' + name + ' | ' + item['status'] + ' | ' + detail + ' |')
        lines += ['', 'A completed workflow is not a proof of the entire codebase. '
                  'Unsupported, unexercised and failed checks remain gaps.', '',
                  '[Proof guarantee and scope](guarantee.md) · [Detailed assurance argument](assurance.md) '
                  '· [Machine-readable stage report](run.json)', '']
        if self.properties is not None:
            lines += ['[Independent security properties and their exact scope](security.md)', '']
        (self.report / 'summary.md').write_text('\n'.join(lines))
        print('==> ' + data['execution_status'] + ': ' + str(self.report / 'summary.md'), flush=True)
        return 1 if issues else 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('module')
    parser.add_argument('--properties', type=Path,
        help='independent Lean security properties (default: SOURCE/autoform.properties.json if present)')
    parser.add_argument('--stage-timeout', type=float, default=7200,
        help='maximum seconds for each assurance stage (default: 7200)')
    args = parser.parse_args(argv)
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', args.module):
        parser.error('module must be a Lean identifier beginning with an uppercase letter')
    if not math.isfinite(args.stage_timeout) or args.stage_timeout <= 0:
        parser.error('--stage-timeout must be a finite positive number')
    from repository_assurance import RepositoryRun
    job = RepositoryRun(Assurance(args.source, args.module, properties=args.properties,
                                  stage_timeout=args.stage_timeout))

    def terminate(signum, _frame):
        raise SignalInterrupt(signum)

    previous_termination = signal.signal(signal.SIGTERM, terminate)
    try:
        return job.execute()
    except (KeyboardInterrupt, Exception) as exc:
        job.stages['interrupted' if isinstance(exc, KeyboardInterrupt) else 'driver'] = dict(
            status='failed', reason=str(exc) or type(exc).__name__)
        job.finish()
        return interrupt_exit_code(exc) if isinstance(exc, KeyboardInterrupt) else 2
    finally:
        signal.signal(signal.SIGTERM, previous_termination)


if __name__ == '__main__':
    sys.exit(main())
