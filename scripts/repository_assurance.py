"""Dispatch repository languages and retain the scope of every child proof run."""
import hashlib
import json
import os
from pathlib import Path
import re

import proof_artifacts
import repository_inventory
import repository_scope
import security_specs


def read(path):
    try:
        result = json.loads(Path(path).read_text())
        return result if isinstance(result, dict) else {}
    except (OSError, ValueError):
        return {}


def write(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def property_request(path):
    """Validate the request schema before routing its subjects to actual models."""
    content = path if isinstance(path, bytes) else Path(path).read_bytes()
    request = json.loads(content)
    if not isinstance(request, dict) or not isinstance(request.get('claims'), list):
        raise ValueError('properties require an object with a claims list')
    subjects = {claim['subject'] for claim in request['claims']
                if isinstance(claim, dict) and isinstance(claim.get('subject'), str)}
    # load_properties checks duplicate JSON keys, IDs, fields and identifier
    # collisions. These placeholders validate syntax only; actual routing below
    # requires the exact subject in a child's freshly exported function list.
    return security_specs.load_properties(None, [{'name': name} for name in sorted(subjects)], content=content)


def current_certificate(root, report, certificate, audit_name='audit.json'):
    """Recheck earlier child evidence after later children have executed."""
    if certificate.get('status') != 'verified_scoped' or not certificate.get('claims'):
        return False
    bindings = certificate.get('evidence_sha256')
    if not isinstance(bindings, dict) or not bindings or audit_name not in bindings:
        return False
    try:
        for name, digest in bindings.items():
            if (not isinstance(name, str) or not isinstance(digest, str)
                    or not re.fullmatch(r'[0-9a-f]{64}', digest)):
                return False
            path = report / name
            if not path.is_file() or proof_artifacts.digest(path) != digest:
                return False
        audit = read(report / audit_name)
        expected_module = ('Autoform.Security.' if audit_name == 'security-audit.json'
                           else 'Autoform.SpecsGen.') + str(certificate.get('module', ''))
        return (audit.get('root_module') == expected_module
                and audit.get('verdict', {}).get('pass') is True
                and audit.get('lean4checker', {}).get('status') == 'VERIFIED'
                and audit.get('lean4checker', {}).get('mode') == 'fresh'
                and security_specs.zero_exit(audit.get('lean4checker', {}).get('returncode'))
                and audit.get('artifact_snapshot', {}).get('status') == 'STABLE'
                and not proof_artifacts.changed(root, audit['artifact_snapshot'].get('files')))
    except (OSError, ValueError, TypeError, AttributeError):
        return False


def scan_exclusions(job):
    root, source = job.root.resolve(), job.source.resolve()
    if root == source:
        return ('artifacts',)
    return (str(root),) if root.is_relative_to(source) else ()


def configure(job, language, inventory, exclusions):
    job.language, job.inventory, job.inventory_exclude = language, inventory, exclusions
    job.env.update(AUTOFORM_LANGUAGE=language,
                   AUTOFORM_FRONTEND=repository_inventory.ADAPTERS[language]['frontend'],
                   PYTHONDONTWRITEBYTECODE='1')


class RepositoryRun:
    def __init__(self, job):
        self.job = job
        self.delegate = False
        self.inventory = None
        self.exclusions = scan_exclusions(job)
        self.children = []
        self.request = None
        self.property_error = None
        self.property_input = None

    @property
    def stages(self):
        return self.job.stages

    def execute(self):
        job = self.job
        print('==> inventory: ' + str(job.source), flush=True)
        self.inventory = repository_inventory.discover(job.source, exclude=self.exclusions)
        languages = sorted(language for language, data in self.inventory['languages'].items()
                           if data['supported_files'])
        if len(languages) == 1 and len(self.inventory['languages']) == 1:
            self.delegate = True
            configure(job, languages[0], self.inventory, self.exclusions)
            return job.execute()

        content, self.property_error = job.snapshot_properties()
        self.property_input = content
        job.clear_outputs()
        write(job.report / 'inventory.json', self.inventory)
        job.stages['inventory'] = dict(status='completed' if self.inventory['scan_complete'] else 'failed',
                                      exit_code=0 if self.inventory['scan_complete'] else 1)
        job.checkpoint()
        if content is not None:
            frozen = job.report / 'properties.json'
            frozen.write_bytes(content)
            try:
                self.request = property_request(content)
            except (OSError, ValueError, TypeError) as exc:
                self.property_error = str(exc)
        if self.property_error:
            job.blocked('security-properties', self.property_error)
            return self.finish()
        if not languages:
            job.blocked('source', 'No supported source-language adapter matches the inventoried files.')
            return self.finish()

        # All children keep the original checkout, imports and build context.
        # Shared Lake state and mutation restoration require sequential execution.
        for language in languages:
            module = job.module + language.title()
            print('==> repository language: ' + language + ' (' + module + ')', flush=True)
            manifest = read(job.root / '.autoform-package.json')
            if 'Autoform/Generated/' + module + '.lean' in manifest.get('files', {}):
                job.blocked(language, 'Child module collides with a bundled runtime resource: ' + module)
                continue
            try:
                child = type(job)(job.source, module, root=job.root,
                    properties=job.report / 'properties.json' if self.request is not None else None,
                    stage_timeout=job.stage_timeout, language=language, inventory=self.inventory,
                    inventory_exclude=self.exclusions, route_properties=self.request is not None,
                    frozen_properties=content)
                child.env.update({key: value for key, value in job.env.items()
                                  if key not in ('AUTOFORM_LANGUAGE', 'AUTOFORM_FRONTEND')})
                child.env['PYTHONDONTWRITEBYTECODE'] = '1'
            except (OSError, ValueError) as exc:
                job.blocked(language, 'Child setup failed: ' + str(exc))
                continue
            interrupted = None
            try:
                code = child.execute()
            except (KeyboardInterrupt, Exception) as exc:
                child.stages['interrupted' if isinstance(exc, KeyboardInterrupt) else 'driver'] = dict(
                    status='failed', reason=str(exc) or type(exc).__name__)
                child.finish()
                code = 128 + getattr(exc, 'signum', 2) if isinstance(exc, KeyboardInterrupt) else 2
                interrupted = exc if isinstance(exc, KeyboardInterrupt) else None
            record = dict(language=language, module=module, exit_code=code,
                          report=os.path.relpath(child.report, job.report))
            self.children.append(record)
            job.stages[language] = dict(status='completed' if code in (0, 1) else 'failed',
                                       exit_code=code, report=record['report'] + '/summary.md')
            job.checkpoint()
            if interrupted is not None:
                raise interrupted
        return self.finish()

    def finish(self):
        if self.delegate:
            return self.job.finish()
        job = self.job
        if self.inventory is None:
            self.inventory = repository_inventory.discover(job.source, exclude=self.exclusions)
            write(job.report / 'inventory.json', self.inventory)
        after = repository_inventory.discover(job.source, exclude=self.exclusions)
        write(job.report / 'inventory-after.json', after)
        scope = repository_scope.coverage(self.inventory, after, job.report / 'no-repository-model.json', {})
        children, represented, evidence = [], set(), {}
        request_stable = True
        if self.property_input is not None:
            try:
                request_stable = (job.report / 'properties.json').read_bytes() == self.property_input
            except OSError:
                request_stable = False
        security_routes = {}
        total_proofs, comparisons = 0, 0
        for record in self.children:
            report = job.report / record['report']
            run, certificate = read(report / 'run.json'), read(report / 'guarantee.json')
            child_scope = read(report / 'source-coverage.json')
            represented.update(row['path'] for row in child_scope.get('files', [])
                               if row.get('status') == 'represented')
            proofs = run.get('proofs')
            cases = run.get('comparisons')
            total_proofs += proofs if type(proofs) is int and proofs >= 0 else 0
            comparisons += cases if type(cases) is int and cases >= 0 else 0
            security = read(report / 'security.json')
            current = (record['exit_code'] in (0, 1)
                       and run.get('module') == certificate.get('module') == record['module']
                       and run.get('execution_status') in ('completed', 'completed_with_gaps')
                       and current_certificate(job.root, report, certificate))
            security_current = current and security.get('module') == record['module'] and current_certificate(job.root, report,
                dict(security, evidence_sha256=certificate.get('evidence_sha256')), 'security-audit.json')
            expected = {c['id']: c for c in self.request['claims']} if self.request else {}
            verified_ids = {claim.get('id') for claim in security.get('claims', []) if isinstance(claim, dict)
                            and claim.get('id') in expected
                            and claim.get('subject') == expected[claim['id']]['subject']
                            and claim.get('statement') == expected[claim['id']]['statement']}
            routed = run.get('property_selection', {}).get('routed_claim_ids', [])
            for ident in routed:
                security_routes.setdefault(ident, []).append(dict(module=record['module'],
                    verified=security_current and request_stable and ident in verified_ids))
            children.append(dict(**record, execution_status=run.get('execution_status', 'failed'),
                guarantee_status=certificate.get('status', 'unverified'), proofs=proofs,
                comparisons=cases, eligible_for_current_repository=scope['source_stable'] and
                    scope['scan_complete'] and current,
                evidence_current=current))
            for name in ('run.json', 'guarantee.json', 'security.json', 'source-coverage.json'):
                path = report / name
                if path.is_file():
                    evidence[os.path.relpath(path, job.report)] = hashlib.sha256(path.read_bytes()).hexdigest()
        for row in scope['files']:
            if row['status'] == 'unrepresented' and row['path'] in represented:
                row['status'] = 'represented'
        for status in scope['counts']:
            scope['counts'][status] = sum(row['status'] == status for row in scope['files'])
        scope['truncated_by_method_limit'] = any(
            read(job.report / c['report'] / 'source-coverage.json').get('truncated_by_method_limit')
            for c in children)
        write(job.report / 'source-coverage.json', scope)
        properties = []
        for claim in self.request['claims'] if self.request else []:
            routes = security_routes.get(claim['id'], [])
            status = ('verified_scoped' if len(routes) == 1 and routes[0]['verified']
                      and scope['source_stable'] and scope['scan_complete'] else
                      'ambiguous' if len(routes) > 1 else 'unverified' if routes else 'unrouted')
            properties.append(dict(id=claim['id'], subject=claim['subject'], status=status, routes=routes))
        repository = read(job.env.get('AUTOFORM_REPOSITORY_REPORT', ''))
        if repository.get('status') != 'ready' or repository.get('source') != str(job.source):
            repository = None
        issues = ['whole-repository source equivalence is not proved']
        for key in ('unsupported', 'unrepresented', 'unclassified'):
            if scope['counts'][key]:
                issues.append(key + ' files: ' + str(scope['counts'][key]))
        if not scope['source_stable']:
            issues.append('repository inputs changed during analysis')
        if not scope['scan_complete']:
            issues.append('repository inventory incomplete')
        if self.property_error:
            issues.append('security property request invalid: ' + self.property_error)
        if not request_stable:
            issues.append('frozen security property input changed during analysis')
        if any(c['guarantee_status'] == 'verified_scoped' and not c['evidence_current'] for c in children):
            issues.append('previous child proof evidence changed or is no longer current')
        if any(p['status'] != 'verified_scoped' for p in properties):
            issues.append('requested security properties remain unresolved or unrouted')
        if len(children) > 1:
            issues.append('behavior across language boundaries is not proved')
        if scope['truncated_by_method_limit']:
            issues.append('frontend method limit truncated an export')
        issues.extend(name for name, stage in job.stages.items() if stage['status'] != 'completed')
        data = job.checkpoint('completed_with_gaps')
        data.update(schema_version=1, mode='repository', verification_complete=False,
                    repository=repository, children=children, source_coverage=scope,
                    comparisons=comparisons, proofs=total_proofs, proof_counts_scope='child conformance proofs',
                    security_properties=properties, guarantee_status='unverified', issues=issues)
        if job.properties is not None:
            data['security_status'] = 'unverified'
            data['security_open_obligations'] = (sum(p['status'] != 'verified_scoped' for p in properties)
                                                  if self.request is not None else None)
        for name in ('inventory.json', 'inventory-after.json', 'source-coverage.json', 'properties.json'):
            path = job.report / name
            if path.is_file():
                evidence[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        certificate = dict(schema_version=4, module=job.module, source=str(job.source), repository=repository,
            status='unverified', whole_program_correctness=False, claims=[],
            child_certificates=[dict(module=c['module'], path=c['report'] + '/guarantee.json',
                                    status=c['guarantee_status'],
                                    eligible_for_current_repository=c['eligible_for_current_repository']) for c in children],
            security_properties=properties, failed_checks=issues, evidence_sha256=evidence,
            note='Child certificates retain their exact model/property/input scopes. '
                 'They do not compose into a whole-repository correctness guarantee.')
        write(job.report / 'guarantee.json', certificate)
        if job.properties is not None:
            write(job.report / 'security.json', dict(status='unverified', claims=[],
                properties=properties, failed_checks=issues))
            security_lines = ['# Repository security requirements', '',
                'Repository security guarantee: **unverified**.', '',
                '| Property | Subject | Status |', '|---|---|---|']
            security_lines += ['| ' + p['id'] + ' | `' + p['subject'] + '` | ' + p['status'] + ' |'
                               for p in properties]
            security_lines += ['', '[Exact routing and remaining obligations](repository-summary.json).', '']
            (job.report / 'security.md').write_text('\n'.join(security_lines))
        write(job.report / 'repository-summary.json', data)
        write(job.report / 'run.json', data)
        lines = ['# Repository assurance: ' + job.module, '',
                 '**completed_with_gaps** — repository guarantee **unverified**.', '',
                 '| Language | Source files | Runnable files | Child result |', '|---|---:|---:|---|']
        by_language = {c['language']: c for c in children}
        for language, info in sorted(self.inventory['languages'].items()):
            child = by_language.get(language)
            detail = (('[' + child['guarantee_status'] + '](' + child['report'] + '/summary.md)')
                      if child else job.stages.get(language, {}).get('reason', 'unsupported / not run'))
            lines.append(f"| {language} | {len(info['files'])} | {len(info['supported_files'])} | {detail} |")
        lines += ['', f'Conformance proofs built across children: {total_proofs}; native comparisons: {comparisons}.',
                  '', 'Remaining gaps:', '', *['- ' + issue for issue in issues], '',
                  '[Complete file inventory](inventory.json) · [File representation and source stability](source-coverage.json) '
                  '· [Exact child evidence and property routing](repository-summary.json)', '']
        if job.properties is not None:
            lines += ['[Requested security properties](security.md).', '']
        (job.report / 'summary.md').write_text('\n'.join(lines))
        (job.report / 'guarantee.md').write_text('# Repository guarantee: ' + job.module +
            '\n\n**unverified**\n\n[Child scopes and remaining gaps](summary.md).\n')
        print('==> completed_with_gaps: ' + str(job.report / 'summary.md'), flush=True)
        return 1
