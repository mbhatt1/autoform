"""Publish the exact guarantee supported by this run's audited proof artifacts."""
import json
import os
import re
from pathlib import Path

import proof_artifacts
import deep_json
import security_specs


def read(path):
    try:
        data = deep_json.load(path)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


def object_value(value):
    return value if isinstance(value, dict) else {}


def dialect_assumptions(conformance):
    """Declare an inexact source-language dialect as an assumption of the guarantee.

    `differential.py` records `dialect_is_exact: false` for languages Core has no
    dedicated dialect for -- Java, Kotlin and Go all run under `.cLike`. Until this
    function existed that flag was WRITE-ONLY: nothing downstream read it, so a Java
    guarantee listed three generic assumptions and silently omitted the one thing
    this project's own headline finding says is a correctness issue. A dialect
    mismatch (Python's floored `%` against C's truncated `%`) is precisely how every
    C and Java program once got wrong answers, so it belongs in `assumptions`, where
    a reader of the guarantee will see it, and not only in a conformance log.
    """
    if conformance.get('dialect_is_exact') is not False:
        return []
    language = conformance.get('language') or 'this language'
    dialect = conformance.get('dialect_expected') or 'an approximating'
    note = conformance.get('dialect_note')
    text = (f'Core has no {language}-specific dialect; {language} was interpreted under '
            f'the `.{dialect}` dialect. Operations the exporter could type are handled by '
            f'{language}-specific typed numeric semantics, but any operation left untyped '
            f'falls back to `.{dialect}` behaviour, which may differ from {language}.')
    return [text + (' ' + note if note else '')]


def emit(root, report, module, source, stages, repository=None, security_requested=False,
         source_scope=None):
    root, report = Path(root), Path(report)
    specs, audit = read(report / 'specs.json'), read(report / 'audit.json')
    mutation, conformance = read(report / 'mutation.json'), read(report / 'conformance.json')
    required = ('source', 'core-oracle', 'mutation', 'restore-build', 'audit')
    failures = [name for name in required if not security_specs.completed_stage(stages, name)]
    scope_failures = []
    if source_scope is not None:
        if source_scope.get('scan_complete') is not True:
            scope_failures.append('repository file inventory incomplete')
        if source_scope.get('source_stable') is not True:
            scope_failures.append('repository inputs changed during analysis')
        if source_scope.get('unexpected_ast_files'):
            scope_failures.append('exported files absent from the repository inventory')
        failures.extend(scope_failures)
    proof_module = 'Autoform.SpecsGen.' + module
    model = root / 'Autoform/Generated' / (module + '.lean')
    proof = root / 'Autoform/SpecsGen' / (module + '.lean')
    entries = specs.get('specs', [])
    proved = [s for s in entries if isinstance(s, dict) and s.get('proved') is True
              and s.get('family') == 'conform'] if isinstance(entries, list) else []
    if any(not isinstance(s.get('id'), str) or not re.fullmatch(r'conform_\w+', s['id'])
           or not isinstance(s.get('subject'), str)
           or s.get('definition') != security_specs.ident(s['subject']) or type(s.get('domain')) is not int
           or s['domain'] < 1 for s in proved):
        failures.append('invalid conformance claim metadata')
        proved = []
    if len({s['id'] for s in proved}) != len(proved) or len({s['subject'] for s in proved}) != len(proved):
        failures.append('duplicate conformance claim inventory')
    if not (proved and specs.get('build_clean') is True and specs.get('module') == module
            and specs.get('cross_runtime_evidence') is True):
        failures.append('native conformance proofs unavailable')
    checker = object_value(audit.get('lean4checker'))
    if not (audit.get('root_module') == proof_module and object_value(audit.get('verdict')).get('pass') is True
            and checker.get('status') == 'VERIFIED' and checker.get('mode') == 'fresh'
            and security_specs.zero_exit(checker.get('returncode'))):
        failures.append('independent proof replay unavailable')
    snapshot = object_value(audit.get('artifact_snapshot'))
    files = object_value(snapshot.get('files'))
    if snapshot.get('status') != 'STABLE':
        failures.append('stable replay artifact snapshot unavailable')
    for name in proof_artifacts.changed(root, files):
        failures.append('audited artifact changed or unavailable: ' + name)
    required_paths = [model, proof, root / '.lake/build/lib/lean' /
                      (proof_module.replace('.', '/') + '.olean')]
    required_paths += [report / name for name in ('specs.json', 'conformance.json', 'mutation.json',
                      'core-oracle.json', 'context.json', 'ast-' + module + '.json')]
    if source_scope is not None:
        required_paths += [report / 'inventory.json', report / 'selection.json']
    for path in required_paths:
        if not path.is_file() or not isinstance(files.get(proof_artifacts.key(root, path)), str):
            failures.append('required artifact not bound to replay: ' + proof_artifacts.key(root, path))
    bindings = object_value(specs.get('artifact_hashes'))
    for name, path in [('model', model), ('proof', proof), ('conformance', report / 'conformance.json'),
                       ('ast', report / ('ast-' + module + '.json'))]:
        try:
            current = proof_artifacts.digest(path)
        except OSError:
            current = None
        if current is None or bindings.get(name) != current:
            failures.append('specification generation artifact changed: ' + name)
    if not (mutation.get('status') == 'OK' and mutation.get('module') == 'Autoform.Generated.' + module
            and mutation.get('spec_module') == proof_module and not mutation.get('inconclusive')
            and not mutation.get('coarse_attributions')
            and security_specs.zero_exit(object_value(mutation.get('restored_build')).get('exit_code'))):
        failures.append('complete, attributable mutation evidence unavailable')
    theorem_names = object_value(audit.get('axiom_sweep')).get('root_theorem_names')
    theorem_names = theorem_names if isinstance(theorem_names, list) else []
    for spec in proved:
        if proof_module + '.' + spec['id'] not in theorem_names:
            failures.append('claimed theorem absent from replayed module: ' + spec['id'])
        if not security_specs.mutation_adequate(mutation, spec['id'], spec.get('definition')):
            failures.append('specification adequacy unverified: ' + spec['id'])
    if not failures:
        try:
            from runtime_backends import load_observations
            rows, _ = load_observations(report / 'conformance.json', report / ('ast-' + module + '.json'),
                                        source, module, root / 'Autoform/Generated' / (module + '.lean'))
            if (conformance.get('build_stable') is not True
                    or not security_specs.zero_exit(conformance.get('divergences'))
                    or not security_specs.nonnegative_count(conformance.get('total'))
                    or conformance['total'] < len(rows)):
                raise ValueError('invalid native observation summary')
            for spec in proved:
                observed = sum(row.get('name') == spec['subject'] for row in rows)
                if spec['domain'] > observed:
                    raise ValueError('claimed cases exceed observations for subject: ' + spec['subject'])
        except (OSError, ValueError, KeyError, TypeError, AttributeError) as exc:
            failures.append('evidence provenance: ' + str(exc))
    security = None
    if security_requested:
        security = security_specs.certify(root, report, source, module, stages)
        if scope_failures:
            security.update(status='unverified', claims=[])
            security.setdefault('failed_checks', []).extend(scope_failures)
        security_specs.publish(report, security)
        if security['status'] != 'verified_scoped':
            failures.append('requested independent security properties unverified')
    artifacts = {}
    for path in (report / 'conformance.json', report / 'specs.json', report / 'audit.json',
                 report / 'mutation.json', report / 'context.json', report / 'repository.json',
                 root / 'Autoform/Generated' / (module + '.lean'),
                 root / 'Autoform/SpecsGen' / (module + '.lean')):
        if path.is_file():
            try:
                artifacts[os.path.relpath(path, report)] = proof_artifacts.digest(path)
            except OSError:
                failures.append('evidence artifact unreadable: ' + str(path))
    claims = [dict(theorem=proof_module + '.' + s['id'], subject=s['subject'],
                   recorded_cases=s['domain'], all_inputs=False,
                   property='The Lean model produces the recorded native outcome for each listed input and initial state.')
              for s in proved] if not failures else []
    data = dict(schema_version=2, module=module,
                status='verified_scoped' if claims else 'unverified',
                whole_program_correctness=False, claims=claims, failed_checks=failures,
                repository=repository, source=str(source),
                native_observations=conformance.get('total', 0),
                assumptions=[
                    'The recorded build context, source revision and initial states define the scope.',
                    'The Lean kernel and stated interpreter semantics are trusted.',
                    'Native comparisons test translation fidelity on recorded cases; they do not prove it for all inputs.',
                ] + dialect_assumptions(conformance),
                exclusions=['All-input correctness of the original program', 'Absence of all bugs or security vulnerabilities',
                            'Untranslated, unexecuted or unproved behavior',
                            'Deployment behavior outside the recorded environment'],
                evidence_sha256=artifacts,
                replay_command='lake env leanchecker --fresh ' + proof_module)
    if security_requested:
        data['schema_version'] = 3
        data['security'] = security
        for name in security_specs.OUTPUTS:
            path = report / name
            if path.is_file():
                data['evidence_sha256'][name] = proof_artifacts.digest(path)
    if source_scope is not None:
        data['source_coverage'] = source_scope
        for name in ('inventory.json', 'inventory-after.json', 'source-coverage.json', 'selection.json'):
            path = report / name
            if path.is_file():
                data['evidence_sha256'][name] = proof_artifacts.digest(path)
    (report / 'guarantee.json').write_text(json.dumps(data, indent=2) + '\n')
    lines = ['# Proof guarantee: ' + module, '', '**' + data['status'] + '**', '',
             'Conformance guarantees concern the listed input cases and initial states. '
             'Whole-program correctness and absence of all bugs are not established.', '']
    if repository and repository.get('commit'):
        lines += ['Source commit: `' + repository['commit'] + '`.', '']
    for claim in claims:
        lines.append('- `' + claim['theorem'] + '`: ' + str(claim['recorded_cases']) +
                     ' recorded cases for `' + claim['subject'] + '`.')
    if failures:
        lines += ['No verified guarantee was issued. Failed or missing checks:', '']
        lines += ['- ' + failure for failure in failures]
    if security_requested:
        lines += ['', 'Independent security properties: **' + security['status'] + '**. '
                  'Their scope is the supplied Lean propositions and premises.', '',
                  '[Security properties, proof attempts and open obligations](security.md)', '']
    lines += ['', '[Exact scope, assumptions and artifact hashes](guarantee.json)', '']
    (report / 'guarantee.md').write_text('\n'.join(lines))
    return data
