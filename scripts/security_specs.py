"""Prove independently supplied Lean properties of a generated source model.

Property statements are inputs, never inferred from the implementation's answers.
An unsuccessful proof attempt is an open obligation, not a counterexample. The
certificate names the exact propositions and retains source-fidelity assumptions.
"""
from pathlib import Path
import argparse
import json
import os
import re
import signal
import subprocess
import sys

import deep_json
import proof_artifacts
import runtime_backends

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'cartographer'))
from render_lean import ident, lean_str

OUTPUTS = ('properties.json', 'security-claims.json', 'security-mutation.json',
           'security-audit.json', 'security.json', 'security.md')
DEFAULT_PROOF = 'by intros; first | decide +kernel | portfolio'


def obj(value):
    return value if isinstance(value, dict) else {}


def nonnegative_count(value):
    return type(value) is int and value >= 0


def zero_exit(value):
    # JSON booleans compare equal to Python integers; they are not exit codes.
    return type(value) is int and value == 0


def completed_stage(stages, name):
    stage = obj(obj(stages).get(name))
    return (stage.get('status') == 'completed' and zero_exit(stage.get('exit_code'))
            and stage.get('timed_out', False) is False)


def mutation_adequate(mutation, theorem, definition):
    """Require attributable mutation records, not only a favorable summary label."""
    result = obj(obj(mutation.get('theorems')).get(theorem))
    if (not isinstance(definition, str) or not definition
            or obj(mutation.get('restored_build')).get('timeout', False) is not False
            or obj(mutation.get('subject_map')).get(theorem) != [definition]
            or result.get('scope') != 'on-subject' or result.get('verdict') != 'HAS TEETH'
            or any(not nonnegative_count(result.get(key)) for key in ('killed', 'survived', 'inconclusive'))
            or result['killed'] < 1 or result['survived'] != 0 or result['inconclusive'] != 0):
        return False
    records = mutation.get('mutants')
    if (not isinstance(records, list)
            or any(not nonnegative_count(mutation.get(key)) for key in
                   ('mutants_generated', 'mutants_run', 'invalid', 'inconclusive', 'coarse_attributions'))
            or mutation['mutants_run'] != len(records)
            or mutation['mutants_generated'] < len(records)
            or mutation['inconclusive'] != 0 or mutation['coarse_attributions'] != 0):
        return False
    killed, invalid = 0, 0
    for record in records:
        if (not isinstance(record, dict) or not isinstance(record.get('decl'), str)
                or record.get('timeout', False) is not False):
            return False
        verdict = record.get('verdict')
        if verdict == 'invalid':
            invalid += 1
            continue
        if not isinstance(verdict, dict) or verdict.get(theorem) not in ('killed', 'survived'):
            return False
        if record['decl'] == definition:
            if verdict[theorem] != 'killed':
                return False
            killed += 1
    return killed == result['killed'] and invalid == mutation['invalid']


def read(path):
    try:
        value = deep_json.load(path)
        return value if isinstance(value, dict) else {}
    except (OSError, ValueError):
        return {}


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def load_properties(path, functions, *, content=None):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('duplicate property field: ' + key)
            result[key] = value
        return result

    data = json.loads(content if content is not None else Path(path).read_text(), object_pairs_hook=unique)
    if (not isinstance(data, dict) or set(data) != {'schema_version', 'claims'}
            or type(data['schema_version']) is not int or data['schema_version'] != 1
            or not isinstance(data['claims'], list) or not data['claims']):
        raise ValueError('properties require schema_version 1 and a nonempty claims list')
    names = [f['name'] for f in functions]
    definitions = [ident(name) for name in names]
    seen = set()
    for claim in data['claims']:
        if (not isinstance(claim, dict) or set(claim) - {'id', 'subject', 'statement', 'proof', 'description'}
                or not {'id', 'subject', 'statement'} <= set(claim)):
            raise ValueError('each property requires id, subject and statement; unknown fields are rejected')
        for key, value in claim.items():
            if not isinstance(value, str) or not value.strip():
                raise ValueError('property fields must be nonempty strings: ' + key)
        if not re.fullmatch(r'[a-z][a-z0-9_]{0,63}', claim['id']) or claim['id'] in seen:
            raise ValueError('property ids must be distinct lowercase identifiers of at most 64 characters')
        seen.add(claim['id'])
        if names.count(claim['subject']) != 1 or definitions.count(ident(claim['subject'])) != 1:
            raise ValueError('property subject is missing or ambiguous: ' + claim['subject'])
    return data


def header(module):
    return (f'import Autoform.Generated.{module}\n'
            'import Autoform.Tactics.Portfolio\nimport Autoform.Harness.Audit\n'
            'set_option autoImplicit false\nset_option maxRecDepth 10000\n'
            'set_option maxHeartbeats 2000000\nset_option pp.maxSteps 1000000\n'
            f'open Autoform.Core Autoform.Generated.{module}\n')


def declaration(claim):
    # Both fragments are parsed as complete Lean terms before interpolating them
    # into a command. A statement cannot close this declaration and add commands.
    return (f"theorem property_{claim['id']} : (\n{claim['statement']}\n) := (\n"
            f"{claim.get('proof', DEFAULT_PROOF)}\n)\n")


def lean_run(root, report, source, tag, timeout):
    path = report / (tag + '.lean')
    path.write_text(source)
    log = report / (tag + '.log')
    env = dict(os.environ, PATH=str(Path.home() / '.elan/bin') + os.pathsep + os.environ.get('PATH', ''))
    process = None
    try:
        with log.open('w') as stream:
            process = subprocess.Popen(['lake', 'env', 'lean', str(path)], cwd=root, env=env,
                                       stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = process.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                code = 124
                stream.write('\nProperty check exceeded its deadline.\n')
    except OSError as exc:
        log.write_text(str(exc) + '\n')
        code = 127
    finally:
        if process is not None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
    return code, log.read_text()


def generate(root, report, source, module, properties, timeout=180):
    root, report, source = Path(root), Path(report), Path(source)
    report.mkdir(parents=True, exist_ok=True)
    ast = report / ('ast-' + module + '.json')
    functions = deep_json.load(ast)
    # The copied request is the proof input, even if its original file changes.
    request = Path(properties).read_bytes()
    (report / 'properties.json').write_bytes(request)
    data = load_properties(report / 'properties.json', functions)
    model = root / 'Autoform/Generated' / (module + '.lean')
    before = {name: proof_artifacts.digest(path) for name, path in
              [('model', model), ('ast', ast), ('properties', report / 'properties.json')]}
    source_hashes = runtime_backends.source_fingerprints(source, functions)
    if not source_hashes:
        raise ValueError('no source files can be bound to the security properties')
    fragments = [text for claim in data['claims'] for text in
                 (claim['statement'], claim.get('proof', DEFAULT_PROOF))]
    validation = header(module) + '''\nopen Lean Elab Command
run_cmd do
  let env ← getEnv
  for text in (FRAGMENTS : List String) do
    match Parser.runParserCategory env `term text with
    | .ok _ => pure ()
    | .error message => throwError "invalid property term: {message}"
'''.replace('FRAGMENTS', '[' + ', '.join(map(lean_str, fragments)) + ']')
    code, output = lean_run(root, report, validation, 'security-syntax', timeout)
    if code:
        raise ValueError('invalid or unchecked property syntax; see security-syntax.log')
    proof_module = 'Autoform.Security.' + module
    claims, declarations = [], []
    for requested in data['claims']:
        claim = dict(requested, definition=ident(requested['subject']),
                     theorem=proof_module + '.property_' + requested['id'])
        name = claim['theorem']
        checks = f'\n#audit_axioms {name}\n#audit_depends {name} on {claim["definition"]}\n'
        checks += '''\nopen Lean Elab Command in
run_cmd liftTermElabM do
  let env ← getEnv
  let name := String.toName NAME
  let some (.thmInfo info) := env.find? name | throwError "property theorem missing"
  let axioms ← collectAxioms name
  unless axioms.all (fun a => [``propext, ``Quot.sound, ``Classical.choice].contains a) do
    throwError "property uses an unapproved axiom"
  let statement ← Lean.Meta.ppExpr info.type
  IO.println ("AUTOFORM_SECURITY:" ++ (Json.mkObj [
    ("theorem", Json.str name.toString), ("statement", Json.str statement.pretty)]).compress)
'''.replace('NAME', lean_str(name))
        candidate = header(module) + '\nnamespace ' + proof_module + '\n'
        candidate += declaration(claim) + '\nend ' + proof_module + '\n' + checks
        code, output = lean_run(root, report, candidate, 'security-' + claim['id'], timeout)
        records = [json.loads(line[len('AUTOFORM_SECURITY:'):]) for line in output.splitlines()
                   if line.startswith('AUTOFORM_SECURITY:')]
        proved = code == 0 and len(records) == 1 and records[0].get('theorem') == name
        claim.update(proved=proved, status='proved' if proved else 'unresolved',
                     log='security-' + claim['id'] + '.log', exit_code=code)
        if proved:
            claim['elaborated_statement'] = records[0]['statement']
            declarations.append(declaration(claim))
        else:
            claim['reason'] = ('proof attempt timed out' if code == 124 else
                              'proof or dependency/axiom check failed; this is not a native-confirmed violation')
        claims.append(claim)
    proof = root / 'Autoform/Security' / (module + '.lean')
    proof.parent.mkdir(parents=True, exist_ok=True)
    proof.write_text(header(module) + '\nnamespace ' + proof_module + '\n\n' +
                     '\n'.join(declarations) + '\nend ' + proof_module + '\n')
    for name, path in [('model', model), ('ast', ast), ('properties', report / 'properties.json')]:
        if proof_artifacts.digest(path) != before[name]:
            raise ValueError('security proof input changed during generation: ' + name)
    if runtime_backends.source_fingerprints(source, functions) != source_hashes:
        raise ValueError('source changed during property generation')
    result = dict(schema_version=1, module=module, proof_module=proof_module, claims=claims,
                  source_sha256=source_hashes, artifact_hashes=dict(before, proof=proof_artifacts.digest(proof)),
                  proved=sum(c['proved'] for c in claims), open_obligations=sum(not c['proved'] for c in claims))
    write(report / 'security-claims.json', result)
    return result


def certify(root, report, source, module, stages):
    root, report, source = Path(root), Path(report), Path(source)
    specs, audit = read(report / 'security-claims.json'), read(report / 'security-audit.json')
    mutation = read(report / 'security-mutation.json')
    proof_module = 'Autoform.Security.' + module
    failures = [name for name in ('security-properties', 'security-mutation', 'security-restore', 'security-audit')
                if not completed_stage(stages, name)]
    entries = specs.get('claims', [])
    entries = entries if isinstance(entries, list) else []
    if (specs.get('module') != module or specs.get('proof_module') != proof_module or not entries
            or any(not isinstance(c, dict) or c.get('proved') is not True for c in entries)):
        failures.append('one or more independent properties remain unresolved')
    if (not nonnegative_count(specs.get('proved')) or not nonnegative_count(specs.get('open_obligations'))
            or specs.get('proved') != sum(isinstance(c, dict) and c.get('proved') is True for c in entries)
            or specs.get('open_obligations') != sum(not isinstance(c, dict) or c.get('proved') is not True
                                                   for c in entries)):
        failures.append('independent property counts disagree with the claim inventory')
    checker = obj(audit.get('lean4checker'))
    if (audit.get('root_module') != proof_module or obj(audit.get('verdict')).get('pass') is not True
            or checker.get('status') != 'VERIFIED' or checker.get('mode') != 'fresh'
            or not zero_exit(checker.get('returncode'))):
        failures.append('fresh security proof replay unavailable')
    snapshot = obj(audit.get('artifact_snapshot'))
    if not proof_artifacts.replay_current(root, snapshot, proof_module):
        failures.append('security replay artifacts are missing or changed')
    files = snapshot.get('files', {})
    model = root / 'Autoform/Generated' / (module + '.lean')
    proof = root / 'Autoform/Security' / (module + '.lean')
    ast = report / ('ast-' + module + '.json')
    required = [model, proof, ast, *[report / name for name in
                ('properties.json', 'security-claims.json', 'security-mutation.json', 'context.json')]]
    if not isinstance(files, dict) or any(not isinstance(files.get(proof_artifacts.key(root, p)), str)
                                          for p in required):
        failures.append('security evidence is not bound to the replay')
    for key, path in [('model', model), ('proof', proof), ('ast', ast), ('properties', report / 'properties.json')]:
        if not path.is_file() or obj(specs.get('artifact_hashes')).get(key) != proof_artifacts.digest(path):
            failures.append('security generation input changed: ' + key)
    try:
        functions = deep_json.load(ast)
        request = load_properties(report / 'properties.json', functions)
        requested = {c['id']: c for c in request['claims']}
        if len(entries) != len(requested) or len({c.get('id') for c in entries}) != len(entries):
            raise ValueError('property claim inventory differs from the request')
        for claim in entries:
            item = requested.get(claim.get('id'))
            if not item or any(claim.get(k) != v for k, v in item.items()):
                raise ValueError('property statement differs from the request')
            if (claim.get('theorem') != proof_module + '.property_' + item['id']
                    or claim.get('definition') != ident(item['subject'])):
                raise ValueError('property theorem or subject differs from the request')
        if runtime_backends.source_fingerprints(source, functions) != specs.get('source_sha256'):
            raise ValueError('source has changed since property generation')
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as exc:
        failures.append('security provenance: ' + str(exc))
    if (mutation.get('status') != 'OK' or mutation.get('module') != 'Autoform.Generated.' + module
            or mutation.get('spec_module') != proof_module or mutation.get('inconclusive')
            or mutation.get('coarse_attributions')
            or not zero_exit(obj(mutation.get('restored_build')).get('exit_code'))):
        failures.append('complete attributable security mutations unavailable')
    theorem_names = obj(audit.get('axiom_sweep')).get('root_theorem_names', [])
    theorem_names = theorem_names if isinstance(theorem_names, list) else []
    for claim in entries:
        if not isinstance(claim, dict):
            continue
        if claim.get('theorem') not in theorem_names:
            failures.append('property theorem absent from replay: ' + str(claim.get('id')))
        theorem_id = 'property_' + str(claim.get('id'))
        if obj(mutation.get('subject_map')).get(theorem_id) != [claim.get('definition')]:
            failures.append('property mutation subject differs: ' + str(claim.get('id')))
        if not mutation_adequate(mutation, theorem_id, claim.get('definition')):
            failures.append('property mutation adequacy unverified: ' + str(claim.get('id')))
    return dict(schema_version=1, status='verified_scoped' if not failures else 'unverified',
                module=module, claims=entries if not failures else [], failed_checks=failures,
                open_obligations=specs.get('open_obligations'),
                scope='Exactly the supplied Lean propositions, under the generated model and their stated premises.',
                assumptions=['Source equivalence for all inputs is an assumption; native comparisons are separate evidence.',
                             'A property proof does not establish that its premises hold in deployment.',
                             'The Lean kernel, interpreter semantics and evidence runner are trusted.'],
                native_validation=dict(status='not_run', reason='No native property oracle is supplied; conformance is separate evidence.'),
                native_confirmed_violations=[])


def publish(report, result):
    report = Path(report)
    write(report / 'security.json', result)
    lines = ['# Independent security properties', '', '**' + result['status'] + '**', '', result['scope'], '']
    for claim in result['claims']:
        lines += ['- `' + claim['theorem'] + '` for `' + claim['subject'] + '`:', '',
                  '```lean', claim['statement'], '```', '']
    if result['failed_checks']:
        lines += ['No security guarantee was issued.', ''] + ['- ' + s for s in result['failed_checks']]
    lines += ['', 'An unsuccessful proof attempt is not a vulnerability finding. '
              'Native property counterexamples were not searched automatically.', '',
              '[Property attempts and open obligations](security-claims.json) · [Exact certificate](security.json)', '']
    (report / 'security.md').write_text('\n'.join(lines))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('module')
    parser.add_argument('properties', type=Path)
    parser.add_argument('--timeout', type=int, default=180)
    args = parser.parse_args(argv)
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', args.module) or args.timeout < 1:
        parser.error('a valid module name and positive timeout are required')
    report = ROOT / 'artifacts/pipeline' / args.module
    (report / 'security-claims.json').unlink(missing_ok=True)
    try:
        data = generate(ROOT, report, args.source.resolve(), args.module, args.properties, args.timeout)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print('security properties: ' + str(exc), file=sys.stderr)
        return 2
    print(f"Independent properties: {data['proved']} proved, {data['open_obligations']} open obligations")
    return 1 if data['open_obligations'] else 0


if __name__ == '__main__':
    sys.exit(main())
