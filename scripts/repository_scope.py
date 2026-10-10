"""Keep the source-file population independent of a frontend's exported AST."""
import argparse
import hashlib
import json
import os
from pathlib import Path

import deep_json
import repository_inventory


def source_path(filename, source):
    if not isinstance(filename, str) or not filename or '\0' in filename:
        return None
    source = os.path.abspath(source)
    path = os.path.abspath(os.path.join(source, filename))
    try:
        if os.path.commonpath((source, path)) != source:
            return None
        if not Path(path).resolve().is_relative_to(Path(source).resolve()):
            return None
    except (OSError, RuntimeError, ValueError):
        return None
    return Path(os.path.relpath(path, source)).as_posix()


def _dump(value, stream):
    """Write parsed JSON without recursive encoder calls or global stack changes."""
    pending = [('value', value)]
    while pending:
        kind, item = pending.pop()
        if kind == 'text':
            stream.write(item)
        elif isinstance(item, (dict, list)):
            mapping = isinstance(item, dict)
            stream.write('{' if mapping else '[')
            pending.append(('text', '}' if mapping else ']'))
            rows = list(item.items()) if mapping else list(enumerate(item))
            for index in range(len(rows) - 1, -1, -1):
                key, value = rows[index]
                pending.append(('value', value))
                if mapping:
                    pending.append(('text', json.dumps(key, ensure_ascii=True) + ':'))
                if index:
                    pending.append(('text', ','))
        else:
            stream.write(json.dumps(item, ensure_ascii=True, allow_nan=False))


def select_ast(ast_path, source, language, output_report):
    path = Path(ast_path)
    adapter = repository_inventory.ADAPTERS[language]
    functions = deep_json.load(path)
    if not isinstance(functions, list) or any(not isinstance(f, dict) for f in functions):
        raise ValueError('frontend AST must be a function list')
    selected, excluded, files = [], [], set()
    for function in functions:
        filename = function.get('file')
        relative = source_path(filename, source)
        if filename == '' or (relative is not None and Path(relative).suffix in adapter['extensions']):
            selected.append(function)
            if relative is not None:
                files.add(relative)
        else:
            excluded.append(dict(name=function.get('name'), file=filename,
                                 reason='outside selected source language or source directory'))
    before = hashlib.sha256(path.read_bytes()).hexdigest()
    if excluded:
        temporary = path.with_suffix(path.suffix + '.selected')
        try:
            with temporary.open('w', encoding='utf-8') as stream:
                _dump(selected, stream)
                stream.write('\n')
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)
    report = dict(schema_version=1, language=language, frontend=adapter['frontend'],
                  source=str(Path(source).resolve()), input_sha256=before,
                  output_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  kept_functions=len(selected), kept_files=sorted(files),
                  excluded_functions=excluded, source_census_complete=False)
    Path(output_report).write_text(json.dumps(report, indent=2) + '\n')
    if not files:
        raise ValueError('frontend exported no files in the selected source language')
    return report


def coverage(inventory_before, inventory_after, ast_path, frontend_metadata, language=None):
    try:
        functions = deep_json.load(ast_path)
    except (OSError, ValueError):
        functions = []
    if not isinstance(functions, list):
        functions = []
    represented, outside = set(), set()
    known = {entry['path'] for entry in inventory_before['files']}
    for function in functions:
        if not isinstance(function, dict):
            continue
        filename = function.get('file')
        relative = source_path(filename, inventory_before['source'])
        if relative in known:
            represented.add(relative)
        elif filename:
            outside.add(str(filename))
    rows = []
    for entry in inventory_before['files']:
        if entry['kind'] != 'regular':
            status = 'unclassified'
        elif entry['category'] == 'auxiliary':
            status = 'auxiliary'
        elif entry['category'] != 'source':
            status = 'unclassified'
        elif not entry.get('supported'):
            status = 'unsupported'
        elif language is not None and entry.get('language') != language:
            status = 'outside_partition'
        else:
            status = 'represented' if entry['path'] in represented else 'unrepresented'
        rows.append(dict(path=entry['path'], language=entry.get('language'), status=status))
    changes = repository_inventory.changed(inventory_before, inventory_after)
    counts = {status: sum(row['status'] == status for row in rows) for status in
              ('represented', 'unrepresented', 'unsupported', 'unclassified', 'auxiliary',
               'outside_partition')}
    metadata = frontend_metadata if isinstance(frontend_metadata, dict) else {}
    return dict(schema_version=1, language=language, inventory_fingerprint=inventory_before['fingerprint'],
                files=rows, counts=counts, source_changes=changes,
                source_stable=not changes,
                scan_complete=inventory_before['scan_complete'] and inventory_after['scan_complete'],
                source_census_complete=False,
                truncated_by_method_limit=metadata.get('truncatedByMethodLimit') is True,
                frontend_census_complete=metadata.get('sourceCensusComplete') is True,
                unexpected_ast_files=sorted(outside),
                note='Represented means at least one exported AST entry names the file. '
                     'It does not establish complete parsing, translation or proof coverage.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('ast', type=Path)
    parser.add_argument('source', type=Path)
    parser.add_argument('language', choices=sorted(repository_inventory.ADAPTERS))
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    select_ast(args.ast, args.source, args.language, args.output)


if __name__ == '__main__':
    main()
