#!/usr/bin/env python3
"""extract_sample_ast.py — extract a sample corpus from a parent AST.

Sample corpora (ast-V8BaseSample.json, ast-LinuxLibSample.json) are byte-identical subsets
of larger AST files that are gitignored as local build products. The samples exist so that
Autoform's root build can reference them in imports without requiring a fresh clone to
regenerate the multi-GB parent corpora.

This script reproduces a sample corpus deterministically from its parent. It exists so that
the Sample artifacts can carry provenance records naming this script as their "exporter"
(the analogue of cartographer/export_ast.sc for Joern exports) and the exact command that
regenerates them.

Extraction is by function name: entries whose `name` field matches the given list are
selected from the parent, sorted alphabetically by name, and written in the same JSON
format as the parent (compact, no indentation, separators=(', ', ': '), no trailing newline).

The samples are NOT call closures — ast-V8BaseSample.json contains exactly the 4 functions
named in Autoform/SpecsGen/V8BaseSample.lean, and none of those functions call other
functions in the corpus. ast-LinuxLibSample.json MAY contain call-closure entries, but the
extraction rule is the same: a fixed list of names, sorted alphabetically.

Usage:
    python3 scripts/extract_sample_ast.py ast-V8Base.json \\
        --names "v8.base.bits.SignedMod32:int32_t(int32_t,int32_t)" \\
                "v8.base.bits.SignedMod64:int64_t(int64_t,int64_t)" \\
                "v8.base.debug.BacktraceOutputHandler.OutputFileDescriptor:int()<const>" \\
                "v8.base.debug.EnableInProcessStackDumping<duplicate>0:bool()" \\
        --out ast-V8BaseSample.json

    # Or, read names from the generated Lean file's function references:
    python3 scripts/extract_sample_ast.py ast-V8Base.json \\
        --from-lean Autoform/Generated/V8BaseSample.lean \\
        --out ast-V8BaseSample.json

Exit 0 on success, 1 on name not found, 2 on usage error.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def extract_names_from_lean(lean_path: Path) -> list[str]:
    """Extract function names from a Generated/*.lean file.

    The generated Lean files define function records like:
        def f_v8_base_bits_SignedMod32_int32_t_int32_t_int32_t_ : Func := {
          name := "v8.base.bits.SignedMod32:int32_t(int32_t,int32_t)",
          ...
        }

    This extracts the names from the `name := "..."` lines.
    """
    if not lean_path.exists():
        raise FileNotFoundError(f"Lean file not found: {lean_path}")

    src = lean_path.read_text()
    # Match: name := "..." (allowing escaped quotes inside)
    names = re.findall(r'name := "([^"]+)"', src)
    return sorted(set(names))


def extract_sample(parent_path: Path, names: list[str]) -> list[dict]:
    """Extract entries from parent AST by name, sorted alphabetically."""
    if not parent_path.exists():
        raise FileNotFoundError(f"Parent AST not found: {parent_path}")

    parent = json.loads(parent_path.read_text())

    if not isinstance(parent, list):
        raise ValueError(f"Parent AST is not a JSON array: {parent_path}")

    # Build name set for O(1) lookup
    target_names = set(names)

    # Extract matching entries
    extracted = [entry for entry in parent if entry.get('name') in target_names]

    # Check all names were found
    found_names = {entry['name'] for entry in extracted}
    missing = target_names - found_names
    if missing:
        raise ValueError(f"Names not found in parent: {', '.join(sorted(missing))}")

    # Sort by name (this is how the tracked samples are ordered)
    extracted.sort(key=lambda e: e['name'])

    return extracted


def write_sample(entries: list[dict], out_path: Path) -> None:
    """Write sample AST in the canonical format: compact JSON, no trailing newline."""
    # The tracked format uses separators=(', ', ': ') and no indentation
    content = json.dumps(entries, separators=(', ', ': '))
    out_path.write_text(content)


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='\n'.join(__doc__.splitlines()[1:])
    )
    ap.add_argument('parent', type=Path, help='Parent AST file (e.g., ast-V8Base.json)')

    name_group = ap.add_mutually_exclusive_group(required=True)
    name_group.add_argument('--names', nargs='+', help='Function names to extract')
    name_group.add_argument('--from-lean', type=Path, metavar='FILE',
                           help='Extract names from Generated/*.lean file')

    ap.add_argument('--out', type=Path, required=True,
                   help='Output sample AST file')
    ap.add_argument('--verify', type=Path, metavar='FILE',
                   help='Verify against existing file (check SHA256 match)')

    args = ap.parse_args()

    # Resolve paths relative to repo root
    parent_path = args.parent if args.parent.is_absolute() else REPO / args.parent
    out_path = args.out if args.out.is_absolute() else REPO / args.out

    try:
        # Get function names
        if args.from_lean:
            lean_path = args.from_lean if args.from_lean.is_absolute() else REPO / args.from_lean
            print(f"Extracting names from {lean_path.relative_to(REPO)}...", file=sys.stderr)
            names = extract_names_from_lean(lean_path)
            print(f"Found {len(names)} function name(s)", file=sys.stderr)
        else:
            names = args.names
            print(f"Extracting {len(names)} named function(s)...", file=sys.stderr)

        # Extract sample
        print(f"Reading parent AST from {parent_path.relative_to(REPO) if parent_path.is_relative_to(REPO) else parent_path}...", file=sys.stderr)
        entries = extract_sample(parent_path, names)
        print(f"Extracted {len(entries)} entries", file=sys.stderr)

        # Verify if requested
        if args.verify:
            verify_path = args.verify if args.verify.is_absolute() else REPO / args.verify
            if not verify_path.exists():
                print(f"extract_sample_ast: --verify file does not exist: {verify_path}", file=sys.stderr)
                return 2

            # Generate what we would write
            test_content = json.dumps(entries, separators=(', ', ': '))
            test_hash = hashlib.sha256(test_content.encode()).hexdigest()

            # Compare to existing
            actual_content = verify_path.read_bytes()
            actual_hash = hashlib.sha256(actual_content).hexdigest()

            if test_hash == actual_hash:
                print(f"✓ VERIFIED: extracted sample matches {verify_path.relative_to(REPO) if verify_path.is_relative_to(REPO) else verify_path} byte-exactly", file=sys.stderr)
                print(f"  SHA256: {actual_hash}", file=sys.stderr)
            else:
                print(f"✗ MISMATCH: extracted sample differs from {verify_path.relative_to(REPO) if verify_path.is_relative_to(REPO) else verify_path}", file=sys.stderr)
                print(f"  Expected: {actual_hash} ({len(actual_content)} bytes)", file=sys.stderr)
                print(f"  Got:      {test_hash} ({len(test_content)} bytes)", file=sys.stderr)
                return 1

        # Write output
        print(f"Writing {out_path.relative_to(REPO) if out_path.is_relative_to(REPO) else out_path}...", file=sys.stderr)
        write_sample(entries, out_path)

        # Report hash
        written_hash = hashlib.sha256(out_path.read_bytes()).hexdigest()
        print(f"✓ Wrote {len(entries)} entries ({out_path.stat().st_size} bytes)", file=sys.stderr)
        print(f"  SHA256: {written_hash}", file=sys.stderr)

        return 0

    except (FileNotFoundError, ValueError) as e:
        print(f"extract_sample_ast: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"extract_sample_ast: unexpected error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 2


if __name__ == '__main__':
    sys.exit(main())
