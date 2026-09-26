#!/usr/bin/env python3
"""dwarf_signature.py -- a function's parameter and return shapes, read from DWARF.

    dwarf_signature.py OBJECT SYMBOL        # prints the signature as JSON

The machine-level regression search (`scripts/machine_regress.py`) and its kernel
checks need to know how many integer arguments a function
takes, how wide each one is, whether it is signed, and how wide the return value
is. Guessing that from the machine code is unsound (a callee may ignore an
argument register), so it is read from the compiler's debug information instead.

Only scalar integer-class shapes are classified as `int` or `pointer`; anything
else (floating point, aggregates passed by value, variadic tails) is reported with
its own `kind` so a caller can refuse it rather than silently mis-model it.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, field
import json
from pathlib import Path
import sys

# DW_ATE_* encodings (DWARF 5 §7.8).
_SIGNED = {0x05, 0x06, 0x0d}          # signed, signed_char, signed_fixed
_UNSIGNED = {0x02, 0x07, 0x08, 0x0e, 0x10}  # boolean, unsigned, unsigned_char, unsigned_fixed, UTF
_FLOAT = {0x03, 0x04, 0x09}           # complex_float, float, imaginary_float
_QUALIFIERS = {'DW_TAG_typedef', 'DW_TAG_const_type', 'DW_TAG_volatile_type',
               'DW_TAG_restrict_type', 'DW_TAG_atomic_type'}


class SignatureError(ValueError):
    """The object has no usable DWARF description of the requested function."""


@dataclass
class Value:
    name: str | None
    size: int            # bytes; 0 for void
    signed: bool
    kind: str            # int | pointer | bool | enum | float | aggregate | void | unknown
    type_name: str | None = None

    @property
    def bits(self):
        return 8 * self.size


@dataclass
class Signature:
    name: str
    params: list[Value]
    ret: Value
    variadic: bool = False
    file: str | None = None
    line: int | None = None
    notes: list[str] = field(default_factory=list)

    def integer_class(self):
        """True when every parameter and the return fit AAPCS64 general registers."""
        ok = {'int', 'pointer', 'bool', 'enum'}
        return (not self.variadic and len(self.params) <= 8
                and all(p.kind in ok and 1 <= p.size <= 8 for p in self.params)
                and (self.ret.kind == 'void' or (self.ret.kind in ok and 1 <= self.ret.size <= 8)))

    def to_json(self):
        return asdict(self)

    @classmethod
    def from_json(cls, data):
        return cls(name=data['name'], params=[Value(**p) for p in data['params']],
                   ret=Value(**data['ret']), variadic=data.get('variadic', False),
                   file=data.get('file'), line=data.get('line'), notes=list(data.get('notes', [])))


def _attr(die, name):
    attribute = die.attributes.get(name)
    return None if attribute is None else attribute.value


def _name(die):
    value = _attr(die, 'DW_AT_name')
    return value.decode('utf-8', 'replace') if isinstance(value, bytes) else value


def _origin(die):
    """Follow abstract_origin / specification to the DIE that carries names and types."""
    seen = 0
    while seen < 8:
        for key in ('DW_AT_abstract_origin', 'DW_AT_specification'):
            if key in die.attributes:
                die = die.get_DIE_from_attribute(key)
                break
        else:
            return die
        seen += 1
    return die


def _lookup(die, name):
    """An attribute from this DIE or the declaration/abstract DIEs it refines."""
    current, seen = die, 0
    while current is not None and seen < 8:
        if name in current.attributes:
            return current
        nxt = None
        for key in ('DW_AT_abstract_origin', 'DW_AT_specification'):
            if key in current.attributes:
                nxt = current.get_DIE_from_attribute(key)
                break
        current, seen = nxt, seen + 1
    return None


def _classify(type_die, name):
    """Map a DW_AT_type chain to a Value."""
    type_name = None
    seen = 0
    while type_die is not None and type_die.tag in _QUALIFIERS and seen < 32:
        if type_die.tag == 'DW_TAG_typedef' and type_name is None:
            type_name = _name(type_die)
        if 'DW_AT_type' not in type_die.attributes:
            return Value(name, 0, False, 'void', type_name or 'void')
        type_die = type_die.get_DIE_from_attribute('DW_AT_type')
        seen += 1
    if type_die is None:
        return Value(name, 0, False, 'void', 'void')
    tag = type_die.tag
    type_name = type_name or _name(type_die)
    size = _attr(type_die, 'DW_AT_byte_size')
    if tag == 'DW_TAG_base_type':
        encoding = _attr(type_die, 'DW_AT_encoding')
        if encoding in _FLOAT:
            return Value(name, size or 0, True, 'float', type_name)
        if encoding == 0x02:
            return Value(name, size or 1, False, 'bool', type_name)
        if encoding in _SIGNED:
            return Value(name, size or 0, True, 'int', type_name)
        if encoding in _UNSIGNED:
            return Value(name, size or 0, False, 'int', type_name)
        return Value(name, size or 0, False, 'unknown', type_name)
    if tag in ('DW_TAG_pointer_type', 'DW_TAG_reference_type', 'DW_TAG_rvalue_reference_type'):
        return Value(name, size or 8, False, 'pointer', type_name or 'pointer')
    if tag == 'DW_TAG_enumeration_type':
        signed = False
        if 'DW_AT_type' in type_die.attributes:
            signed = _classify(type_die.get_DIE_from_attribute('DW_AT_type'), None).signed
        return Value(name, size or 4, signed, 'enum', type_name)
    if tag in ('DW_TAG_structure_type', 'DW_TAG_union_type', 'DW_TAG_class_type', 'DW_TAG_array_type'):
        return Value(name, size or 0, False, 'aggregate', type_name)
    return Value(name, size or 0, False, 'unknown', type_name or tag)


def _signature(die, symbol):
    typed = _lookup(die, 'DW_AT_type')
    ret = (_classify(typed.get_DIE_from_attribute('DW_AT_type'), None) if typed is not None
           else Value(None, 0, False, 'void', 'void'))
    # A concrete out-of-line instance lists its own formal parameters (pointing at
    # the abstract ones); a plain definition lists them directly. Prefer the DIE
    # that actually has children, then fall back to the declaration.
    params, variadic = [], False
    for candidate in (die, _origin(die)):
        children = [c for c in candidate.iter_children()
                    if c.tag in ('DW_TAG_formal_parameter', 'DW_TAG_unspecified_parameters')]
        if children:
            for child in children:
                if child.tag == 'DW_TAG_unspecified_parameters':
                    variadic = True
                    continue
                named = _lookup(child, 'DW_AT_name')
                typed_param = _lookup(child, 'DW_AT_type')
                params.append(_classify(
                    typed_param.get_DIE_from_attribute('DW_AT_type') if typed_param is not None else None,
                    _name(named) if named is not None else None))
            break
    decl = _lookup(die, 'DW_AT_decl_line')
    file_die = _lookup(die, 'DW_AT_decl_file')
    return Signature(name=symbol, params=params, ret=ret, variadic=variadic,
                     line=_attr(decl, 'DW_AT_decl_line') if decl is not None else None,
                     file=None if file_die is None else str(_attr(file_die, 'DW_AT_decl_file')))


def read_signature(path, symbol):
    """The Signature of `symbol` in the ELF object or executable at `path`."""
    from elftools.elf.elffile import ELFFile

    path = Path(path)
    with path.open('rb') as stream:
        elf = ELFFile(stream)
        if not elf.has_dwarf_info():
            raise SignatureError(f'{path}: no DWARF debug information (compile with -g)')
        dwarf = elf.get_dwarf_info()
        best = None
        for unit in dwarf.iter_CUs():
            for die in unit.iter_DIEs():
                if die.tag != 'DW_TAG_subprogram':
                    continue
                named = _lookup(die, 'DW_AT_name')
                linkage = _lookup(die, 'DW_AT_linkage_name')
                names = {_name(named) if named is not None else None}
                if linkage is not None:
                    value = _attr(linkage, 'DW_AT_linkage_name')
                    names.add(value.decode() if isinstance(value, bytes) else value)
                if symbol not in names:
                    continue
                # A definition with code (low_pc) beats a bare declaration.
                has_code = 'DW_AT_low_pc' in die.attributes or 'DW_AT_ranges' in die.attributes
                if best is None or (has_code and not best[0]):
                    best = (has_code, die)
                if has_code:
                    break
            if best is not None and best[0]:
                break
        if best is None:
            raise SignatureError(f'{path}: no DWARF subprogram named {symbol!r}')
        signature = _signature(best[1], symbol)
        if not best[0]:
            signature.notes.append('only a declaration was found; the function may be inlined everywhere')
        return signature


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    parser.add_argument('object', type=Path)
    parser.add_argument('symbol')
    args = parser.parse_args(argv)
    try:
        signature = read_signature(args.object, args.symbol)
    except (SignatureError, OSError) as exc:
        print(f'dwarf_signature: {exc}', file=sys.stderr)
        return 2
    print(json.dumps(signature.to_json(), indent=2))
    return 0


if __name__ == '__main__':
    sys.exit(main())
