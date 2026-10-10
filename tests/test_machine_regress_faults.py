"""A fault in one commit and a value in the other is a machine-level divergence.

Before 2026-09-26 the lifted-model search only compared two returned values, so the
kernel's gcd division-by-zero fix (e96875677fb2) compared as "no divergence": the old
code traps on `gcd(7, 0)`, and a trap was dropped rather than reported. Out-of-fuel is
not a fault; a function that merely runs long must not be reported as crashing.
"""
from __future__ import annotations

import pytest

from test_machine_regress import needs_lean, needs_toolchain, regress

BEFORE = '''#include <linux/kernel.h>
unsigned long gcd(unsigned long a, unsigned long b)
{
	unsigned long r;
	if (a < b) { r = a; a = b; b = r; }
	while ((r = a % b) != 0) { a = b; b = r; }
	return b;
}
'''
AFTER = BEFORE.replace('while ((r = a % b)', 'if (!b)\n\t\treturn a;\n\twhile ((r = a % b)')


@needs_toolchain
@needs_lean
def test_division_by_zero_fix_is_a_kernel_checked_fault_divergence(tmp_path):
    for name, text in (('base', BEFORE), ('head', AFTER)):
        (tmp_path / name).mkdir()
        (tmp_path / name / 'gcd.c').write_text(text)
    report = regress.run(tmp_path / 'base', tmp_path / 'head', ['gcd.c'], ['gcd'], target='x86_64',
                         out=tmp_path / 'out', native=False, limit=10, given=[(7, 0)])
    record = report['functions'][0]
    assert record['status'] == 'diverges'
    witness = next(w for w in record['witnesses'] if w['inputs'] == [7, 0])
    assert witness['kind'] == 'fault' and witness['kernel_checked']
    assert witness['base'] == 'error: division-by-zero' and witness['head'] == 7
    assert 'Fault_base' in witness['lean_checks']['base'] and 'Check_head' in witness['lean_checks']['head']


def test_out_of_fuel_is_not_a_fault():
    class Model:
        def __init__(self, value):
            self.value = value

        def evaluate(self, batch):
            return [self.value for _ in batch]

    found, _ = regress.model_divergences(Model('error: out-of-fuel'), Model(3), [(1,), (2,)], 5)
    assert found == []
    found, _ = regress.model_divergences(Model('error: division-by-zero'), Model(3), [(1,)], 5)
    assert found == [((1,), 'error: division-by-zero', 3)]


if __name__ == '__main__':
    pytest.main([__file__])
