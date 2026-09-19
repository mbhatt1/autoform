"""Nested source programs must not depend on the Python process's stack settings."""
import json
import math
import subprocess
import sys
from pathlib import Path

import pytest
from hypothesis import given, settings, strategies as st

from conftest import SCRIPTS, load


@pytest.fixture(scope='module')
def reader():
    return load(str(Path(SCRIPTS)/'deep_json.py'), 'af_deep_json')


values = st.recursive(st.none() | st.booleans() | st.integers() |
                      st.floats(allow_nan=False, allow_infinity=False) | st.text(),
                      lambda inner: st.lists(inner, max_size=5) |
                      st.dictionaries(st.text(), inner, max_size=5), max_leaves=30)


@given(values)
@settings(max_examples=150)
def test_matches_standard_json_value_semantics(reader, value):
    for separators in [(',', ':'), (', ', ': ')]:
        text = json.dumps(value, ensure_ascii=True, separators=separators)
        assert reader.loads(text) == json.loads(text)


@pytest.mark.parametrize('text', [
    '', ' ', '[', '{', '[1,]', '{"a":1,}', '{1:2}', '{"a" 2}', '[1 2]',
    '{"a":}', 'true false', '01', '1e', 'undefined', '"bad\nstring"',
    '"bad\\x"', '"\\u00zz"', '[}', '{]', '[,1]', '{,"a":1}',
    '\ufeff[]', '[truex]', '{"a":1 "b":2}', '[[1],]', '{"a":[1,]}',
])
def test_invalid_json_remains_an_error(reader, text):
    with pytest.raises(json.JSONDecodeError):
        json.loads(text)
    with pytest.raises(json.JSONDecodeError):
        reader.loads(text)


def test_duplicate_keys_numbers_and_escapes_follow_standard_decoder(reader):
    text = '{"a":1,"a":2,"s":"\\ud83d\\ude00\\n\\t","n":-123456789012345678901234567890,"f":1.25e-7}'
    assert reader.loads(text) == json.loads(text)
    assert math.isnan(reader.loads('NaN'))
    assert reader.loads('Infinity') == float('inf')
    assert reader.loads('-Infinity') == -float('inf')


def test_deep_json_at_default_stack_and_recursion_limit(tmp_path):
    path=tmp_path/'deep.json'
    path.write_text('[' * 12000 + '{"marker":"last"}' + ']' * 12000)
    # A fresh interpreter catches regressions hidden by another test raising the
    # process-wide recursion limit before this reader is invoked.
    driver='''import sys
sys.path.insert(0, sys.argv[1])
import deep_json
assert sys.getrecursionlimit() == 1000
value=deep_json.load(sys.argv[2])
for _ in range(12000): value=value[0]
assert value == {'marker':'last'}
assert sys.getrecursionlimit() == 1000
'''
    result=subprocess.run([sys.executable,'-c',driver,SCRIPTS,str(path)],
                          capture_output=True,text=True,timeout=30)
    assert result.returncode == 0, result.stdout+result.stderr


def test_deep_ast_reporting_and_specification_analysis(tmp_path):
    path=tmp_path/'ast-Deep.json'
    body='{"k":"seq","a":{"k":"skip"},"b":' * 1400
    body+='{"k":"raise","e":{"k":"str","v":"tryFinally"}}' + '}' * 1400
    path.write_text('[{"name":"f","file":"f.c","params":[],"body":'+body+'}]')
    driver='''import os,sys
os.environ['AUTOFORM_NO_REEXEC']='1'
sys.path.insert(0,sys.argv[1])
import deep_json,sacm,synth_specs,scale_test,check_docs,core_oracle
assert sys.getrecursionlimit()==1000
funcs=deep_json.load(sys.argv[2])
body=funcs[0]['body']
assert not synth_specs.has_try_finally(body), 'a string literal is not a finally statement'
assert not synth_specs.writes_heap(body)
assert not synth_specs.can_hole_or_loop(body)
assert synth_specs.mine_artifacts(funcs,sys.argv[3])['raises']==1
assert sacm.analyse_ast(sacm.load_json(sys.argv[2]))[:2]==(1,1)
assert check_docs.ast_function_count(sys.argv[2])==1
assert scale_test.ast_stats(sys.argv[2])['ast_max_depth']>1000
assert core_oracle.count_ast_holes(funcs)==0
assert sys.getrecursionlimit()==1000
'''
    result=subprocess.run([sys.executable,'-c',driver,SCRIPTS,str(path),str(tmp_path)],
                          capture_output=True,text=True,timeout=30)
    assert result.returncode == 0, result.stdout+result.stderr


def test_deep_runtime_provenance_is_validated_without_stack_tuning(tmp_path):
    driver='''import json,sys
from pathlib import Path
sys.path.insert(0,sys.argv[1])
import runtime_backends as rb
root=Path(sys.argv[2]); ast=root/'ast.json'; report=root/'conformance.json'; model=root/'Model.lean'
(root/'f.c').write_text('int f(void) { return 1; }')
model.write_text('-- fixture: provenance validation only')
ast.write_text('[{"name":"f","file":"f.c","body":'+ '['*1400+'0'+']'*1400+'}]')
funcs=[dict(name='f',file='f.c')]
data=dict(module='Deep',build_stable=True,divergences=0,runtime_cases=[dict(name='f',comparison='agree')],
 provenance=dict(ast_sha256=rb.sha256(ast),generated_sha256=rb.sha256(model),
 source_sha256=rb.source_fingerprints(root,funcs),semantics_sha256=rb.semantics_fingerprints()))
report.write_text(json.dumps(data))
assert len(rb.load_observations(report,ast,root,'Deep',model)[0])==1
(root/'f.c').write_text('int f(void) { return 2; }')
try: rb.load_observations(report,ast,root,'Deep',model)
except ValueError: pass
else: raise AssertionError('changed source was accepted')
assert sys.getrecursionlimit()==1000
'''
    result=subprocess.run([sys.executable,'-c',driver,SCRIPTS,str(tmp_path)],
                          capture_output=True,text=True,timeout=30)
    assert result.returncode == 0, result.stdout+result.stderr
