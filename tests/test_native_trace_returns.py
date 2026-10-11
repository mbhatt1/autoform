"""Exercise real CPython trace events, including handled exceptions and unwinding."""
import sys


SOURCE = '''
def caught_none():
    try:
        raise ValueError('handled')
    except ValueError:
        return None

def caught_fallthrough():
    try:
        raise KeyError('handled')
    except KeyError:
        pass

def final_return():
    try:
        raise ValueError('suppressed')
    finally:
        return None

def final_unwind():
    try:
        raise ValueError('escapes')
    finally:
        value = 1

def nested_unwind():
    try:
        raise ValueError('escapes')
    finally:
        try:
            raise KeyError('handled')
        except KeyError:
            pass

def value_return():
    return 11

def yields():
    yield 7
    yield 9

async def coroutine():
    return 13
'''


def test_native_trace_returns_and_gaps(tmp_path, monkeypatch, differential):
    path = tmp_path / 'trace_cases.py'
    path.write_text(SOURCE)
    namespace = {}
    exec(compile(SOURCE, str(path), 'exec'), namespace)
    names = ['caught_none', 'caught_fallthrough', 'final_return', 'final_unwind',
             'nested_unwind', 'value_return', 'yields', 'coroutine']
    keys = {name: 'trace_cases.py:<module>.' + name for name in names}
    index = differential.build_lineno_index(str(tmp_path), ['trace_cases.py'])

    def suite(_):
        for name in names[:6]:
            try:
                namespace[name]()
            except (ValueError, KeyError):
                pass
        assert list(namespace['yields']()) == [7, 9]
        task = namespace['coroutine']()
        try:
            task.send(None)
        except StopIteration:
            pass
        return 0

    monkeypatch.setattr(differential, 'run_suite', suite)
    stats = {'skip_unencodable_args': 0, 'skip_unencodable_ret': 0}
    def previous_trace(frame, event, arg):
        return previous_trace
    previous = sys.gettrace()
    try:
        sys.settrace(previous_trace)
        records = differential.trace_tests(str(tmp_path), [str(tmp_path)], index,
            set(keys.values()), 5, stats, {key: [] for key in keys.values()})
        assert sys.gettrace() is previous_trace
    finally:
        sys.settrace(previous)
    actual = {record['name']: record['outcome'] for record in records}
    assert actual == {
        keys['caught_none']: ('val', ('unit',)),
        keys['caught_fallthrough']: ('val', ('unit',)),
        keys['final_return']: ('val', ('unit',)),
        keys['final_unwind']: ('exn', 'ValueError'),
        keys['value_return']: ('val', ('int', 11)),
    }
    assert stats['skip_ambiguous_trace_return'] == 1
    assert stats['skip_suspended_frame'] >= 2
    assert stats['test_runs'] == [{'dir': str(tmp_path), 'rc': 0}]


CLOSURE_SOURCE = '''
def outer(default):
    def inner(name):
        if name is None:
            return default
        return name
    return inner

def plain(x):
    return x
'''


def test_nested_function_reading_its_enclosing_scope_is_refused(tmp_path, monkeypatch,
                                                                differential):
    """A traced call of a closure body carries the arguments, not the captured cells, so
    the model would read the free name as an unbound global (Jinja2
    `select_autoescape.autoescape`: CPython 'STRING', model `unit`). It is refused and
    counted; a plain function in the same file is still recorded."""
    path = tmp_path / 'closures.py'
    path.write_text(CLOSURE_SOURCE)
    namespace = {}
    exec(compile(CLOSURE_SOURCE, str(path), 'exec'), namespace)
    index = differential.build_lineno_index(str(tmp_path), ['closures.py'])
    inner = 'closures.py:<module>.outer.inner'
    plain = 'closures.py:<module>.plain'

    def suite(_):
        namespace['outer']('STRING')(None)
        namespace['plain'](3)
        return 0

    monkeypatch.setattr(differential, 'run_suite', suite)
    stats = {'skip_unencodable_args': 0, 'skip_unencodable_ret': 0}
    previous = sys.gettrace()
    try:
        records = differential.trace_tests(str(tmp_path), [str(tmp_path)], index,
            {inner, plain}, 5, stats, {inner: ['name'], plain: ['x']})
    finally:
        sys.settrace(previous)
    assert [r['name'] for r in records] == [plain]
    assert stats['skip_closure_captures'] == 1
    assert stats['closure_capture_detail'] == {inner: ['default']}
