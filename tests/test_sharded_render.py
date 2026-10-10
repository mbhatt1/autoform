"""`render_lean.py --shard-functions`: a large model rendered as parallel part modules.

Sharding is a layout change only. The unsharded render must stay byte-identical (every
tracked render pin is a hash of it), the sharded root must import exactly its parts, and
everything that binds evidence to "the model" must see every part.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
RENDER = ROOT / 'cartographer' / 'render_lean.py'
sys.path.insert(0, str(ROOT / 'scripts'))
import generated_module  # noqa: E402


def render(ast, out, module, *extra, env=None):
    run_env = dict(os.environ)
    run_env.pop('AUTOFORM_SHARD_FUNCTIONS', None)
    run_env.update(env or {})
    result = subprocess.run([sys.executable, str(RENDER), str(ast), str(out), module, *extra],
                            capture_output=True, text=True, env=run_env, timeout=600)
    assert result.returncode == 0, result.stderr
    return result.stdout


@pytest.fixture
def generated(tmp_path):
    out = tmp_path / 'Autoform' / 'Generated'
    out.mkdir(parents=True)
    return out


def test_unsharded_render_is_unchanged(generated):
    render(ROOT / 'ast-Stress.json', generated / 'Plain.lean', 'Plain')
    render(ROOT / 'ast-Stress.json', generated / 'Zero.lean', 'Plain', '--shard-functions', '0')
    render(ROOT / 'ast-Stress.json', generated / 'Big.lean', 'Plain', '--shard-functions', '1000')
    plain = (generated / 'Plain.lean').read_bytes()
    assert (generated / 'Zero.lean').read_bytes() == plain
    assert (generated / 'Big.lean').read_bytes() == plain   # under the threshold: one module
    assert not (generated / 'Plain').exists()


def test_sharded_root_imports_its_parts(generated):
    functions = json.loads((ROOT / 'ast-Stress.json').read_text())
    message = render(ROOT / 'ast-Stress.json', generated / 'Sharded.lean', 'Sharded',
                     '--shard-functions', '2')
    root = (generated / 'Sharded.lean').read_text()
    parts = sorted((generated / 'Sharded').glob('Part*.lean'))
    assert len(parts) >= 3 and '%d parts' % len(parts) in message
    assert generated_module.part_names(generated / 'Sharded.lean', 'Sharded') == [p.stem for p in parts]
    # Definitions live in the parts; the root assembles `program` from their names.
    assert 'def program : Program' in root and 'def moduleInits' in root
    assert ' : Func :=' not in root
    defs = sum(p.read_text().count(' : Func :=') for p in parts)
    assert defs >= len(functions)
    for part in parts:
        text = part.read_text()
        assert text.startswith('import Autoform.Lang.Core.Semantics\n')
        assert 'import Autoform.Generated' not in text      # independent: built in parallel
        assert 'namespace Autoform.Generated.Sharded' in text


def test_rerender_removes_stale_parts(generated):
    render(ROOT / 'ast-Stress.json', generated / 'Sharded.lean', 'Sharded', '--shard-functions', '2')
    assert list((generated / 'Sharded').glob('Part*.lean'))
    render(ROOT / 'ast-Stress.json', generated / 'Sharded.lean', 'Sharded')
    assert not (generated / 'Sharded').exists()
    assert generated_module.part_names(generated / 'Sharded.lean', 'Sharded') == []


def test_environment_selects_sharding(generated):
    render(ROOT / 'ast-Stress.json', generated / 'Env.lean', 'Env',
           env={'AUTOFORM_SHARD_FUNCTIONS': '2'})
    assert generated_module.part_names(generated / 'Env.lean', 'Env')


def test_model_digest_covers_every_part(generated):
    render(ROOT / 'ast-Stress.json', generated / 'Plain.lean', 'Plain')
    plain = generated / 'Plain.lean'
    assert generated_module.model_digest(plain) == hashlib.sha256(plain.read_bytes()).hexdigest()
    render(ROOT / 'ast-Stress.json', generated / 'Sharded.lean', 'Sharded', '--shard-functions', '2')
    root = generated / 'Sharded.lean'
    files = generated_module.model_files(root)
    assert files[0] == root and len(files) > 2
    before = generated_module.model_digest(root)
    files[-1].write_text(files[-1].read_text() + '\n-- edited\n')
    assert generated_module.model_digest(root) != before
    # A part on disk that the root does not import is not part of the model.
    shutil.copy(files[1], root.parent / 'Sharded' / 'Part9999.lean')
    assert root.parent / 'Sharded' / 'Part9999.lean' not in generated_module.model_files(root)


def test_invalid_shard_size_is_refused(generated):
    result = subprocess.run([sys.executable, str(RENDER), str(ROOT / 'ast-Stress.json'),
                             str(generated / 'X.lean'), 'X', '--shard-functions', '-1'],
                            capture_output=True, text=True, timeout=600)
    assert result.returncode != 0 and 'must be >= 0' in (result.stdout + result.stderr)
