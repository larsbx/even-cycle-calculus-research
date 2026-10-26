from pathlib import Path
import json, subprocess, sys, tomllib
sys.path.insert(0, str(Path(__file__).resolve().parent))
from source import checked_source
root = Path(__file__).resolve().parents[1]
src = checked_source()
registry = tomllib.loads((root/'proof/claims.toml').read_text())
original = {c['id']: c for c in tomllib.loads((src/'proof/claims.toml').read_text())['claim']}
for c in registry['claim']:
    assert c['status'] in registry['meta']['status_values']
    if c['status'] == 'source_reference':
        assert c['source_status'] == original[c['source_id']]['status']
        assert c['source_commit'] == json.loads((root/'sources.lock.json').read_text())['commit']
actual = subprocess.check_output([sys.executable, str(root/'experiments/first.py')], cwd=root)
assert actual == (root/'conformance/first.json').read_bytes(), 'Receipt differs from replay'
print('PASS: source pins, preserved claim statuses, and exact finite receipt')
