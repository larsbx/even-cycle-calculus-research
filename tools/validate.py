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
lower = subprocess.check_output([sys.executable, str(root/'experiments/lower_support.py')], cwd=root)
assert lower == (root/'conformance/lower-support.json').read_bytes(), 'Lower-support receipt differs'
near = subprocess.check_output([sys.executable, str(root/'experiments/near_top.py')], cwd=root)
assert near == (root/'conformance/near-top.json').read_bytes(), 'Near-top receipt differs'
inversion = subprocess.check_output([sys.executable, str(root/'experiments/partition_inversion.py')], cwd=root)
assert inversion == (root/'conformance/partition-inversion.json').read_bytes(), 'Direct quotient-inversion receipt differs'
histogram = subprocess.check_output([sys.executable, str(root/'experiments/partition_histogram.py')], cwd=root)
assert histogram == (root/'conformance/partition-histogram.json').read_bytes(), 'Histogram-inversion receipt differs'
repeated = subprocess.check_output([sys.executable, str(root/'experiments/repeated_edge.py')], cwd=root)
assert repeated == (root/'conformance/repeated-edge.json').read_bytes(), 'Repeated-edge receipt differs'
even_edges = subprocess.check_output([sys.executable, str(root/'experiments/even_edge_resolutions.py')], cwd=root)
assert even_edges == (root/'conformance/even-edge-resolutions.json').read_bytes(), 'Even-edge resolution receipt differs'
subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-v'], cwd=root, check=True)
print('PASS: source pins, preserved statuses, all seven exact receipts, and coefficient/graph regressions')
