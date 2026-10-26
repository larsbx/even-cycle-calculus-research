"""Load exact pinned source inputs without copying theorem authority."""
from pathlib import Path
import hashlib, json, os, subprocess

def checked_source():
    root = Path(__file__).resolve().parents[1]
    lock = json.loads((root / 'sources.lock.json').read_text())
    src = Path(os.environ.get('GPR_SOURCE', root / '.deps/graph-product-ring-research')).resolve()
    head = subprocess.check_output(['git', '-C', str(src), 'rev-parse', 'HEAD'], text=True).strip()
    if head != lock['commit']:
        raise RuntimeError('Source HEAD differs from sources.lock.json')
    for path, digest in lock['files'].items():
        if hashlib.sha256((src / path).read_bytes()).hexdigest() != digest:
            raise RuntimeError('Pinned source digest mismatch: ' + path)
    return src
