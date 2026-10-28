"""Compile all Lean components and enforce each declaration's exact axiom set."""
from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
LEAN = os.environ.get('LEAN_BINARY', 'lean')
EXPECTED = {
    **{'ECC.'+n: {'propext'} for n in (
        'paired_triangle_coefficient', 'four_step_coefficients',
        'two_four_step_coefficients', 'six_two_coefficients', 'three_five_coefficients')},
    **{'ECC.CollisionBridge.'+n: {'Quot.sound'} for n in (
        'decode_equal_iff', 'trace_injective_iff', 'decoded_cycle_iff', 'assignments_recovered')},
    **{'ECC.CollisionBridge.'+n: set() for n in (
        'coordinate_step_iff', 'coordinate_axis_unique', 'cartesian_adj_preserved', 'used_coordinate_iff')},
    'ECC.CollisionControls.fold_edges_preserved': set(),
    **{'ECC.CollisionControls.'+n: {'propext', 'Quot.sound'} for n in (
        'square_is_cycle', 'folded_trace_not_injective', 'unseen_assignments_injective',
        'unseen_assignments_same_trace', 'unseen_assignments_differ')},
    **{'ECC.CanonicalTrace.'+n: {'propext', 'Quot.sound'} for n in (
        'scan_spec', 'first_le', 'first_value', 'first_minimal',
        'first_eq_of_value_eq', 'first_eq_iff', 'first_idempotent',
        'realize_extract', 'extract_representative', 'realize_injective',
        'first_injective_relabeling', 'first_equality_relation',
        'normalized_shape_recovered', 'canonical_shape_unique', 'extract_surjective')},
    **{'ECC.CanonicalControls.'+n: {'propext', 'Quot.sound'} for n in (
        'first_positions', 'positions_are_not_ordinals', 'noninjective_relabel_changes_first')},
}


def main():
    version = subprocess.check_output([LEAN, '--version'], cwd=ROOT, text=True).strip()
    expected_version = (ROOT/'lean-toolchain').read_text().strip().rsplit(':', 1)[1].removeprefix('v')
    if not version.startswith('Lean (version '+expected_version+','):
        raise RuntimeError('Compiler differs from lean-toolchain: '+version)
    print(version, flush=True)
    actual = {}
    pattern = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)$")
    with tempfile.TemporaryDirectory(prefix='ecc-lean-') as build:
        env = dict(os.environ, LEAN_PATH=build)
        for args in [('Shuffle.lean',), ('-o', str(Path(build)/'CollisionBridge.olean'), 'CollisionBridge.lean'),
                     ('CollisionControls.lean',),
                     ('-o', str(Path(build)/'CanonicalTrace.olean'), 'CanonicalTrace.lean'),
                     ('CanonicalControls.lean',)]:
            run = subprocess.run([LEAN, *args], cwd=ROOT, env=env, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(run.stdout, end='', flush=True)
            run.check_returncode()
            for line in run.stdout.splitlines():
                match = pattern.fullmatch(line)
                if not match:
                    raise RuntimeError('Unexpected Lean output: '+line)
                name, axioms = match.groups()
                if name in actual:
                    raise RuntimeError('Duplicate axiom declaration: '+name)
                actual[name] = {a.strip() for a in axioms.split(',')} if axioms else set()
    if actual != EXPECTED:
        raise RuntimeError('Axiom audit differs: '+repr(actual))
    print('PASS: 37 exact declaration audits; no placeholders, choice, or native-evaluation axioms')


if __name__ == '__main__':
    main()
