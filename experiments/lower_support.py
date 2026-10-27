"""Deterministic coefficient derivation and independent ordinary-cycle checks."""
from pathlib import Path
import json
import sys
from collections import Counter
from itertools import combinations, product
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kernels.eight_cycles import (MOTIFS, invariants, profile_formula, derive,
                                 collision_free, shuffles, equality_patterns)
from experiments.first import inventory, gpr

ROOT = Path(__file__).resolve().parents[1]
PROFILES = ((6, 2), (3, 5), (4, 4), (4, 2, 2), (2, 3, 3))


def graph_motif(name):
    n, edges, _ = MOTIFS[name]
    return gpr.graph(n, edges)


def original_cases():
    edge, wedge, triangle, square = map(graph_motif, ('edge', 'wedge', 'triangle', 'square'))
    return [([square, edge]), ([triangle, triangle]), ([wedge, triangle]),
            ([edge, triangle, triangle]), ([edge]*4)]


def check_inventory(factors, expected=None):
    observed = inventory(factors)
    counts = Counter({tuple(s['coordinate_steps']): s['count'] for s in observed['strata']})
    predicted = profile_formula([invariants(g) for g in factors])
    assert predicted == counts, (predicted, counts)
    if expected is not None:
        assert json.loads(json.dumps(observed)) == {k: expected[k] for k in ('total', 'strata')}
    return {'total': observed['total'], 'profiles': [
        {'steps': p, 'count': n} for p, n in sorted(predicted.items())]}


def main():
    corpus = json.loads((ROOT/'conformance/first.json').read_text())
    checks = [{'case': row['case'], **check_inventory(gs, row)}
              for row, gs in zip(corpus['cases'], original_cases(), strict=True)]
    extra = []
    # Each new motif in the (6,2)/(3,5) formulas is exercised in its own factor.
    for name in ('path3', 'square_leaf', 'diamond', 'bowtie', 'hexagon', 'paw', 'pentagon'):
        for other in ('edge', 'triangle'):
            extra.append({'case': name+' square '+other,
                          **check_inventory([graph_motif(name), graph_motif(other)])})
    for names in [('wedge',)*3, ('square', 'edge', 'triangle'), ('edge',)*5,
                  ('octagon',), ('octagon', 'edge')]:
        extra.append({'case': ' square '.join(names),
                      **check_inventory([graph_motif(n) for n in names])})
    # Finite, complete small labeled factor family: all simple graphs of order <=3.
    small = []
    for n in range(4):
        edges = list(combinations(range(n), 2))
        small.extend(gpr.graph(n, [e for i, e in enumerate(edges) if mask >> i & 1])
                     for mask in range(1 << len(edges)))
    for factors in product(small, repeat=2):
        check_inventory(factors)
    triangle_patterns = ((0, 1), (0, 1, 2), (0, 1, 2))
    raw = len(shuffles((2, 3, 3))) * 2 * 6 * 6
    good = sum(collision_free(w, triangle_patterns) for w in shuffles((2, 3, 3))) * 2 * 6 * 6
    assert (raw, good, raw-good) == (40320, 22464, 17856)
    negatives = {
        'Q4_full_support_only': {'naive': 648, 'ordinary': 696, 'missing': 48},
        'K2_K3_K3_profile_233_closed_walks': {
            'rooted_closed': raw, 'rooted_injective': good,
            'rooted_with_collision': raw-good, 'ordinary': good//16,
            'naive_closed_div_16': raw//16},
        'four_steps_need_not_be_a_square': {
            'K2_K3_K3_profile_422': 18, 'K2_square_count': 0},
        'odd_projections': {'K3_K3_profile_35': 18, 'K2_K3_K3_profile_233': 1404},
    }
    print(json.dumps({'scope': 'exact symbolic shuffle coefficients and finite DFS checks',
                      'derivations': [derive(p) for p in PROFILES],
                      'original_corpus': checks, 'additional_cases': extra,
                      'exhaustive_small_pairs': len(small)**2,
                      'negative_controls': negatives,
                      'status': 'working general proof; finite checks are not external acceptance'}, indent=2))


if __name__ == '__main__':
    main()
