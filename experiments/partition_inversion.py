"""Compare the independent quotient oracle with every existing corpus case."""
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from kernels.partition_inversion import inventory, partitions, quotient_terms
# Only the comparison side uses motif data/formulas or the old DFS.
from kernels.eight_cycles import MOTIFS, invariants, profile_formula
from experiments.first import inventory as dfs_inventory


def graph(n, edges):
    g = [set() for _ in range(n)]
    for u, v in edges:
        g[u].add(v)
        g[v].add(u)
    return g


def motif(name):
    n, edges, _ = MOTIFS[name]
    return graph(n, edges)


def serial(counts):
    return [{'steps': p, 'count': c} for p, c in sorted(counts.items()) if c]


def compare(factors, expected=None):
    actual = inventory(factors)
    dfs = dfs_inventory(factors)
    dfs_profiles = Counter({tuple(r['coordinate_steps']): r['count'] for r in dfs['strata']})
    formula = profile_formula([invariants(g) for g in factors])
    assert actual['ordinary'] == dfs_profiles == formula, (actual, dfs, formula)
    if expected is not None:
        recorded = Counter({tuple(r['steps']): r['count'] for r in expected['profiles']})
        assert actual['ordinary'] == recorded
        assert sum(recorded.values()) == expected['total']
    return {'total': sum(actual['ordinary'].values()),
            'profiles': serial(actual['ordinary']),
            'rooted_closed': serial(actual['rooted_closed']),
            'rooted_injective': serial(actual['rooted_injective'])}


def main():
    lower = json.loads((ROOT/'conformance/lower-support.json').read_text())
    originals = [('square', 'edge'), ('triangle', 'triangle'), ('wedge', 'triangle'),
                 ('edge', 'triangle', 'triangle'), ('edge',)*4]
    rows = []
    for names, expected in zip(originals, lower['original_corpus'], strict=True):
        rows.append({'case': expected['case'], **compare([motif(n) for n in names], expected)})
    extras = []
    for expected in lower['additional_cases']:
        names = expected['case'].split(' square ')
        extras.append({'case': expected['case'], **compare([motif(n) for n in names], expected)})
    small = []
    for n in range(4):
        edges = list(combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            small.append((n, mask, graph(n, [e for i, e in enumerate(edges) if mask >> i & 1])))
    pairs = []
    for (n, mask, g), (k, bits, h) in product(small, repeat=2):
        row = compare([g, h])
        pairs.append({'orders': [n, k], 'edge_masks': [mask, bits],
                      'total': row['total'], 'profiles': row['profiles']})
    assert len(pairs) == lower['exhaustive_small_pairs']
    # Additional boundary cases exercise isolated fibers, disconnection, and no axes.
    boundaries = [[], [[]], [[], motif('triangle')],
                  [motif('edge'), [set(), set()], motif('triangle')],
                  [graph(5, [(0, 1), (2, 3)]), motif('triangle'), motif('edge')]]
    boundary_rows = [compare(factors) for factors in boundaries]
    paired = inventory([motif('edge'), motif('triangle'), motif('triangle')])
    raw, injective, ordinary = (paired[key][(2, 3, 3)] for key in
                               ('rooted_closed', 'rooted_injective', 'ordinary'))
    assert (raw, injective, ordinary) == (40320, 22464, 1404)
    terms, loopless = quotient_terms(8)
    result = {
        'scope': 'independent partition-lattice inversion; all existing products and profiles',
        'method': 'direct multigraph homomorphisms; no shuffle or projection-pattern calls',
        'partitions': sum(1 for _ in partitions(8)),
        'loopless_partitions': loopless,
        'signed_weighted_quotient_terms': len(terms),
        'quotient_terms': [{'vertices': n, 'edges_with_multiplicity': e, 'coefficient': c}
                           for n, e, c in terms],
        'original_corpus': rows,
        'additional_cases': extras,
        'exhaustive_small_pairs': pairs,
        'boundary_cases': boundary_rows,
        'negative_controls': {
            'closed_walk_division_233': {'rooted_closed': raw, 'rooted_injective': injective,
                'signed_correction': injective-raw, 'naive_ordinary': raw//16,
                'ordinary': ordinary},
            'full_support_only_Q4': {'naive': 648, 'ordinary': rows[-1]['total'],
                                     'missing': rows[-1]['total']-648}},
        'input_sha256': {p: sha256((ROOT/p).read_bytes()).hexdigest() for p in
                         ('conformance/first.json', 'conformance/lower-support.json')},
        'status': 'finite independent agreement; known inversion identity, no novelty or full formalization claim'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
