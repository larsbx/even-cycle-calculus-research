"""Independent unrestricted-adjacency / finite partition-lattice experiment.

Candidate formulas, DFS receipts and motif kernels enter only the comparison
layer in receipt(); they never supply a hom count, partition or Mobius weight.
"""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json
import subprocess
import sys
import tempfile
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kernels.partition_lattice import (partitions, mobius, refinements, invert,
                                       quotient_homs, normalize)
ROOT = Path(__file__).resolve().parents[1]


def graph(n, edges):
    result = [set() for _ in range(n)]
    for u, v in edges:
        result[u].add(v)
        result[v].add(u)
    return result


def fixture(name):
    paths = {'edge': 2, 'wedge': 3, 'path3': 4}
    cycles = {'triangle': 3, 'square': 4, 'pentagon': 5, 'hexagon': 6, 'octagon': 8}
    if name in paths:
        n = paths[name]
        return graph(n, [(i, i+1) for i in range(n-1)])
    if name in cycles:
        n = cycles[name]
        return graph(n, [(i, (i+1) % n) for i in range(n)])
    data = {
        'square_leaf': (5, [(0,1),(1,2),(2,3),(3,0),(0,4)]),
        'diamond': (4, [(0,1),(0,2),(1,2),(0,3),(1,3)]),
        'bowtie': (5, [(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)]),
        'paw': (4, [(0,1),(1,2),(2,0),(0,3)]),
        'K4': (4, list(combinations(range(4), 2))),
    }
    return graph(*data[name])


def cartesian(factors):
    vs = list(product(*(range(len(g)) for g in factors)))
    index = {v: i for i, v in enumerate(vs)}
    adj = [{} for _ in vs]
    for i, v in enumerate(vs):
        for a, g in enumerate(factors):
            for w in g[v[a]]:
                adj[i][index[v[:a]+(w,)+v[a+1:]]] = a
    return vs, adj


class UnrestrictedWalks:
    def __enter__(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='ecc-partition-')
        self.binary = str(Path(self.tmp.name)/'walks')
        subprocess.run(['g++', '-std=c++17', '-O2', '-Wall', '-Wextra', '-Werror',
                        str(ROOT/'experiments/partition_walks.cpp'), '-o', self.binary], check=True)
        return self

    def __exit__(self, *args):
        self.tmp.cleanup()

    def run(self, factors, length, profile=None, distinguished=-1):
        vs, adj = cartesian(factors)
        if not vs:
            return {}, adj
        q = len(factors)
        if profile is not None and (len(profile) != q or sum(profile) != length or min(profile) < 0):
            raise ValueError('profile must be a nonnegative length budget')
        edges = [(i, j, a) for i, ns in enumerate(adj) for j, a in sorted(ns.items())]
        lines = [f'{len(vs)} {q} {length} {distinguished}',
                 ' '.join(map(str, profile if profile is not None else [-1]*q)),
                 *(' '.join(map(str, v)) for v in vs), str(len(edges)),
                 *(f'{i} {j} {a}' for i, j, a in edges)]
        output = subprocess.check_output([self.binary], input='\n'.join(lines)+'\n', text=True)
        result = defaultdict(Counter)
        for line in output.splitlines():
            key, count = line.split()
            p, kernel, category = key.split('|')
            result[tuple(map(int, p.split(','))), category][tuple(map(int, kernel))] += int(count)
        return dict(result), adj


def combine(histograms):
    result = Counter()
    for histogram in histograms:
        result.update(histogram)
    return result


def digest(homs):
    return sha256(''.join(''.join(map(str, p))+':'+str(n)+'\n'
                          for p, n in sorted(homs.items())).encode()).hexdigest()


def evaluate(histogram, length, adj=None, profile=None, direct=False):
    injective, homs, ledger = invert(histogram, length)
    quotient, remainder = divmod(injective, 2*length)
    assert remainder == 0 and injective >= 0
    # Independent CSP checks of quotient homs, not self-avoiding DFS.
    checks = 0
    positive_checks = 0
    if direct:
        # Include positive, profile-feasible quotients. Arbitrary partitions
        # would mostly collapse an edge and test only the trivial zero case.
        positive = sorted(homs, key=lambda p: (max(p), p))
        samples = positive[:4]
        loopless = [p for p in partitions(length) if max(p) < 4
                    and all(p[i] != p[(i+1)%length] for i in range(length))]
        samples += loopless[:3] + [(0,)*length]
        samples = list(dict.fromkeys(samples))
        positive_checks = 0
        for rho in samples:
            assert quotient_homs(adj, rho, profile) == homs[rho], (rho, homs[rho])
            checks += 1
            positive_checks += int(homs[rho] > 0)
        assert positive_checks >= min(4, len(positive))
    return {'closed_rooted_directed': sum(histogram.values()),
            'injective_rooted_directed': injective, 'ordinary_cycles': quotient,
            'mobius_terms_by_blocks': ledger, 'nonzero_quotient_homs': len(homs),
            'hom_ledger_sha256': digest(homs), 'direct_quotient_checks': checks, 'positive_direct_quotient_checks': positive_checks}


def counts_by_profile(engine, factors, length):
    hist, adj = engine.run(factors, length)
    profiles = defaultdict(list)
    for (p, _), counts in hist.items():
        profiles[p].append(counts)
    rows = {p: evaluate(combine(cs), length) for p, cs in sorted(profiles.items())}
    return rows


def expected_profiles(row):
    key = 'strata' if 'strata' in row else 'profiles'
    return {tuple(p.get('coordinate_steps', p.get('steps'))): p['count'] for p in row[key]}


def receipt():
    # Verify the cancellation identity on EVERY partition through length ten,
    # independently of which equality kernels occur in the corpus.
    cancellation = []
    for n in range(1, 11):
        # A partition's lower interval factors over its blocks. Test each
        # one-block interval explicitly, then every block-product identity.
        local = {k: sum(mobius(p) for p in partitions(k)) for k in range(1, n+1)}
        assert all(local[k] == int(k == 1) for k in local)
        for p in partitions(n):
            sizes = Counter(p)
            value = 1
            for size in sizes.values():
                value *= local[size]
            assert value == int(len(sizes) == n)
        cancellation.append({'length': n, 'partitions': len(partitions(n))})
    first = json.loads((ROOT/'conformance/first.json').read_text())['cases']
    lower = json.loads((ROOT/'conformance/lower-support.json').read_text())
    original_names = [('square','edge'), ('triangle','triangle'), ('wedge','triangle'),
                      ('edge','triangle','triangle'), ('edge',)*4]
    corpus = []
    ten = []
    raw_coefficients = {}
    with UnrestrictedWalks() as engine:
        for expected, names in zip(first, original_names, strict=True):
            rows = counts_by_profile(engine, [fixture(n) for n in names], 8)
            actual = {p: r['ordinary_cycles'] for p, r in rows.items() if r['ordinary_cycles']}
            assert actual == expected_profiles(expected), (names, actual)
            corpus.append({'case': expected['case'], 'total': sum(actual.values()),
                           'profiles': [{'steps': p, **r} for p, r in rows.items()]})
        extras = []
        for expected in lower['additional_cases']:
            names = expected['case'].split(' square ')
            rows = counts_by_profile(engine, [fixture(n) for n in names], 8)
            actual = {p: r['ordinary_cycles'] for p, r in rows.items() if r['ordinary_cycles']}
            assert actual == expected_profiles(expected), (names, actual)
            extras.append({'case': expected['case'], 'total': sum(actual.values()),
                           'profiles': [{'steps': p, **r} for p, r in rows.items()]})
        # The comparison boundary alone imports the candidate formula.
        from kernels.eight_cycles import profile_formula, invariants
        small = []
        for n in range(4):
            edges = list(combinations(range(n), 2))
            small.extend(graph(n, [e for i, e in enumerate(edges) if mask >> i & 1])
                         for mask in range(1 << len(edges)))
        small_rows = []
        for i, g in enumerate(small):
            for j, h in enumerate(small):
                rows = counts_by_profile(engine, [g,h], 8)
                actual = Counter({p: r['ordinary_cycles'] for p,r in rows.items() if r['ordinary_cycles']})
                assert actual == profile_formula([invariants(g),invariants(h)]), (i,j,actual)
                small_rows.append([i,j, [[*p,n] for p,n in sorted(actual.items())]])
        near = json.loads((ROOT/'conformance/near-top.json').read_text())['independent_product_dfs']
        near_names = [('edge',)*4, ('wedge','edge','edge','edge'), ('square','edge','edge','edge'),
                      ('triangle','edge','edge','edge'), ('K4','edge','edge','edge'),
                      ('edge','edge','triangle','triangle'), ('edge','triangle','triangle'),
                      ('triangle','triangle')]
        for expected, names in zip(near, near_names, strict=True):
            factors = [fixture(n) for n in names]
            profile = tuple(expected['profile'])
            length = sum(profile)
            hist, adj = engine.run(factors, length, profile, 0 if profile[0] == 4 else -1)
            merged = combine(hist.values())
            result = evaluate(merged, length, adj, profile, direct=True)
            assert result['ordinary_cycles'] == expected['ordinary_cycles'], (names, result)
            categories = []
            if profile[0] == 4:
                for (_, pattern), counts in sorted(hist.items()):
                    injected, _, _ = invert(counts, length)
                    # Category need not be invariant under rotation: do NOT
                    # divide category counts by 2m; only their sum is a cycle count.
                    categories.append({'projection': pattern,
                                       'injective_rooted_directed': injected})
                # Pattern embedding counts are tiny independent factor walks.
                embeddings = Counter()
                for trace in product(range(len(factors[0])), repeat=4):
                    if all(trace[(i+1)%4] in factors[0][trace[i]] for i in range(4)):
                        embeddings[''.join(map(str,normalize(trace)))] += 1
                for (_, pattern), counts in hist.items():
                    injected, _, _ = invert(counts, length)
                    scale = embeddings[pattern]*8 # three selected K2 axes
                    assert injected % scale == 0
                    coefficient = injected//scale
                    assert pattern not in raw_coefficients or raw_coefficients[pattern] == coefficient
                    raw_coefficients[pattern] = coefficient
            ten.append({'case': expected['case'], 'profile': profile, **result,
                        'projection_categories': categories})
        assert raw_coefficients == {'0101':660, '0102':2562, '0121':4008, '0123':8310}
        assert ten[5]['injective_rooted_directed'] // (2*2*6*6) == 12540
        a = ten[0]['ordinary_cycles']
        b = ten[1]['ordinary_cycles']-2*a
        c = ten[2]['ordinary_cycles']-4*a-4*b
        motif_coefficients = {'edge':a, 'wedge':b, 'square':c,
                              'paired_triangles':ten[5]['ordinary_cycles']}
        assert (a,b,c) == (528,5256,26592)
        assert ten[3]['ordinary_cycles'] == 3*a+3*b
        assert ten[4]['ordinary_cycles'] == 6*a+12*b+3*c
        k4hist, _ = engine.run([fixture('K4')], 4)
        k4ordinary = invert(combine(k4hist.values()), 4)[0]//8
        from itertools import permutations
        k4 = fixture('K4')
        k4induced = sum(all(t[j] not in k4[t[i]] for i in range(4) for j in range(i+1,4)
                           if j-i not in (1,3)) for t in permutations(range(4)))//8
        assert (k4ordinary, k4induced) == (3,0)
        # A fully direct quotient CSP comparison on all Pi_10 for K2.
        hist, adj = engine.run([fixture('edge')], 10)
        _, homs, _ = invert(combine(hist.values()), 10)
        for rho in partitions(10):
            assert quotient_homs(adj, rho) == homs[rho], rho
        # All partitions at every shorter length on a nonbipartite target.
        direct_short = 0
        for length in range(3,7):
            hist, adj = engine.run([fixture('triangle')], length)
            _, homs, _ = invert(combine(hist.values()), length)
            for rho in partitions(length):
                assert quotient_homs(adj, rho) == homs[rho], (length,rho)
                direct_short += 1
    return {'scope': 'finite partition-lattice inversion; general theory is established prior work',
            'algorithm': 'unrestricted rooted adjacency walks -> equality histogram -> quotient-hom zeta -> Mobius sum',
            'all_partition_cancellation': cancellation,
            'ordinary_c8_corpus': corpus, 'additional_c8_cases': extras,
            'small_graph_pairs': len(small_rows), 'small_pairs_results_sha256': sha256(json.dumps(small_rows).encode()).hexdigest(),
            'near_top_profiles': ten, 'four_step_raw_coefficients': raw_coefficients,
            'paired_triangle_raw_coefficient': 12540,
            'recovered_motif_coefficients': motif_coefficients,
            'direct_quotient_oracle': {'K2_length10_all_partitions':len(partitions(10)),
                                       'K3_lengths3_through6_all_partitions': direct_short},
            'negative_controls': {
                'paired_c10_unfiltered_closed_div20': ten[5]['closed_rooted_directed']//20,
                'paired_c10_after_inversion': ten[5]['ordinary_cycles'],
                'C4_Q3_square_projection_only': next(c['injective_rooted_directed']//20 for c in ten[2]['projection_categories'] if c['projection']=='0123'),
                'C4_Q3_all_projections': ten[2]['ordinary_cycles'],
                'Q4_c8_only_full_support': 648, 'Q4_c8_all_supports': 696,
                'wrong_c10_divide_by_length': ten[5]['injective_rooted_directed']//10,
                'wrong_c10_divide_twice': [ten[5]['ordinary_cycles'],20],
                'K4_ordinary_c4': k4ordinary, 'K4_induced_c4': k4induced},
            'discrepancies': [],
            'claim_boundary': 'Finite corroboration of candidate expansions; no new general inversion theorem, novelty or full graph-level Lean cardinality claim.'}


if __name__ == '__main__':
    print(json.dumps(receipt(), indent=2))
