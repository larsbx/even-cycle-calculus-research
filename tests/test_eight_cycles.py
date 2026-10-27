"""Exact polynomial, automorphism, boundary and permutation regressions."""
from collections import Counter
from itertools import permutations, product
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kernels.eight_cycles import (MOTIFS, derive, f62, f35, f44, f422, f233,
                                 profile_formula, invariants, shuffles,
                                 equality_patterns, quotient_edges)
from experiments.lower_support import graph_motif, check_inventory
from experiments.first import gpr


class EightCycles(unittest.TestCase):
    def test_automorphisms(self):
        for name, (n, edges, aut) in MOTIFS.items():
            g = graph_motif(name)
            actual = sum(all(p[v] in g[p[u]] for u, v in edges)
                         for p in permutations(range(n)))
            self.assertEqual(actual, aut, name)

    def test_all_symbolic_coefficients(self):
        """Compare formula on every multilinear basis to full pattern derivation."""
        names = tuple(MOTIFS)
        for profile, f in [((6, 2), f62), ((3, 5), f35), ((4, 4), f44),
                           ((4, 2, 2), f422), ((2, 3, 3), f233)]:
            coefficients = {}
            for row in derive(profile)['grouped_injection_coefficients']:
                numerator = row['numerator']
                for name in row['motifs']:
                    numerator *= MOTIFS[name][2]
                self.assertEqual(numerator % 16, 0)
                coefficients[row['motifs']] = numerator//16
            for key in product(names, repeat=len(profile)):
                basis = [{n: int(n == chosen) for n in names} for chosen in key]
                self.assertEqual(f(*basis), coefficients.get(key, 0), (profile, key))

    def test_pattern_and_shuffle_completeness(self):
        # Independent brute-force restricted-growth check, without recursion.
        for n in range(2, 7):
            brute = {p for p in product(range(n), repeat=n)
                     if p[0] == 0 and all(p[i] <= 1+max(p[:i]) for i in range(1, n))
                     and all(p[i] != p[(i+1) % n] for i in range(n))}
            self.assertEqual(set(equality_patterns(n)), brute)
        for profile in ((6, 2), (3, 5), (4, 4), (4, 2, 2), (2, 3, 3)):
            ws = shuffles(profile)
            brute = {w for w in product(range(len(profile)), repeat=8)
                     if tuple(w.count(a) for a in range(len(profile))) == profile}
            self.assertEqual(set(ws), brute)
            self.assertEqual(len(ws), len(brute))

    def test_quotient_embeddings_are_exact_equalities(self):
        # Every rooted closed projected walk has exactly one pattern plus injection.
        g = gpr.graph(4, list(permutations(range(4), 2)))
        for n in range(2, 7):
            observed = Counter()
            for w in product(range(4), repeat=n):
                if all(w[(i+1) % n] in g[w[i]] for i in range(n)):
                    labels = {}
                    p = tuple(labels.setdefault(v, len(labels)) for v in w)
                    observed[p] += 1
            for p in equality_patterns(n):
                edges = quotient_edges(p)
                inj = sum(all(a[v] in g[a[u]] for u, v in edges)
                          for a in permutations(range(4), max(p)+1))
                self.assertEqual(observed[p], inj)

    def test_empty_edgeless_disconnected_and_fiber_multiplicity(self):
        edge = graph_motif('edge')
        triangle = graph_motif('triangle')
        for factors in ([], [[]], [[], triangle], [edge, [set(), set()], triangle],
                        [gpr.graph(5, [(0, 1), (2, 3)]), triangle, edge]):
            check_inventory(factors)
        base = profile_formula([invariants(triangle)]*2)
        extended = profile_formula([invariants(triangle), invariants([set()]*3), invariants(triangle)])
        self.assertEqual(extended, Counter({(a, 0, b): 3*n for (a, b), n in base.items()}))

    def test_relabeling_and_coordinate_permutation(self):
        factors = [graph_motif(n) for n in ('edge', 'wedge', 'triangle')]
        for axes in permutations(range(3)):
            check_inventory([factors[a] for a in axes])
        renamed = [[{len(g)-1-v for v in g[len(g)-1-u]} for u in range(len(g))] for g in factors]
        self.assertEqual(profile_formula([invariants(g) for g in factors]),
                         profile_formula([invariants(g) for g in renamed]))

    def test_invalid_graph_rejected(self):
        for g in ([{0}], [{1}, set()]):
            with self.assertRaises(AssertionError):
                invariants(g)


if __name__ == '__main__':
    unittest.main()
