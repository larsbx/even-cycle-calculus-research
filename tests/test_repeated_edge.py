"""Independent finite tests of the two-resolution identity and its scope."""
from collections import Counter
from itertools import permutations
import json
from math import factorial
from pathlib import Path
import unittest
from kernels.repeated_edge import (matchings, crossing_connected,
                                  joint_resolution_count, repeated_edge_coefficient,
                                  near_top_coefficients, near_top_profiles)
from kernels.eight_cycles import collision_free, shuffles, invariants
from kernels.simple_projections import c10_support_four
from experiments.repeated_edge import resolutions, word_connected, mixed_cases
from experiments.near_top import motif, profile_count, cases


def no_closed_interval(chords):
    # Independent endpoint parity test; no crossing/intersection graph.
    length = 2*len(chords)
    for start in range(length):
        for stop in range(start+1, length+1):
            if stop-start < length and all(
                    (start <= a < stop) == (start <= b < stop) for a, b in chords):
                return False
    return True


class RepeatedEdge(unittest.TestCase):
    def test_matching_generator_and_connectivity(self):
        for n in range(1, 6):
            generated = list(matchings(tuple(range(2*n))))
            self.assertEqual(len(generated), factorial(2*n)//(2**n*factorial(n)))
            self.assertEqual(len(generated), len(set(generated)))
            for chords in generated:
                self.assertEqual(sorted(v for c in chords for v in c), list(range(2*n)))
                self.assertEqual(crossing_connected(chords), no_closed_interval(chords))
        self.assertEqual(list(matchings(())), [()])

    def test_wordwise_collision_equivalence(self):
        for r in range(4):
            accepted = 0
            for word in shuffles((4,)+(2,)*r):
                front, outer = resolutions(word)
                both = word_connected(front) and word_connected(outer)
                literal = collision_free(word, ((0, 1, 0, 1),)+((0, 1),)*r)
                self.assertEqual(both, literal, (r, word))
                accepted += literal
            self.assertEqual(accepted, factorial(r)*joint_resolution_count(r))

    def test_finite_family_and_independent_product_dfs(self):
        self.assertEqual([joint_resolution_count(r) for r in range(6)],
                         [0, 0, 2, 110, 3381, 89782])
        self.assertEqual([repeated_edge_coefficient(r) for r in range(6)],
                         [0, 0, 2, 528, 108192, 24625920])
        edge = motif([(0, 1)], 2)
        for r in range(5):
            self.assertEqual(profile_count([edge]*(r+1), (4,)+(2,)*r),
                             repeated_edge_coefficient(r))
        self.assertEqual(near_top_coefficients(6),
                         {'edge': 108192, 'wedge': 663168, 'square': 2780928,
                          'paired_triangle': 9337536})

    def test_existing_corpus_and_all_allocations(self):
        # All original eight-cycle profiles with exactly three active axes.
        root = Path(__file__).resolve().parents[1]
        # Use the same independent graph fixtures as the original inventory.
        from experiments.lower_support import original_cases
        corpus = json.loads((root/'conformance/first.json').read_text())['cases']
        for original, factors in zip(corpus, original_cases(), strict=True):
            name = original['case']
            predicted = near_top_profiles([invariants(g) for g in factors], 4)
            expected = Counter({tuple(s['coordinate_steps']): s['count']
                                for s in original['strata']
                                if sum(d > 0 for d in s['coordinate_steps']) == 3})
            self.assertEqual(predicted, expected, name)
        for name, factors, profile, expected in cases():
            if sum(profile) == 10:
                data = [invariants(g) for g in factors]
                self.assertEqual(near_top_profiles(data, 5), c10_support_four(data), name)
                self.assertEqual(near_top_profiles(data, 5)[profile], expected, name)

    def test_fibers_small_lengths_and_negative_controls(self):
        edge = motif([(0, 1)], 2)
        triangle = motif([(0, 1), (1, 2), (2, 0)], 3)
        data = [invariants(g) for g in (edge, triangle, triangle)]
        for order in permutations(range(3)):
            self.assertEqual(near_top_profiles([data[a] for a in order], 4),
                             Counter({tuple(p[a] for a in order): n
                                      for p, n in near_top_profiles(data, 4).items()}))
        base = near_top_profiles(data, 4)
        self.assertEqual(near_top_profiles(data+[invariants([set()]*3)], 4),
                         Counter({p+(0,): 3*n for p, n in base.items()}))
        self.assertFalse(near_top_profiles(data+[invariants([])], 4))
        self.assertFalse(near_top_profiles([], 2))
        square = motif([(0, 1), (1, 2), (2, 3), (3, 0)], 4)
        self.assertEqual(near_top_profiles([invariants(square)], 2), Counter({(4,): 1}))
        # Fresh adjacency DFS for these cases is mandatory in receipt replay;
        # compare their complete motif inventory here without repeating that DFS.
        for name, factors, profile, expected in mixed_cases():
            self.assertEqual(near_top_profiles([invariants(g) for g in factors], 6)[profile],
                             expected, name)
        # Each individual resolution overcounts genuine collisions.
        failures = set()
        for word in shuffles((4, 2, 2)):
            a, b = map(word_connected, resolutions(word))
            if a != b:
                self.assertFalse(collision_free(word, ((0, 1, 0, 1), (0, 1), (0, 1))))
                failures.add((a, b))
        self.assertEqual(failures, {(True, False), (False, True)})
        for bad in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                repeated_edge_coefficient(bad)
        for bad in (1, False, 2.5):
            with self.assertRaises(ValueError):
                near_top_coefficients(bad)


if __name__ == '__main__':
    unittest.main()
