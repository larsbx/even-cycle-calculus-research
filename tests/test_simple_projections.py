"""Independent finite checks for all-length sectors and c10 support four."""
from collections import Counter
from itertools import permutations
import json
from math import factorial, prod
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kernels.eight_cycles import collision_free, invariants, shuffles
from kernels.simple_projections import (connected_words, simple_projection_coefficient,
                                        wedge_projection_coefficient,
                                        c10_support_four, f4222, f3322)
from experiments.near_top import cases, profile_count


def interval_free(word, profile):
    # Deliberately no product vertices or modular coordinates.
    for start in range(len(word)):
        counts = [0]*len(profile)
        for end in range(start, len(word)):
            counts[word[end]] += 1
            if end-start+1 < len(word) and all(c in (0, d) for c, d in zip(counts, profile)):
                return False
    return True


class SimpleProjections(unittest.TestCase):
    def test_all_length_wedge_coarsening_identity(self):
        expected = [0, 1, 60, 5256, 663168, 114681600, 26074068480]
        self.assertEqual([wedge_projection_coefficient(r) for r in range(7)], expected)
        # Direct B/C collision sums, independent of the top-minus-square evaluation.
        for r in range(4):
            counts = (4,)+(2,)*r
            rest = ((0, 1),)*r
            rooted = sum(collision_free(w, (p,)+rest)
                         for p in ((0, 1, 0, 2), (0, 1, 2, 1))
                         for w in shuffles(counts))
            numerator = rooted*2*2**r
            self.assertEqual(numerator, 2*sum(counts)*expected[r])
        # Independent adjacency DFS: P3 has two edge copies and one wedge copy.
        edge = cases()[0][1][0]
        wedge = cases()[1][1][0]
        for r in range(1, 4):
            p = (4,)+(2,)*r
            observed = profile_count([wedge]+[edge]*r, p) - 2*profile_count([edge]*(r+1), p)
            self.assertEqual(observed, expected[r])
        for r in (-1, True, 2.5):
            with self.assertRaises(ValueError):
                wedge_projection_coefficient(r)

    def test_recurrence_against_two_distinct_collision_checks(self):
        # Covers odd/even and repeated/different block sizes; labeled axes.
        for profile in ((2, 2), (3, 3), (2, 2, 2), (2, 3, 3), (4, 2, 2),
                        (5, 3), (2, 2, 2, 2), (2, 2, 3, 3), (4, 2, 2, 2)):
            patterns = tuple(tuple(range(d)) for d in profile)
            accepted = 0
            for word in shuffles(profile):
                interval = interval_free(word, profile)
                self.assertEqual(interval, collision_free(word, patterns), (profile, word))
                accepted += interval
            self.assertEqual(connected_words(profile), accepted, profile)

    def test_general_paired_family_and_existing_c8_coefficients(self):
        self.assertEqual([simple_projection_coefficient((2,)*r+(3, 3)) for r in range(5)],
                         [42, 1404, 90288, 9337536, 1404034560])
        self.assertEqual(simple_projection_coefficient((4, 2, 2)), 408)
        self.assertEqual(simple_projection_coefficient((4, 2, 2, 2)), 26592)
        # Existing source-owned specialization is only a regression, not a new claim.
        self.assertEqual(simple_projection_coefficient((2, 2, 2, 2)), 648)
        original = json.loads((Path(__file__).resolve().parents[1]/'conformance/first.json').read_text())
        paired = next(c for c in original['cases'] if c['case'] == 'K2 square K3 square K3')
        recorded = next(s['count'] for s in paired['strata'] if s['coordinate_steps'] == [2, 3, 3])
        self.assertEqual(simple_projection_coefficient((2, 3, 3)), recorded)
        for profile in ((2, 3, 3), (4, 2, 2), (2, 2, 3, 3)):
            for reordered in set(permutations(profile)):
                self.assertEqual(connected_words(profile), connected_words(reordered))

    def test_c10_motif_formula_against_independent_adjacency_dfs(self):
        for name, factors, profile, expected in cases():
            if sum(profile) != 10:
                continue
            data = [invariants(g) for g in factors]
            predicted = c10_support_four(data)
            self.assertEqual(predicted[profile], expected, name)
            self.assertEqual(profile_count(factors, profile), expected, name)
        edge = cases()[0][1][0]
        self.assertEqual(sum(c10_support_four([invariants(edge)]*4).values()), 2112)

    def test_c10_full_multilinear_basis(self):
        # The A/B/C/D inventory is general: do not fit coefficients to examples.
        pp = ((0, 1, 0, 1), (0, 1, 0, 2), (0, 1, 2, 1), (0, 1, 2, 3))
        raw = [sum(collision_free(w, (p, (0, 1), (0, 1), (0, 1)))
                   for w in shuffles((4, 2, 2, 2))) for p in pp]
        self.assertEqual(raw, [660, 2562, 4008, 8310])
        numerators = [raw[0]*2*8, (raw[1]+raw[2])*2*8, raw[3]*8*8]
        for name, num in zip(('edge', 'wedge', 'square'), numerators):
            self.assertEqual(num % 20, 0)
            unit = {'edge': 1}
            g = {n: int(n == name) for n in ('edge', 'wedge', 'square')}
            self.assertEqual(f4222(g, unit, unit, unit), num//20)
        self.assertEqual(f3322({'triangle': 1}, {'triangle': 1}, {'edge': 1}, {'edge': 1}),
                         connected_words((3, 3, 2, 2))*36*4//20)

    def test_fibers_coordinate_permutations_and_empty_cases(self):
        factors, profile = cases()[5][1:3]
        data = [invariants(g) for g in factors]
        base = c10_support_four(data)
        self.assertEqual(c10_support_four([]), Counter())
        self.assertEqual(c10_support_four(data[:3]), Counter())
        for order in permutations(range(4)):
            observed = c10_support_four([data[i] for i in order])
            expected = Counter({tuple(p[i] for i in order): n for p, n in base.items()})
            self.assertEqual(observed, expected)
        isolates = invariants([set()]*3)
        self.assertEqual(c10_support_four(data+[isolates]),
                         Counter({p+(0,): 3*n for p, n in base.items()}))
        self.assertEqual(c10_support_four(data+[invariants([])]), Counter())

    def test_negative_controls_and_scope(self):
        # Whole-block intervals fail for a noninjective four-step projection.
        word = (0, 0, 1, 0, 1, 0)
        self.assertTrue(interval_free(word, (4, 2)))
        self.assertFalse(collision_free(word, ((0, 1, 0, 1), (0, 1))))
        total = factorial(10)//prod(factorial(d) for d in (2, 2, 3, 3))
        self.assertEqual(total*144//20, 181440)
        self.assertNotEqual(total*144//20, 90288)
        self.assertEqual(49728-26592, 23136)  # discarded edge/wedge projections
        for profile in ((), (1, 3), (0, 2), (-2, 4)):
            with self.assertRaises(ValueError):
                connected_words(profile)
        with self.assertRaises(ValueError):
            simple_projection_coefficient((2,))


if __name__ == '__main__':
    unittest.main()
