"""Exact finite controls for simultaneous pairing resolutions."""
from collections import Counter
from itertools import product
from math import factorial, prod
from pathlib import Path
import json
import unittest
from kernels.even_edge_resolutions import (block_partitions, pairing,
    all_resolutions_connected, even_edge_coefficient, unlabeled_count, cube_profile_totals)
from kernels.eight_cycles import shuffles, collision_free
from kernels.repeated_edge import repeated_edge_coefficient
from kernels.simple_projections import simple_projection_coefficient
from experiments.near_top import profile_count, motif


def literal_injective(word):
    state, seen = 0, set()
    for a in word:
        if state in seen:
            return False
        seen.add(state)
        state ^= 1 << a
    return state == 0


def blocks_from_word(word, profile):
    return tuple(tuple(i for i, a in enumerate(word) if a == j) for j in range(len(profile)))


class EvenEdgeResolutions(unittest.TestCase):
    def test_partition_inventory_and_every_small_word(self):
        for p in ((4,), (2, 2), (4, 2), (6, 2), (4, 4), (2, 2, 2),
                  (4, 2, 2), (6, 2, 2), (4, 4, 2), (4, 2, 2, 2)):
            canonical = tuple(sorted(p))
            blocks = list(block_partitions(canonical))
            labelings = prod(factorial(n) for n in Counter(p).values())
            expected = factorial(sum(p))//prod(factorial(d) for d in p)//labelings
            self.assertEqual(len(blocks), expected)
            self.assertEqual(len(set(blocks)), expected)
            accepted = 0
            for word in shuffles(p):
                observed = literal_injective(word)
                self.assertEqual(observed, collision_free(word, ((0, 1),)*len(p)))
                self.assertEqual(all_resolutions_connected(blocks_from_word(word, p)), observed,
                                 (p, word))
                accepted += observed
            self.assertEqual(accepted, unlabeled_count(p)*labelings)

    def test_existing_formulas_and_independent_lower_sector(self):
        for r in range(4):
            self.assertEqual(even_edge_coefficient((4,)+(2,)*r), repeated_edge_coefficient(r))
        for q in range(2, 6):
            self.assertEqual(even_edge_coefficient((2,)*q), simple_projection_coefficient((2,)*q))
        edge = motif([(0, 1)], 2)
        for profile, expected in (((6, 2, 2, 2), 32), ((4, 4, 2, 2), 816)):
            self.assertEqual(even_edge_coefficient(profile), expected)
            self.assertEqual(profile_count([edge]*4, profile), expected)
        self.assertEqual(cube_profile_totals(4, 12), Counter({(2, 2, 2, 6): 128, (2, 2, 4, 4): 4896}))
        self.assertEqual(sum(cube_profile_totals(4, 10).values()), 2112)
        original = json.loads((Path(__file__).resolve().parents[1]/'conformance/first.json').read_text())
        q4 = next(row for row in original['cases'] if row['case'] == 'Q4')
        baseline = Counter()
        for row in q4['strata']:
            baseline[tuple(sorted(d for d in row['coordinate_steps'] if d))] += row['count']
        self.assertEqual(cube_profile_totals(4, 8), baseline)

    def test_all_choice_combinations_and_scope(self):
        # The two globally constant choices both miss this actual collision.
        blocks = ((1, 6), (0, 2, 4, 8), (3, 5, 7, 9))
        outcomes = []
        from kernels.repeated_edge import crossing_connected
        for bits in product(range(2), repeat=2):
            outcomes.append(crossing_connected(tuple(c for b, flag in zip(blocks, (0,)+bits)
                                                    for c in pairing(b, flag))))
        self.assertEqual(outcomes, [True, True, False, True])
        word = tuple(next(a for a, b in enumerate(blocks) if i in b) for i in range(10))
        self.assertFalse(literal_injective(word))
        self.assertFalse(all_resolutions_connected(blocks))
        for b in ((0, 1), (0, 2, 4, 5), (1, 3, 5, 8, 10, 12)):
            for flag in (False, True):
                self.assertEqual(sorted(v for chord in pairing(b, flag) for v in chord), list(b))
        # Selected-edge sector in two axes has at most four vertices, even
        # when host triangles provide many ordinary eight-cycles by other motifs.
        self.assertEqual(even_edge_coefficient((4, 4)), 0)
        self.assertEqual(even_edge_coefficient((6, 2)), 0)
        self.assertNotEqual(sum(cube_profile_totals(4, 12).values()), 0)

    def test_finite_boundaries_and_validation(self):
        self.assertFalse(cube_profile_totals(0, 8))
        self.assertFalse(cube_profile_totals(1, 8))
        self.assertEqual(cube_profile_totals(2, 4), Counter({(2, 2): 1}))
        for p in ((), (2,), (3, 3), (0, 4), (True, 4), (4.0, 2)):
            with self.assertRaises(ValueError):
                even_edge_coefficient(p)
        for d, length in ((-1, 8), (True, 8), (4, 3), (4, 2), (4, 8.0)):
            with self.assertRaises(ValueError):
                cube_profile_totals(d, length)


if __name__ == '__main__':
    unittest.main()
