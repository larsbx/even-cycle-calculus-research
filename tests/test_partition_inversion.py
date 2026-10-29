"""Cross-check the new oracle at its distinct combinatorial boundaries."""
from collections import Counter
from itertools import combinations, product
from math import factorial
import unittest

from kernels.partition_inversion import (colored_product, hom_profiles, inventory,
    mobius, partitions, quotient, quotient_terms)


def complete(n):
    return [set(range(n)) - {u} for u in range(n)]


class PartitionInversion(unittest.TestCase):
    def test_partition_inventory_and_mobius_cancellation(self):
        self.assertEqual([sum(1 for _ in partitions(n)) for n in range(9)],
                         [1, 1, 2, 5, 15, 52, 203, 877, 4140])
        ps = list(partitions(8))
        self.assertEqual(len(set(ps)), len(ps))
        for p in ps:
            self.assertEqual(sorted(v for b in p for v in b), list(range(8)))
            self.assertTrue(all(b for b in p))
        # For every possible walk equality kernel rho, sum mu(pi) over pi <= rho.
        # Refinements are independent partitions within each block of rho.
        block_sums = {n: sum(mobius(p) for p in partitions(n)) for n in range(1, 9)}
        self.assertEqual(block_sums, {1: 1, **{n: 0 for n in range(2, 9)}})
        for rho in partitions(8):
            coefficient = 1
            for block in rho:
                coefficient *= block_sums[len(block)]
            self.assertEqual(coefficient, int(len(rho) == 8))
        terms, loopless = quotient_terms(8)
        self.assertEqual((loopless, len(terms)), (715, 44))
        self.assertTrue(all(sum(w for _, _, w in e) == 8 for _, e, _ in terms))

    def test_parallel_edges_preserve_profile_degree(self):
        # Alternating C8 collapses to one host edge used eight times.
        edges = quotient(((0, 2, 4, 6), (1, 3, 5, 7)))
        self.assertEqual(edges, ((0, 1, 8),))
        adj = colored_product([[{1}, {0}], [{1}, {0}]])
        self.assertEqual(hom_profiles(2, edges, adj, 9), Counter({8: 4, 72: 4}))
        self.assertIsNone(quotient(((0, 1), (2,), (3,))))

    def test_frontier_counts_against_all_maps(self):
        # Arbitrary maps allow equal images for nonadjacent quotient vertices.
        adj = colored_product([complete(2), complete(3)])
        for n in range(3, 6):
            for blocks in partitions(n):
                edges = quotient(blocks)
                if edges is None:
                    continue
                brute = Counter()
                for f in product(range(len(adj)), repeat=len(blocks)):
                    if all(f[b] in adj[f[a]] for a, b, _ in edges):
                        p = sum(w * 9**adj[f[a]][f[b]] for a, b, w in edges)
                        brute[p] += 1
                self.assertEqual(hom_profiles(len(blocks), edges, adj, 9), brute)

    def test_complete_hosts_and_noninduced_convention(self):
        for m in (3, 4, 5, 6, 8):
            n = m
            # All injections into K_m; each selected cycle has 2m presentations.
            actual = inventory([complete(n)], m)
            self.assertEqual(actual['ordinary'], Counter({(m,): factorial(m)//(2*m)}))
        self.assertEqual(inventory([complete(7)])['ordinary'], Counter())

    def test_every_simple_host_of_order_at_most_four(self):
        for n in range(5):
            edges = list(combinations(range(n), 2))
            for mask in range(1 << len(edges)):
                g = [set() for _ in range(n)]
                for j, (u, v) in enumerate(edges):
                    if mask >> j & 1:
                        g[u].add(v)
                        g[v].add(u)
                self.assertEqual(inventory([g])['ordinary'], Counter())

    def test_boundaries_and_rejected_inputs(self):
        for factors in ([], [[]], [[set(), set()]], [[], complete(3)]):
            self.assertEqual(inventory(factors)['ordinary'], Counter())
        for g in ([{0}], [{1}, set()], [{2}, {0}]):
            with self.assertRaises(ValueError):
                inventory([g])
        for m in (0, 1, 2):
            with self.assertRaises(ValueError):
                inventory([complete(3)], m)


if __name__ == '__main__':
    unittest.main()
