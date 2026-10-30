"""Controls on the hypotheses of the new general proof interfaces."""
import unittest
from experiments.matching_transport import (E, S, graph_cycles, injective,
    literal_trace, connected_by_cuts, whole_interval, matching_key, resolve)


class MatchingTransportControls(unittest.TestCase):
    def test_endpoint_cover_is_required(self):
        # One abstract chord is connected; missing event positions add repeats.
        phases = [(0 < t <= 3,) for t in range(4)]
        self.assertEqual(len(set(phases)), 2)
        self.assertNotEqual(len(set(phases)), 4)

    def test_endpoint_disjointness_is_required(self):
        # [0,1] and [1,2] do not cross. All three departure states are distinct.
        states = [(0 < t <= 1, 1 < t <= 2) for t in range(3)]
        self.assertEqual(len(set(states)), 3)

    def test_connected_does_not_mean_intersection_graph_has_an_edge(self):
        self.assertTrue(connected_by_cuts((0, 0)))
        self.assertTrue(injective((0, 0), ((0, 1),)))
        self.assertIsNone(whole_interval((0, 0)))

    def test_nesting_does_not_connect_chords(self):
        word = (0, 1, 1, 0)
        self.assertFalse(connected_by_cuts(word))
        self.assertEqual(whole_interval(word), (1, 3))

    def test_both_resolution_requirements_are_essential(self):
        for word in ((0, 0, 1, 0, 0, 1), (0, 1, 0, 0, 1, 0)):
            accepted = tuple(map(connected_by_cuts, resolve(word)))
            self.assertNotEqual(accepted[0], accepted[1])
            self.assertFalse(injective(word, ((0, 1, 0, 1), (0, 1))))

    def test_label_names_are_not_unlabeled_matching_data(self):
        word = (0, 1, 0, 2, 0, 1, 0, 2)
        renamed = tuple(3-a if a else 0 for a in word)
        self.assertNotEqual(word, renamed)
        self.assertEqual(matching_key(word), matching_key(renamed))

    def test_full_return_is_not_an_extra_cycle_vertex(self):
        trace = literal_trace((0, 1, 0, 1), ((0, 1),)*2)
        self.assertEqual(len(set(trace)), 4)
        self.assertLess(len(set(trace+(trace[0],))), len(trace)+1)

    def test_global_quotient_counts_chorded_host_cycles(self):
        # A square host contributes an ordinary length-four cycle with eight
        # rooted directed representatives; its four positions are not enough.
        profiles, orbits = graph_cycles([S], 4)
        self.assertEqual(profiles[(4,)], 1)
        self.assertEqual(list(orbits.values()), [8])
        profiles, orbits = graph_cycles([E, E], 4)
        self.assertEqual(profiles[(2, 2)], 1)
        self.assertEqual(list(orbits.values()), [8])


if __name__ == '__main__':
    unittest.main()
