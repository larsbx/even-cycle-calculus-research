"""Boundary controls for the occurrence and canonical-data continuation."""
import unittest
from experiments.canonical_matching import extract, reconstruct, datum, axis_word


class CanonicalMatchingControls(unittest.TestCase):
    def test_occurrence_inverse_preserves_labeled_pairs(self):
        word = (0, 1, 0, 2, 0, 1, 0, 2)
        matching = extract(word, 2)
        self.assertEqual(matching, ((0, 2, 4, 6), ((1, 5), (3, 7))))
        self.assertEqual(reconstruct(matching), word)

    def test_data_forgets_names_but_retains_four_set_and_pairs(self):
        word = (0, 1, 0, 2, 0, 1, 0, 2)
        renamed = (0, 2, 0, 1, 0, 2, 0, 1)
        other = (0, 1, 0, 2, 0, 2, 0, 1)
        self.assertEqual(datum(word), datum(renamed))
        self.assertNotEqual(datum(word), datum(other))
        self.assertNotEqual(extract(word, 2), extract(renamed, 2))

    def test_profile_hypothesis_is_required(self):
        for word, r in (((0,)*6, 1), ((0,)*5, 0), ((0, 0, 0, 0, 1, 2), 1)):
            with self.assertRaises(ValueError):
                extract(word, r)

    def test_endpoint_hypotheses_are_required(self):
        for matching in (((0, 1, 2, 3), ((3, 4),)), ((0, 1, 2, 4), ()), ((1, 0, 2, 3), ()), ((0, 1, 2), ())):
            with self.assertRaises(ValueError):
                reconstruct(matching)

    def test_rooted_input_requires_cartesian_steps(self):
        with self.assertRaises(ValueError):
            axis_word(((0, 0), (1, 1)))
        with self.assertRaises(ValueError):
            axis_word(((0, 0), (0, 0)))
        self.assertEqual(axis_word(((0, 0), (1, 0), (1, 1), (0, 1))), (0, 1, 0, 1))


if __name__ == '__main__':
    unittest.main()
