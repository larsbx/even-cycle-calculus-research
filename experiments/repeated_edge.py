"""Exact matching receipt, with independent collision and adjacency checks."""
import json
from math import comb, factorial, prod
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kernels.repeated_edge import (joint_resolution_count, repeated_edge_coefficient,
                                  near_top_coefficients, near_top_profiles, crossing_connected)
from kernels.eight_cycles import collision_free, shuffles, invariants
from experiments.near_top import profile_count, motif


def resolutions(word):
    """Split successive distinguished steps by 0011 and 0110, respectively."""
    out = [[], []]
    step = 0
    for a in word:
        if a == 0:
            out[0].append((0, 0, 1, 1)[step])
            out[1].append((0, 1, 1, 0)[step])
            step += 1
        else:
            for row in out:
                row.append(a+1)
    assert step == 4
    return tuple(tuple(row) for row in out)


def word_connected(word):
    axes = max(word)+1
    chords = tuple(tuple(i for i, a in enumerate(word) if a == axis)
                   for axis in range(axes))
    assert all(len(c) == 2 for c in chords)
    return crossing_connected(chords)


def mixed_cases():
    edge = motif([(0, 1)], 2)
    wedge = motif([(0, 1), (1, 2)], 3)
    square = motif([(0, 1), (1, 2), (2, 3), (3, 0)], 4)
    triangle = motif([(0, 1), (1, 2), (2, 0)], 3)
    return [
        ('P3 square Q4', [wedge]+[edge]*4, (4, 2, 2, 2, 2), 879552),
        ('C4 square Q4', [square]+[edge]*4, (4, 2, 2, 2, 2), 5866368),
        ('K3 square K3 square Q3', [triangle]*2+[edge]*3,
         (3, 3, 2, 2, 2), 9337536),
    ]


def receipt():
    edge = motif([(0, 1)], 2)
    rows, direct = [], []
    for r in range(6):
        rows.append({'edge_axes': r, 'length': 2*r+4,
                     'diagrams_examined': comb(2*r+4, 4)*prod(range(1, 2*r, 2)),
                     'joint_connected_resolutions': joint_resolution_count(r),
                     'labeled_valid_axis_words': joint_resolution_count(r)*factorial(r),
                     'ordinary_repeated_edge_coefficient': repeated_edge_coefficient(r)})
    for r in range(5):
        observed = profile_count([edge]*(r+1), (4,)+(2,)*r)
        assert observed == repeated_edge_coefficient(r)
        direct.append({'edge_axes': r, 'ordinary_cycles_by_adjacency_dfs': observed})
    mixed = []
    for name, factors, profile, expected in mixed_cases():
        observed = profile_count(factors, profile)
        predicted = near_top_profiles([invariants(g) for g in factors], 6)[profile]
        assert observed == predicted == expected, (name, observed, predicted, expected)
        mixed.append({'case': name, 'profile': profile,
                      'ordinary_cycles_by_adjacency_dfs': observed,
                      'ordinary_cycles_by_motif_formula': predicted})
    controls = {}
    for word in shuffles((4, 2, 2)):
        front, outer = map(word_connected, resolutions(word))
        if front != outer:
            key = 'front_only_accepts' if front else 'outer_only_accepts'
            if key not in controls:
                controls[key] = {'word': word, 'front_connected': front,
                                 'outer_connected': outer,
                                 'folded_is_simple': collision_free(word, ((0, 1, 0, 1), (0, 1), (0, 1)))}
    return {'scope': 'working general finite-sum identity; listed evaluations are finite observations',
            'matching_sum': rows, 'independent_product_dfs': direct, 'independent_mixed_c12_dfs': mixed,
            'complete_next_to_top_coefficients': [
                {'half_length': k, **near_top_coefficients(k)} for k in range(2, 8)],
            'negative_controls': controls}


if __name__ == '__main__':
    print(json.dumps(receipt(), indent=2))
