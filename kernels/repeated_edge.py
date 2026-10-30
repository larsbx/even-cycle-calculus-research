"""Two connected matching resolutions for a four-step repeated edge.

All counts are finite integers. Connected chord diagrams are established
combinatorics; the two-resolution collision identity is proved in
proof/repeated-edge-resolutions.md. No product graph or axis-word generator
is used by this evaluator.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import factorial, prod
from kernels.simple_projections import (simple_projection_coefficient,
                                        wedge_projection_coefficient)


def matchings(points):
    """Each perfect matching of the ordered points, exactly once."""
    if not points:
        yield ()
        return
    a = points[0]
    for i in range(1, len(points)):
        b = points[i]
        for rest in matchings(points[1:i]+points[i+1:]):
            yield ((a, b),)+rest


def crossing_connected(chords):
    """Connectivity of the intersection graph of chords on ordered endpoints."""
    if not chords:
        return False
    reached, frontier = {0}, [0]
    while frontier:
        a, b = chords[frontier.pop()]
        for j, (c, d) in enumerate(chords):
            if j not in reached and (a < c < b < d or c < a < d < b):
                reached.add(j)
                frontier.append(j)
    return len(reached) == len(chords)


@lru_cache(None, typed=True)
def joint_resolution_count(edge_axes):
    """J_r: four distinguished positions and an unlabeled matching of the rest.

    Accept iff both noncrossing resolutions of the distinguished four points
    give connected chord diagrams. Cost grows as C(2r+4,4)*(2r-1)!! diagrams;
    this is an exact finite sum, not a polynomial-time recurrence.
    """
    if type(edge_axes) is not int or edge_axes < 0:
        raise ValueError('Expected a nonnegative integer number of edge axes')
    length, total = 2*edge_axes+4, 0
    patterns = tuple(matchings(tuple(range(2*edge_axes))))
    for four in combinations(range(length), 4):
        a, b, c, d = four
        rest = tuple(i for i in range(length) if i not in four)
        for pattern in patterns:
            chords = tuple((rest[u], rest[v]) for u, v in pattern)
            if (crossing_connected(chords+((a, b), (c, d))) and
                    crossing_connected(chords+((a, d), (b, c)))):
                total += 1
    return total


def repeated_edge_coefficient(edge_axes):
    """A_r, the selected-edge contribution to profile (4,2^r)."""
    count = joint_resolution_count(edge_axes)
    value, remainder = divmod(2**edge_axes*factorial(edge_axes)*count, 2*edge_axes+4)
    assert remainder == 0
    return value


def near_top_coefficients(half_length):
    """Complete next-to-top-support coefficient inventory, length 2k, k>=2."""
    if type(half_length) is not int or half_length < 2:
        raise ValueError('Expected an integer half-length >= 2')
    r = half_length-2
    out = {'edge': repeated_edge_coefficient(r),
           'wedge': wedge_projection_coefficient(r),
           'square': simple_projection_coefficient((4,)+(2,)*r)}
    if half_length >= 3:
        out['paired_triangle'] = simple_projection_coefficient((3, 3)+(2,)*(half_length-3))
    return out


def near_top_profiles(data, half_length):
    """Ordinary C_(2k) using exactly k-1 coordinates, with all inactive fibers.

    Selected motifs are noninduced edge copies, wedges, squares and triangles.
    This does not count smaller support or the source-owned top support.
    """
    coefficients = near_top_coefficients(half_length)
    q, out = len(data), Counter()
    for axes in combinations(range(q), half_length-1):
        fiber = prod(data[a]['vertices'] for a in range(q) if a not in axes)
        for a in axes:
            motif = sum(coefficients[name]*data[a][name]
                        for name in ('edge', 'wedge', 'square'))
            profile = tuple(4 if b == a else 2 if b in axes else 0 for b in range(q))
            out[profile] += fiber*motif*prod(data[b]['edge'] for b in axes if b != a)
        for triangles in combinations(axes, 2):
            profile = tuple(3 if b in triangles else 2 if b in axes else 0 for b in range(q))
            out[profile] += fiber*coefficients['paired_triangle']*prod(
                data[b]['triangle'] if b in triangles else data[b]['edge'] for b in axes)
    return +out
