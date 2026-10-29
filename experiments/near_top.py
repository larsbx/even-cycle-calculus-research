"""Independent adjacency DFS and exact receipt for the scoped continuation."""
from itertools import product
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from kernels.eight_cycles import collision_free, shuffles
from kernels.simple_projections import connected_words, simple_projection_coefficient


def profile_count(factors, profile):
    """Count ordinary cycles of one profile directly on product adjacency.

    No canonical patterns, motif counts, connected recurrence, or shuffle
    generator are used here. Root is the least product vertex; direction is
    chosen by the second and last vertices. Thus there is no final division.
    """
    if len(factors) != len(profile) or sum(profile) < 3:
        raise ValueError('Expected a cycle profile matching the factors')
    vertices = list(product(*(range(len(g)) for g in factors)))
    index = {v: i for i, v in enumerate(vertices)}
    adj = []
    for v in vertices:
        neighbors = []
        for a, g in enumerate(factors):
            for w in sorted(g[v[a]]):
                target = v[:a] + (w,) + v[a+1:]
                neighbors.append((index[target], a))
        adj.append(neighbors)
    total = 0
    for root in range(len(vertices)):
        def dfs(v, remaining, seen, first, left):
            if left == 1:
                return sum(w == root and first < v and remaining[a] == 1
                           for w, a in adj[v])
            value = 0
            for w, a in adj[v]:
                if remaining[a] and w > root and not (seen >> w & 1):
                    rest = list(remaining)
                    rest[a] -= 1
                    value += dfs(w, rest, seen | 1 << w, w if first is None else first,
                                 left - 1)
            return value
        total += dfs(root, list(profile), 1 << root, None, sum(profile))
    return total


def motif(edges, n):
    g = [set() for _ in range(n)]
    for u, v in edges:
        g[u].add(v)
        g[v].add(u)
    return g


def cases():
    edge = motif([(0, 1)], 2)
    wedge = motif([(0, 1), (1, 2)], 3)
    square = motif([(0, 1), (1, 2), (2, 3), (3, 0)], 4)
    triangle = motif([(0, 1), (1, 2), (2, 0)], 3)
    complete4 = motif([(u, v) for u in range(4) for v in range(u+1, 4)], 4)
    return [
        ('Q4, distinguished repeated axis', [edge]*4, (4, 2, 2, 2), 528),
        ('P3 square Q3', [wedge]+[edge]*3, (4, 2, 2, 2), 6312),
        ('C4 square Q3', [square]+[edge]*3, (4, 2, 2, 2), 49728),
        ('K3 square Q3', [triangle]+[edge]*3, (4, 2, 2, 2), 17352),
        ('K4 square Q3', [complete4]+[edge]*3, (4, 2, 2, 2), 146016),
        ('Q2 square K3 square K3', [edge]*2+[triangle]*2, (2, 2, 3, 3), 90288),
        ('K2 square K3 square K3', [edge]+[triangle]*2, (2, 3, 3), 1404),
        ('K3 square K3, six-step paired sector', [triangle]*2, (3, 3), 42),
    ]


def receipt():
    four_patterns = ((0, 1, 0, 1), (0, 1, 0, 2), (0, 1, 2, 1), (0, 1, 2, 3))
    coefficients = [sum(collision_free(w, (p, (0, 1), (0, 1), (0, 1)))
                        for w in shuffles((4, 2, 2, 2))) for p in four_patterns]
    assert coefficients == [660, 2562, 4008, 8310]
    paired = sum(collision_free(w, ((0, 1), (0, 1), (0, 1, 2), (0, 1, 2)))
                 for w in shuffles((2, 2, 3, 3)))
    assert paired == connected_words((2, 2, 3, 3)) == 12540
    rows = []
    for name, factors, profile, expected in cases():
        actual = profile_count(factors, profile)
        assert actual == expected, (name, actual, expected)
        rows.append({'case': name, 'profile': profile, 'ordinary_cycles': actual})
    return {
        'scope': 'working general sector identities; the listed finite evaluations are exact',
        'four_step_raw_coefficients': coefficients,
        'paired_triangle_raw_coefficient': paired,
        'paired_triangle_family': [
            {'edge_axes': r, 'length': 2*r+6,
             'valid_axis_words': connected_words((2,)*r+(3, 3)),
             'motif_coefficient': simple_projection_coefficient((2,)*r+(3, 3))}
            for r in range(7)],
        'independent_product_dfs': rows,
        'negative_controls': {
            'c10_C4_Q3_square_projection_only': 26592,
            'c10_C4_Q3_actual_profile': 49728,
            'c10_paired_unfiltered_walks_divided_by_20': 181440,
            'c10_paired_actual_profile': 90288,
            'c10_Q4_full_support_five_only': 0,
            'c10_Q4_all_four_support_profiles': 2112,
        },
    }


if __name__ == '__main__':
    print(json.dumps(receipt(), indent=2))
