"""Finite connected-block recurrence and a scoped c10 support-four formula.

Connected-partition enumeration is prior work (Lehner 2002). The graph-sector
translation and exact scope are proved in proof/simple-projection-sectors.md.
No infinite series, graph product construction, or product-cycle DFS is used.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import factorial, prod


@lru_cache(None)
def connected_words(profile):
    """Axis words with no nonempty proper interval made of whole axis blocks.

    Axes are labeled, even when their multiplicities agree. P_k(S) assigns each
    remaining whole axis to one of k ordered gaps, then orders each gap's word.
    The component containing position zero supplies the triangular recurrence.
    """
    if not profile or any(type(d) is not int or d < 2 for d in profile):
        raise ValueError('Expected a nonempty tuple of integer periods >= 2')
    q = len(profile)
    lengths = tuple(sum(d for a, d in enumerate(profile) if mask >> a & 1)
                    for mask in range(1 << q))
    moments = tuple(factorial(lengths[mask]) // prod(
        factorial(d) for a, d in enumerate(profile) if mask >> a & 1)
        for mask in range(1 << q))

    @lru_cache(None)
    def gaps(k, mask):
        if k == 0:
            return int(mask == 0)
        total, sub = 0, mask
        while True:
            total += moments[sub] * gaps(k - 1, mask ^ sub)
            if sub == 0:
                return total
            sub = (sub - 1) & mask

    connected = [0] * len(moments)
    for mask in range(1, len(moments)):
        value = moments[mask]
        sub = (mask - 1) & mask
        while sub:
            value -= connected[sub] * gaps(lengths[sub], mask ^ sub)
            sub = (sub - 1) & mask
        assert value >= 0
        connected[mask] = value
    return connected[-1]


def simple_projection_coefficient(profile):
    """Coefficient for fixed selected edges / once-traversed simple cycles.

    Period 2 means an edge traversed out and back; d>=3 means a selected
    ordinary C_d traversed once. Extra host edges are allowed. Total length
    must be >=3; this is a sector, not the complete cycle count.
    """
    if sum(profile) < 3:
        raise ValueError('Ordinary cycles have length at least three')
    rooted = connected_words(tuple(profile)) * prod(
        2 if d == 2 else 2*d for d in profile)
    value, remainder = divmod(rooted, 2*sum(profile))
    assert remainder == 0
    return value


def f4222(g, h, j, k):
    return (528*g['edge'] + 5256*g['wedge'] + 26592*g['square']) * prod(
        data['edge'] for data in (h, j, k))


def f3322(g, h, j, k):
    return 90288*g['triangle']*h['triangle']*j['edge']*k['edge']


def c10_support_four(data):
    """Every c10 stratum using exactly four axes; no other strata claimed."""
    q, out = len(data), Counter()
    for axes in combinations(range(q), 4):
        fiber = prod(data[a]['vertices'] for a in range(q) if a not in axes)
        for a in axes:
            others = tuple(b for b in axes if b != a)
            profile = tuple(4 if b == a else 2 if b in axes else 0 for b in range(q))
            out[profile] += fiber*f4222(data[a], *(data[b] for b in others))
        for triangles in combinations(axes, 2):
            edges = tuple(a for a in axes if a not in triangles)
            profile = tuple(3 if b in triangles else 2 if b in axes else 0
                            for b in range(q))
            out[profile] += fiber*f3322(*(data[b] for b in triangles + edges))
    return +out
