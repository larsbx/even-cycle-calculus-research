"""Exact ordinary c8 support formulas for finite simple undirected graphs.

Graphs are adjacency sets indexed 0..n-1. Copies preserve selected edges,
not nonedges. No product adjacency or product-cycle enumeration is used here.
See proof/c8-lower-support.md for the shuffle/equality-pattern bijection.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
from math import prod


# Labeled representatives; the automorphism factors are checked in regression.
MOTIFS = {
    'edge': (2, ((0, 1),), 2),
    'wedge': (3, ((0, 1), (1, 2)), 2),
    'triangle': (3, ((0, 1), (1, 2), (2, 0)), 6),
    'square': (4, ((0, 1), (1, 2), (2, 3), (3, 0)), 8),
    'path3': (4, ((0, 1), (1, 2), (2, 3)), 2),
    'square_leaf': (5, ((0, 1), (1, 2), (2, 3), (3, 0), (0, 4)), 2),
    'diamond': (4, ((0, 1), (0, 2), (1, 2), (0, 3), (1, 3)), 4),
    'bowtie': (5, ((0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0)), 8),
    'hexagon': (6, tuple((i, (i+1) % 6) for i in range(6)), 12),
    'paw': (4, ((0, 1), (1, 2), (2, 0), (0, 3)), 2),
    'pentagon': (5, tuple((i, (i+1) % 5) for i in range(5)), 10),
    'octagon': (8, tuple((i, (i+1) % 8) for i in range(8)), 16),
}


def copies(g, name):
    """Injective edge-preserving maps divided by the known automorphism order."""
    n, edges, aut = MOTIFS[name]
    count = sum(all(p[v] in g[p[u]] for u, v in edges)
                for p in permutations(range(len(g)), n))
    q, r = divmod(count, aut)
    assert r == 0
    return q


def invariants(g):
    assert all(u not in ns and all(0 <= v < len(g) and u in g[v] for v in ns)
               for u, ns in enumerate(g)), 'Expected a finite simple undirected graph'
    return {'vertices': len(g), **{name: copies(g, name) for name in MOTIFS}}


def f62(g, h):
    return h['edge'] * (g['path3'] + 6*g['square_leaf'] + 2*g['diamond']
                        + 16*g['bowtie'] + 30*g['hexagon'])


def f35(g, h):
    return g['triangle'] * (18*h['triangle'] + 54*h['paw'] + 180*h['pentagon'])


def f44(g, h):
    return (2*(g['edge']*h['square'] + g['square']*h['edge'])
            + 5*g['wedge']*h['wedge']
            + 40*(g['wedge']*h['square'] + g['square']*h['wedge'])
            + 248*g['square']*h['square'])


def f422(g, h, j):
    return (2*g['edge'] + 60*g['wedge'] + 408*g['square'])*h['edge']*j['edge']


def f233(g, h, j):
    return 1404*g['edge']*h['triangle']*j['triangle']


def profile_formula(data):
    """Every nonzero coordinate-step stratum, including fixed-coordinate fibers.

    The four-coordinate coefficient is imported from the pinned source; its
    ownership/status is unchanged. The lower-support formulas are local.
    """
    q = len(data)
    out = Counter()

    def add(axes, steps, value):
        p = [0]*q
        for a, s in zip(axes, steps):
            p[a] = s
        out[tuple(p)] += value * prod(data[a]['vertices'] for a in range(q) if a not in axes)

    for a, g in enumerate(data):
        add((a,), (8,), g['octagon'])
    for a, b in combinations(range(q), 2):
        g, h = data[a], data[b]
        add((a, b), (6, 2), f62(g, h))
        add((a, b), (2, 6), f62(h, g))
        add((a, b), (3, 5), f35(g, h))
        add((a, b), (5, 3), f35(h, g))
        add((a, b), (4, 4), f44(g, h))
    for axes in combinations(range(q), 3):
        for a in axes:
            b, c = (x for x in axes if x != a)
            add((a, b, c), (4, 2, 2), f422(data[a], data[b], data[c]))
            add((a, b, c), (2, 3, 3), f233(data[a], data[b], data[c]))
    for axes in combinations(range(q), 4):
        add(axes, (2, 2, 2, 2), 648*prod(data[a]['edge'] for a in axes))
    return +out  # Counter unary plus removes zero entries.


@lru_cache(None)
def equality_patterns(n):
    """Restricted-growth encodings of partitions, proper on the cyclic edges."""
    def extend(p):
        if len(p) == n:
            if p[-1] != p[0]:
                yield tuple(p)
            return
        for x in range(max(p)+2):
            if x != p[-1]:
                yield from extend(p+[x])
    return tuple(extend([0]))


@lru_cache(None)
def shuffles(counts):
    if sum(counts) == 0:
        return ((),)
    out = []
    for a, c in enumerate(counts):
        if c:
            rest = list(counts)
            rest[a] -= 1
            out.extend((a,)+w for w in shuffles(tuple(rest)))
    return tuple(out)


def collision_free(word, patterns):
    at = [0]*len(patterns)
    seen = set()
    for a in word:
        vertex = tuple(p[at[b] % len(p)] for b, p in enumerate(patterns))
        if vertex in seen:
            return False
        seen.add(vertex)
        at[a] += 1
    return True


def quotient_edges(p):
    return tuple(sorted({tuple(sorted((p[i], p[(i+1) % len(p)])))
                         for i in range(len(p))}))


@lru_cache(None)
def graph_key(n, edges):
    """Canonical graph key by all finite relabelings, used only in derivation."""
    return (n, min(tuple(sorted(tuple(sorted((p[u], p[v]))) for u, v in edges))
                   for p in permutations(range(n))))


def motif_name(p):
    key = graph_key(max(p)+1, quotient_edges(p))
    for name, (n, edges, _) in MOTIFS.items():
        if n == key[0] and len(edges) == len(key[1]):
            if graph_key(n, tuple(edges)) == key:
                return name
    raise ValueError(('Uncatalogued nonzero projection', p))


def derive(profile):
    """Exact finite symbolic coefficient derivation, independent of graph inputs."""
    rows = []
    grouped = Counter()
    for pp in product(*(equality_patterns(n) for n in profile)):
        k = sum(collision_free(w, pp) for w in shuffles(tuple(profile)))
        if k:
            names = tuple(motif_name(p) for p in pp)
            grouped[names] += k
            rows.append({'patterns': pp, 'motifs': names, 'valid_shuffles': k})
    return {'profile': profile,
            'pattern_counts': [len(equality_patterns(n)) for n in profile],
            'shuffle_count': len(shuffles(tuple(profile))),
            'nonzero_patterns': rows,
            'grouped_injection_coefficients': [
                {'motifs': names, 'numerator': k, 'denominator': 16}
                for names, k in sorted(grouped.items())]}
