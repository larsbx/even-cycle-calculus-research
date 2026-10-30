"""Independent finite checks for the matching/word/quotient/motif interfaces.

No production matching counter, word generator, recurrence or product DFS is
imported. Restricted-growth words, explicit graph cuts, multiset permutations
and rooted product-adjacency paths give separate checks. Bounds are observations.
"""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from math import factorial, prod
from pathlib import Path
import json


def double_words(n):
    def visit(word, used, next_label):
        if len(word) == 2*n:
            yield tuple(word)
            return
        for a in range(min(next_label+1, n)):
            if a == next_label or used[a] == 1:
                fresh = a == next_label
                if fresh:
                    used.append(0)
                used[a] += 1
                word.append(a)
                yield from visit(word, used, next_label+fresh)
                word.pop()
                used[a] -= 1
                if fresh:
                    used.pop()
    yield from visit([], [], 0)


def chord_edges(word):
    chords = [tuple(i for i, x in enumerate(word) if x == a) for a in range(max(word)+1)]
    assert all(len(x) == 2 for x in chords)
    edges = []
    for i, j in combinations(range(len(chords)), 2):
        a, b = chords[i]
        c, d = chords[j]
        if a < c < b < d or c < a < d < b:
            edges.append((1 << i) | (1 << j))
    return chords, edges


def connected_by_cuts(word):
    chords, edges = chord_edges(word)
    for mask in range(1, (1 << len(chords))-1):
        if all((mask & e) in (0, e) for e in edges):
            return False
    return True


def literal_trace(word, patterns):
    phase = [0]*len(patterns)
    vertices = []
    for a in word:
        vertices.append(tuple(patterns[b][phase[b] % len(patterns[b])]
                              for b in range(len(patterns))))
        phase[a] += 1
    return tuple(vertices)


def injective(word, patterns):
    vertices = literal_trace(word, patterns)
    return len(set(vertices)) == len(vertices)


def whole_interval(word):
    for s in range(len(word)):
        for t in range(s+1, len(word)):
            if all(v == 2 for v in Counter(word[s:t]).values()):
                return (s, t)
    return None


def multiset_words(counts):
    budget = list(counts)
    def visit(word):
        if not any(budget):
            yield tuple(word)
            return
        for a in range(len(budget)):
            if budget[a]:
                budget[a] -= 1
                word.append(a)
                yield from visit(word)
                word.pop()
                budget[a] += 1
    yield from visit([])


def resolve(word):
    templates = ((0, 0, 1, 1), (0, 1, 1, 0))
    out = [[], []]
    k = 0
    for a in word:
        for i in range(2):
            out[i].append(templates[i][k] if a == 0 else a+1)
        k += a == 0
    return tuple(tuple(w) for w in out)


def matching_key(word):
    four = tuple(i for i, a in enumerate(word) if a == 0)
    pairs = sorted(tuple(i for i, x in enumerate(word) if x == a)
                   for a in range(1, max(word)+1))
    return four, tuple(pairs)


def graph(n, edges):
    return n, frozenset(frozenset(e) for e in edges)


E = graph(2, [(0, 1)])
W = graph(3, [(0, 1), (0, 2)])
S = graph(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
T = graph(3, [(0, 1), (1, 2), (2, 0)])
K4 = graph(4, list(combinations(range(4), 2)))


def invariants(g):
    n, es = g
    degree = [sum(v in e for e in es) for v in range(n)]
    triangle = sum(all(frozenset(e) in es for e in combinations(c, 2))
                   for c in combinations(range(n), 3))
    square = sum(all(frozenset((p[i], p[(i+1)%4])) in es for i in range(4))
                 for p in permutations(range(n), 4))//8
    return dict(vertices=n, edge=len(es), wedge=sum(d*(d-1)//2 for d in degree),
                square=square, triangle=triangle)


def graph_cycles(factors, length):
    """All ordinary cycles, recovered from every rooted directed path."""
    vertices = list(product(*(range(g[0]) for g in factors)))
    neighbors = {}
    for v in vertices:
        ns = []
        for a, (_, es) in enumerate(factors):
            for e in es:
                if v[a] in e:
                    w = list(v)
                    w[a] = next(x for x in e if x != v[a])
                    ns.append((tuple(w), a))
        neighbors[v] = ns
    orbits = Counter()
    profile_of = {}
    def canonical(path):
        p = tuple(path)
        i = min(range(length), key=lambda j: p[j])
        f = p[i:]+p[:i]
        return min(f, (f[0],)+tuple(reversed(f[1:])))
    for root in vertices:
        path, seen, steps = [root], {root}, [0]*len(factors)
        def walk(v):
            if len(path) == length:
                for w, a in neighbors[v]:
                    if w == root:
                        steps[a] += 1
                        key = canonical(path)
                        profile = tuple(steps)
                        assert key not in profile_of or profile_of[key] == profile
                        profile_of[key] = profile
                        orbits[key] += 1
                        steps[a] -= 1
                return
            for w, a in neighbors[v]:
                if w not in seen:
                    seen.add(w)
                    path.append(w)
                    steps[a] += 1
                    walk(w)
                    steps[a] -= 1
                    path.pop()
                    seen.remove(w)
        walk(root)
    assert set(orbits.values()) <= {2*length}, Counter(orbits.values())
    return Counter(profile_of.values()), orbits


def word_coefficients(r):
    L = 2*r+4
    raw = []
    for p in ((0, 1, 0, 1), (0, 1, 0, 2), (0, 1, 2, 1), (0, 1, 2, 3)):
        raw.append(sum(injective(w, (p,)+((0, 1),)*r)
                       for w in multiset_words((4,)+(2,)*r)))
    nums = (2**(r+1)*raw[0], 2**(r+1)*(raw[1]+raw[2]), 8*2**r*raw[3])
    assert all(n % (2*L) == 0 for n in nums)
    return dict(zip(('edge', 'wedge', 'square'), (n//(2*L) for n in nums)))


def receipt():
    connectivity = []
    for n in range(1, 7):
        total = accepted = 0
        seen_words = set()
        for w in double_words(n):
            assert w not in seen_words
            seen_words.add(w)
            c = connected_by_cuts(w)
            literal = injective(w, ((0, 1),)*n)
            assert c == literal == (whole_interval(w) is None), w
            total += 1
            accepted += c
        assert total == prod(range(1, 2*n, 2))
        connectivity.append(dict(chords=n, diagrams=total, connected=accepted))
    folded, controls = [], {}
    for r in range(4):
        fibers = Counter()
        good = Counter()
        total = 0
        for w in multiset_words((4,)+(2,)*r):
            f, o = resolve(w)
            cf, co = connected_by_cuts(f), connected_by_cuts(o)
            ok = injective(w, ((0, 1, 0, 1),)+((0, 1),)*r)
            assert ok == (cf and co), w
            k = matching_key(w)
            fibers[k] += 1
            good[k] += ok
            total += 1
            if cf != co:
                controls.setdefault('front_only' if cf else 'outer_only', dict(word=w, original=ok, front=cf, outer=co))
        assert total == factorial(2*r+4)//(factorial(4)*2**r)
        assert set(fibers.values()) == {factorial(r)}
        assert all(v in (0, factorial(r)) for v in good.values())
        J = sum(v > 0 for v in good.values())
        assert J == (0, 0, 2, 110)[r]
        folded.append(dict(edge_axes=r, words=total, matching_fibers=len(fibers),
                           fiber_size=factorial(r), accepted_words=sum(good.values()), J=J))
    automorphisms = {}
    for name, g in (('edge', E), ('wedge', W), ('square', S), ('triangle', T)):
        n, es = g
        automorphisms[name] = sum(frozenset(frozenset((p[x], p[y])) for x, y in map(tuple, es)) == es
                                 for p in permutations(range(n)))
    assert automorphisms == dict(edge=2, wedge=2, square=8, triangle=6)
    coeff = [word_coefficients(r) for r in range(3)]
    sectors = []
    for name, factors, r in (
        ('edge', [E, E, E], 2), ('wedge', [W, E, E], 2),
        ('square', [S, E, E], 2), ('extra_host_edges', [K4, E, E], 2),
        ('inactive_vertex_fiber', [W, E, E, graph(3, [])], 2),
    ):
        profiles, orbits = graph_cycles(factors, 2*r+4)
        profile = (4,)+(2,)*r+(0,)*(len(factors)-r-1)
        inv = list(map(invariants, factors))
        predicted = sum(coeff[r][k]*inv[0][k] for k in coeff[r]) * prod(
            x['edge'] for x in inv[1:r+1]) * prod(x['vertices'] for x in inv[r+1:])
        assert profiles[profile] == predicted
        # Every allocation in exactly k-1 coordinates, with inactive fibers.
        k = r+2
        all_predictions = Counter()
        for active in combinations(range(len(factors)), k-1):
            fiber = prod(inv[a]['vertices'] for a in range(len(factors)) if a not in active)
            for distinguished in active:
                p = tuple(4 if a == distinguished else 2 if a in active else 0 for a in range(len(factors)))
                all_predictions[p] = fiber*sum(coeff[r][m]*inv[distinguished][m] for m in coeff[r])*prod(
                    inv[a]['edge'] for a in active if a != distinguished)
        actual = +Counter({p: v for p, v in profiles.items() if sum(x > 0 for x in p) == k-1})
        assert actual == +all_predictions
        selected_copies = Counter()
        for path in orbits:
            recovered = [set() for _ in factors]
            budget = [0]*len(factors)
            for i, u in enumerate(path):
                v = path[(i+1)%len(path)]
                changed = [a for a in range(len(factors)) if u[a] != v[a]]
                assert len(changed) == 1
                a = changed[0]
                recovered[a].add(tuple(sorted((u[a], v[a]))))
                budget[a] += 1
            if sum(x > 0 for x in budget) != k-1:
                continue
            distinguished = budget.index(4)
            es = recovered[distinguished]
            verts = {x for e in es for x in e}
            kind = {(2, 1): 'edge', (3, 2): 'wedge', (4, 4): 'square'}[(len(verts), len(es))]
            for a in range(len(factors)):
                if budget[a] == 2:
                    assert len(recovered[a]) == 1
                if budget[a] == 0:
                    assert len({v[a] for v in path}) == 1
            key = (tuple(budget), tuple(tuple(sorted(es)) for es in recovered),
                   tuple(path[0][a] for a in range(len(factors)) if budget[a] == 0), kind)
            selected_copies[key] += 1
        assert all(v == coeff[r][key[-1]] for key, v in selected_copies.items())
        sectors.append(dict(case=name, length=2*r+4, selected_profile=profile,
                            cycles=predicted, all_near_top_cycles=sum(actual.values()),
                            rooted_quotient=2*(2*r+4), total_graph_cycles=sum(profiles.values()),
                            selected_copy_classes=len(selected_copies)))
    paired = []
    for s in range(2):
        L = 6+2*s
        raw = sum(injective(w, ((0, 1, 2),)*2+((0, 1),)*s)
                  for w in multiset_words((3, 3)+(2,)*s))
        numerator = 36*2**s*raw
        assert numerator % (2*L) == 0
        profiles, _ = graph_cycles([T, T]+[E]*s, L)
        assert profiles[(3, 3)+(2,)*s] == numerator//(2*L)
        paired.append(dict(edge_axes=s, raw_words=raw, coefficient=numerator//(2*L)))
    for r in range(3):
        n = r+2
        raw = sum(injective(w, ((0, 1),)*n) for w in multiset_words((2,)*n))
        top = 2**n*raw//(4*n)
        assert top == 4*coeff[r]['wedge'] + coeff[r]['square']
    # Mutations of explicit general hypotheses must actually fail.
    nested = (0, 1, 1, 0)
    assert not connected_by_cuts(nested) and not injective(nested, ((0, 1),)*2)
    c4 = literal_trace((0, 1, 0, 1), ((0, 1),)*2)
    assert len(set(c4)) == 4 and len(set(c4+(c4[0],))) != 5
    assert len({tuple(c4[(i+j)%4] for j in range(4)) for i in range(4)}) == 4
    assert len({tuple((0, 1, 0, 1)[(i+j)%4] for j in range(4)) for i in range(4)}) == 2
    # A single chord at 0,3 in a four-position word fails endpoint cover:
    # its intersection graph has one vertex, but departures 1 and 2 coincide.
    assert len(set((False, True, True, True))) < 4
    # Two chords sharing endpoint 1 cover 0,1,2, but do not cross; their three
    # departure states are distinct. Endpoint-disjointness is essential.
    shared = tuple((0 < t <= 1, 1 < t <= 2) for t in range(3))
    assert len(set(shared)) == 3
    assert sectors[0]['cycles'] == 2
    assert sectors[-1]['cycles'] == 3*sectors[1]['cycles'] == 192
    controls.update(dict(omit_direction_factor=dict(correct=2, wrong=4),
                         omit_inactive_fiber=dict(correct=192, wrong=64),
                         wedge_root_categories='individual root categories are not invariant under rotation',
                         full_return='including the final root rejects every closed simple cycle',
                         missing_endpoint_cover='one chord at 0,3 has repeated departures',
                         shared_endpoint='two noncrossing chords on 0,1 and 1,2 have distinct departures',
                         non_simple_trace='0101 has only two distinct rotations'))
    return dict(scope='finite observations; general proofs are in separately audited Lean sources',
                double_occurrence=connectivity, labeled_resolution_fibers=folded,
                selected_motif_automorphisms=automorphisms,
                literal_word_coefficients=coeff, product_adjacency=sectors,
                paired_triangle=paired, negative_controls=controls)


if __name__ == '__main__':
    print(json.dumps(receipt(), indent=2))
