"""Independent canonical matching/word/fiber and rooted-input checks.

This uses restricted-growth words and explicit occurrence lists, and imports
only the preceding independent checker. No production matching evaluator,
coefficient formula, Lean implementation, or production DFS is imported.
"""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from math import comb, factorial, prod
from pathlib import Path
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from experiments.matching_transport import (
    E, double_words, multiset_words, matching_key, resolve, connected_by_cuts,
    injective, literal_trace, graph_cycles)


def extract(word, r):
    if len(word) != 2*r+4 or any(not 0 <= a <= r for a in word):
        raise ValueError('wrong finite profile domain')
    occ = [tuple(i for i, a in enumerate(word) if a == j) for j in range(r+1)]
    if tuple(map(len, occ)) != (4,)+(2,)*r:
        raise ValueError('wrong occurrence multiplicities')
    return occ[0], tuple(occ[1:])


def reconstruct(matching):
    four, pairs = matching
    if len(four) != 4:
        raise ValueError('distinguished endpoint inventory must have four entries')
    positions = four+tuple(x for pair in pairs for x in pair)
    if len(set(positions)) != len(positions) or set(positions) != set(range(len(positions))):
        raise ValueError('endpoint cover/disjointness failure')
    if tuple(sorted(four)) != four or any(a >= b for a, b in pairs):
        raise ValueError('endpoint order failure')
    out = [0]*len(positions)
    for a, pair in enumerate(pairs, 1):
        for p in pair:
            out[p] = a
    return tuple(out)


def datum(word):
    return (tuple(a == 0 for a in word),
            tuple(a != 0 and a == b for a in word for b in word))


def unlabeled_matchings(r):
    L = 2*r+4
    for four in combinations(range(L), 4):
        rest = tuple(i for i in range(L) if i not in four)
        if r == 0:
            yield four, ()
        else:
            for w in double_words(r):
                pairs = tuple(sorted(tuple(rest[i] for i, a in enumerate(w) if a == j) for j in range(r)))
                yield four, pairs


def axis_word(trace):
    out = []
    for i, u in enumerate(trace):
        v = trace[(i+1)%len(trace)]
        changes = [a for a in range(len(u)) if u[a] != v[a]]
        if len(changes) != 1:
            raise ValueError('not a Cartesian edge trace')
        out.append(changes[0])
    return tuple(out)


def canonical(trace):
    i = min(range(len(trace)), key=lambda j: trace[j])
    f = trace[i:]+trace[:i]
    return min(f, (f[0],)+tuple(reversed(f[1:])))


def receipt():
    rows = []
    controls = {}
    for r in range(4):
        L = 2*r+4
        by_data = defaultdict(list)
        key_to_data = {}
        accepted = set()
        for w in multiset_words((4,)+(2,)*r):
            M = extract(w, r)
            assert reconstruct(M) == w and extract(reconstruct(M), r) == M
            d = datum(w)
            k = matching_key(w)
            if k in key_to_data:
                assert key_to_data[k] == d
            key_to_data[k] = d
            by_data[d].append(w)
            front, outer = map(connected_by_cuts, resolve(w))
            original = injective(w, ((0, 1, 0, 1),)+((0, 1),)*r)
            assert original == (front and outer)
            if original:
                accepted.add(w)
            if front != outer:
                controls.setdefault('single_resolution', dict(word=w, folded=original, front=front, outer=outer))
        assert len(set(key_to_data.values())) == len(key_to_data)
        independent_matchings = set(unlabeled_matchings(r))
        assert independent_matchings == set(key_to_data)
        expected_matching_count = comb(L, 4)*prod(range(1, 2*r, 2))
        assert len(by_data) == expected_matching_count
        J = 0
        reps = []
        for d, fiber in by_data.items():
            rep = min(fiber)
            reps.append(rep)
            renamed = {tuple(0 if a == 0 else p[a-1]+1 for a in rep)
                       for p in permutations(range(r))}
            assert renamed == set(fiber)
            assert len(fiber) == factorial(r)
            values = {w in accepted for w in fiber}
            assert len(values) == 1
            J += next(iter(values))
            assert all(datum(w) == d for w in renamed)
        assert len(accepted) == factorial(r)*J
        assert J == (0, 0, 2, 110)[r]
        rooted = set()
        orbits = Counter()
        for w in accepted:
            base = literal_trace(w, ((0, 1, 0, 1),)+((0, 1),)*r)
            for bits in product((0, 1), repeat=r+1):
                trace = tuple(tuple(x^b for x, b in zip(v, bits)) for v in base)
                assert trace[0] == bits
                assert axis_word(trace) == w
                assert len(set(trace)) == L
                assert trace not in rooted
                rooted.add(trace)
                orbits[canonical(trace)] += 1
        assert len(rooted) == 2**(r+1)*factorial(r)*J
        assert set(orbits.values()) <= {2*L}
        adjacency_profiles, adjacency_orbits = graph_cycles([E]*(r+1), L)
        actual_cycles = {cycle for cycle in adjacency_orbits
                         if tuple(Counter(axis_word(cycle))[a] for a in range(r+1)) == (4,)+(2,)*r}
        assert actual_cycles == set(orbits)
        assert len(orbits) == adjacency_profiles[(4,)+(2,)*r]
        assert len(orbits)*L == 2**r*factorial(r)*J
        if accepted:
            assert len(accepted)-1 != factorial(r)*J
            controls['omitted_accepted_word'] = dict(edge_axes=r, correct=len(accepted), truncated=len(accepted)-1)
        rows.append(dict(edge_axes=r, length=L, profile_words=sum(map(len, by_data.values())),
                         canonical_unlabeled_data=len(by_data), independent_endpoint_matchings=len(independent_matchings),
                         label_fiber_size=factorial(r), accepted_unlabeled_data=J,
                         accepted_labeled_words=len(accepted), rooted_inputs=len(rooted),
                         distinct_product_traces=len(rooted), ordinary_cycle_orbits=len(orbits),
                         independent_adjacency_cycles=len(actual_cycles)))
    for w, r in (((0,)*6, 1), ((0,)*5, 0), ((0, 0, 0, 0, 1, 2), 1)):
        try:
            extract(w, r)
        except ValueError:
            pass
        else:
            raise AssertionError(('malformed word accepted', w, r))
    for M in (((0, 1, 2, 3), ((3, 4),)), ((0, 1, 2, 4), ()), ((1, 0, 2, 3), ()), ((0, 1, 2), ())):
        try:
            reconstruct(M)
        except ValueError:
            pass
        else:
            raise AssertionError(('malformed matching accepted', M))
    # The generic quotient count requires acceptance stable on each data fiber.
    fiber = {(0, 1, 0, 2, 0, 1, 0, 2), (0, 2, 0, 1, 0, 2, 0, 1)}
    unstable_count = sum(w[1] == 1 for w in fiber)
    assert unstable_count == 1 and unstable_count != factorial(2)
    controls['unstable_predicate'] = dict(fiber_size=2, accepted_labels=unstable_count,
                                          predicate='the first nonzero label is 1')
    controls['missing_label_factor'] = dict(edge_axes=3, correct_labeled_words=660, wrong=110)
    controls['malformed_inputs_rejected'] = dict(words=3, matchings=4)
    return dict(scope='finite observations; general word/data cardinality is separately proved in Lean',
                rows=rows, negative_controls=controls,
                remaining_general_proof='identify rooted inputs with the full product-sector trace inventory and transport its ordinary-cycle quotient')


if __name__ == '__main__':
    print(json.dumps(receipt(), indent=2))
