"""Finite vertex-partition inversion, independent of coordinate-word kernels.

H(rho) is the number of closed walks constant on every block of rho, i.e.
hom(C_m/rho, X). An unrestricted walk histogram supplies H by a finite zeta
transform. No discrete-kernel count is used as the answer to inversion.
"""
from collections import Counter, defaultdict
from functools import cache
from itertools import product
from math import factorial


@cache
def partitions(n):
    """Every partition of range(n), once, as a restricted-growth tuple."""
    if n < 0:
        raise ValueError('negative size')
    if not n:
        return ((),)
    return tuple(p + (a,) for p in partitions(n-1)
                 for a in range(max(p, default=-1)+2))


def blocks(partition):
    result = [[] for _ in range(max(partition, default=-1)+1)]
    for i, a in enumerate(partition):
        result[a].append(i)
    return result


def normalize(values):
    seen = {}
    return tuple(seen.setdefault(x, len(seen)) for x in values)


def refines(rho, kappa):
    return all(rho[i] != rho[j] or kappa[i] == kappa[j]
               for i in range(len(rho)) for j in range(i))


def mobius(partition):
    """mu(discrete, partition) = product_B (-1)^(|B|-1)(|B|-1)!."""
    value = 1
    for block in blocks(partition):
        value *= (-1)**(len(block)-1) * factorial(len(block)-1)
    return value


@cache
def refinements(kappa):
    """Cartesian product of the partition lattices on kappa's blocks."""
    bs = blocks(kappa)
    result = []
    for local in product(*(partitions(len(b)) for b in bs)):
        labels = [None]*len(kappa)
        for a, (b, p) in enumerate(zip(bs, local)):
            for i, label in zip(b, p):
                labels[i] = (a, label)
        result.append(normalize(labels))
    return tuple(result)


def quotient_homs(adjacency, partition, profile=None):
    """Direct quotient CSP oracle: block assignments may coincide.

    Edge occurrences retain multiplicity and their coordinate-axis mark.
    There is no injectivity test or normalization/root/orientation quotient.
    This intentionally slow reference validates the zeta route on small cases.
    """
    b = max(partition, default=-1)+1
    edges = [(partition[i], partition[(i+1) % len(partition)])
             for i in range(len(partition))]
    if any(u == v for u, v in edges):
        return 0
    unique = set(tuple(sorted(e)) for e in edges)
    neighbors = [set() for _ in range(b)]
    for u, v in unique:
        neighbors[u].add(v)
        neighbors[v].add(u)
    order = []
    while len(order) < b:
        order.append(max((v for v in range(b) if v not in order),
                         key=lambda v: (len(neighbors[v].intersection(order)), len(neighbors[v]), -v)))
    assigned = {}
    answer = 0
    def assign(k):
        nonlocal answer
        if k == b:
            counts = Counter(adjacency[assigned[u]][assigned[v]] for u, v in edges)
            if profile is None or tuple(counts[a] for a in range(len(profile))) == tuple(profile):
                answer += 1
            return
        u = order[k]
        fixed = [assigned[v] for v in neighbors[u] if v in assigned]
        candidates = set(adjacency[fixed[0]]) if fixed else range(len(adjacency))
        for v in candidates:
            if all(v in adjacency[w] for w in fixed):
                assigned[u] = v
                assign(k+1)
                del assigned[u]
    assign(0)
    return answer


def invert(histogram, length):
    """Explicit H(rho), mu*H sum and a by-block-count cancellation ledger."""
    homs = Counter()
    for kappa, count in histogram.items():
        if len(kappa) != length or count < 0:
            raise ValueError('malformed equality histogram')
        for rho in refinements(kappa):
            homs[rho] += count
    ledger = defaultdict(int)
    for rho, count in homs.items():
        ledger[max(rho)+1] += mobius(rho)*count
    return sum(ledger.values()), homs, dict(sorted(ledger.items()))
