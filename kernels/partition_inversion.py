"""Independent, integer-only profile oracle via partition-lattice inversion.

No imports from the shuffle, motif, DFS or pinned source kernels. Quotient
homomorphisms may identify different blocks; their signed sum enforces global
injectivity. Parallel quotient edges retain their original multiplicities.
"""
from collections import Counter
from functools import lru_cache
from itertools import permutations, product
from math import factorial, prod


def partitions(n):
    """All partitions of range(n), built by insertion of the last element."""
    if n == 0:
        yield ()
        return
    for blocks in partitions(n-1):
        for j in range(len(blocks)):
            yield blocks[:j] + (blocks[j] + (n-1,),) + blocks[j+1:]
        yield blocks + ((n-1,),)


def mobius(blocks):
    return prod((-1)**(len(b)-1)*factorial(len(b)-1) for b in blocks)


def quotient(blocks):
    """Weighted selected-edge quotient of C_m; None denotes a loop."""
    m = sum(map(len, blocks))
    label = {v: j for j, block in enumerate(blocks) for v in block}
    edges = Counter()
    for v in range(m):
        a, b = label[v], label[(v+1) % m]
        if a == b:
            return None
        edges[tuple(sorted((a, b)))] += 1
    return tuple((a, b, w) for (a, b), w in sorted(edges.items()))


def canonical_edges(n, edges):
    # Finite relabeling only; edge multiplicities are part of the key.
    return min(tuple(sorted((min(p[a], p[b]), max(p[a], p[b]), w)
                            for a, b, w in edges))
               for p in permutations(range(n)))


@lru_cache(None)
def quotient_terms(m):
    """Group isomorphic multigraphs, summing their signed coefficients."""
    terms = Counter()
    loopless = 0
    for blocks in partitions(m):
        edges = quotient(blocks)
        if edges is not None:
            loopless += 1
            terms[(len(blocks), canonical_edges(len(blocks), edges))] += mobius(blocks)
    return tuple(sorted((n, edges, c) for (n, edges), c in terms.items() if c)), loopless


def colored_product(factors):
    """Construct the host independently, with one axis color per edge."""
    for g in factors:
        if any(u in ns or any(not 0 <= v < len(g) or u not in g[v] for v in ns)
               for u, ns in enumerate(g)):
            raise ValueError('Expected finite simple undirected factors')
    vertices = tuple(product(*(range(len(g)) for g in factors)))
    index = {v: i for i, v in enumerate(vertices)}
    adj = [dict() for _ in vertices]
    for i, v in enumerate(vertices):
        for a, g in enumerate(factors):
            for w in sorted(g[v[a]]):
                adj[i][index[v[:a] + (w,) + v[a+1:]]] = a
    return adj


def hom_profiles(n, edges, adj, base):
    """Multigraph homomorphism polynomial by frontier dynamic programming.

    A profile is packed in base m+1, so adding edge exponents never carries.
    Only assigned vertices incident to an unassigned vertex enter the cache.
    No distinctness constraint is imposed on quotient-vertex assignments.
    """
    neighbors = [dict() for _ in range(n)]
    for a, b, w in edges:
        neighbors[a][b] = neighbors[b][a] = w
    order = []
    while len(order) < n:
        u = max((v for v in range(n) if v not in order),
                key=lambda v: (sum(a in order for a in neighbors[v]), len(neighbors[v]), -v))
        order.append(u)
    frontiers = [tuple(u for u in order[:i] if any(v in neighbors[u] for v in order[i:]))
                 for i in range(n+1)]

    @lru_cache(None)
    def solve(i, values):
        if i == n:
            return ((0, 1),)
        assigned = dict(zip(frontiers[i], values))
        u = order[i]
        prior = [(assigned[v], w) for v, w in neighbors[u].items() if v in assigned]
        if prior:
            candidates = set(adj[prior[0][0]])
            for v, _ in prior[1:]:
                candidates.intersection_update(adj[v])
        else:
            candidates = range(len(adj))
        result = Counter()
        for image in sorted(candidates):
            shift = sum(w * base**adj[v][image] for v, w in prior)
            assigned[u] = image
            following = tuple(assigned[v] for v in frontiers[i+1])
            for p, count in solve(i+1, following):
                result[p+shift] += count
        return tuple(sorted(result.items()))

    return Counter(dict(solve(0, ())))


def inventory(factors, m=8):
    """Signed quotient sum, ordinary cycles, and raw closed-walk profiles."""
    if m < 3:
        raise ValueError('Ordinary simple cycles require length at least three')
    adj = colored_product(factors)
    terms, _ = quotient_terms(m)
    signed = Counter()
    closed = Counter()
    for n, edges, coefficient in terms:
        polynomial = hom_profiles(n, edges, adj, m+1)
        if n == m:
            closed = polynomial
        for p, count in polynomial.items():
            signed[p] += coefficient * count

    def unpack(p):
        return tuple(p // (m+1)**a % (m+1) for a in range(len(factors)))

    rooted = {unpack(p): c for p, c in signed.items() if c}
    if any(c < 0 or c % (2*m) for c in rooted.values()):
        raise ArithmeticError('Inversion did not yield nonnegative cycle multiples')
    return {'ordinary': Counter({p: c//(2*m) for p, c in rooted.items()}),
            'rooted_injective': Counter(rooted),
            'rooted_closed': Counter({unpack(p): c for p, c in closed.items() if c})}
