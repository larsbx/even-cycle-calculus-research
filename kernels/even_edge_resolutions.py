"""Simultaneous alternating-pair resolutions of finite even edge profiles.

Every coordinate projects to ONE selected edge; other motifs are outside this
sector. Connectivity machinery and top-support specialization are prior work.
The all-profile collision translation is in proof/even-edge-resolutions.md.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from math import factorial, prod
from kernels.repeated_edge import crossing_connected


def block_partitions(profile):
    """Unlabeled blocks, grouped by size and ordered by least vertex per size.

    Sizes are supplied sorted; equal-size blocks have strictly increasing least
    vertices. This removes just the label permutations within equal-size groups.
    """
    def visit(remaining, index, least):
        if index == len(profile):
            if not remaining:
                yield ()
            return
        size = profile[index]
        for block in combinations(remaining, size):
            if index and size == profile[index-1] and block[0] <= least:
                continue
            rest = tuple(v for v in remaining if v not in block)
            for tail in visit(rest, index+1, block[0]):
                yield (block,)+tail
    yield from visit(tuple(range(sum(profile))), 0, -1)


def pairing(block, shifted):
    """Two alternating adjacent pairings around this even cyclic block."""
    if shifted:
        return ((block[0], block[-1]),)+tuple(zip(block[1:-1:2], block[2:-1:2]))
    return tuple(zip(block[::2], block[1::2]))


def all_resolutions_connected(blocks):
    """Repeated two-event blocks have one resolution; longer blocks have two."""
    for choices in product(*(range(1 if len(b) == 2 else 2) for b in blocks)):
        chords = tuple(c for block, shifted in zip(blocks, choices)
                       for c in pairing(block, shifted))
        if not crossing_connected(chords):
            return False
    return True


def checked_profile(profile):
    profile = tuple(profile)
    if not profile or any(type(d) is not int or d < 2 or d % 2 for d in profile):
        raise ValueError('Expected a nonempty finite profile of positive even integers')
    if sum(profile) < 4:
        raise ValueError('Ordinary even cycles have length at least four')
    return tuple(sorted(profile))


@lru_cache(None)
def _unlabeled_count(profile):
    return sum(all_resolutions_connected(blocks) for blocks in block_partitions(profile))


def unlabeled_count(profile):
    return _unlabeled_count(checked_profile(profile))


def even_edge_coefficient(profile):
    """All cycles of this profile projecting to one selected edge per axis.

    For labeled host axes the answer multiplies their selected edge counts and
    inactive vertex fibers. For a two-event-only profile this evaluates the
    source-owned top coefficient without claiming ownership of that theorem.
    """
    profile = checked_profile(profile)
    count = _unlabeled_count(profile)
    labelings = prod(factorial(n) for n in Counter(profile).values())
    numerator = 2**len(profile)*labelings*count
    value, remainder = divmod(numerator, 2*sum(profile))
    assert remainder == 0
    return value


def _parts(total, lower=1, slots=None):
    if total == 0:
        yield ()
    elif slots:
        for a in range(lower, total+1):
            for tail in _parts(total-a, a, slots-1):
                yield (a,)+tail


def cube_profile_totals(dimension, length):
    """Totals by unordered active-step profile in Q_d, including unused fibers.

    This enumerates finite profile partitions and joint-connected diagrams.
    It is not a polynomial-time cycle-count algorithm or a new top theorem.
    """
    if type(dimension) is not int or dimension < 0:
        raise ValueError('Expected a nonnegative integer cube dimension')
    if type(length) is not int or length < 4 or length % 2:
        raise ValueError('Expected an even integer cycle length >= 4')
    out = Counter()
    for half_profile in _parts(length//2, slots=dimension):
        profile = tuple(2*a for a in half_profile)
        q = len(profile)
        allocations = factorial(dimension)//factorial(dimension-q)//prod(
            factorial(n) for n in Counter(profile).values())
        out[profile] = 2**(dimension-q)*allocations*even_edge_coefficient(profile)
    return +out
