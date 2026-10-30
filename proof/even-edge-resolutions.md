# Simultaneous pairing resolutions for every even selected-edge profile

Internal research note, 2026-10-30. **Working general finite identities.**
The contribution proposed for review is the simultaneous resolution criterion
and its selected-edge-sector counting translation. Priority and independent
mathematical acceptance remain open. Connected pairings, standard hypercube
counts, the support bound and the top-symbol theorem are prior work. This
note reuses them; it does not assign them a second theorem owner.

## General collision criterion

Let a labeled axis word have positive even multiplicities
D=(2m_1,...,2m_q), with each m_a>=1 and L=sum D>=4. In this sector each
coordinate alternates the endpoints of **one selected edge**, however many
times that axis occurs. The departure vertices are indexed 0,...,L-1; the
final root return is not an additional cycle vertex.

For an axis with ordered event positions v_1<...<v_(2m), use these two pairings:

    R0 = {(v_1,v_2),(v_3,v_4),...,(v_(2m-1),v_(2m))},
    R1 = {(v_1,v_(2m)),(v_2,v_3),...,(v_(2m-2),v_(2m-1))}.

Replace each paired event couple by its own new labeled edge axis. Each
resolved axis occurs exactly twice. Make the R0/R1 choices independently in
each original coordinate. Then

    original departure trace is injective
      iff EVERY simultaneous resolution has an injective departure trace
      iff EVERY resolved chord intersection graph is connected.       (1)

An axis used twice has identical R0 and R1, so it needs only one choice.
If h original axes occur more than twice, at most 2^h diagrams are tested.
Two globally constant choices are insufficient in general.

### Proof by local prefix states

After p events of an axis, 0<=p<=2m, the original endpoint is determined by
p modulo 2. The resolved parity states, indexed j=0,...,m-1, are

    F_m(p)_j = [p=2j+1],
    H_m(p)_0 = [0<p<2m],
    H_m(p)_j = [p=2j] for j>0.

Brackets denote an exact Boolean indicator. These descriptions follow by
reading the first and second occurrence of each paired axis; both occurrences
cancel. Thus

    p mod2 = s mod2
      iff F_m(p)=F_m(s) OR H_m(p)=H_m(s).                 (2)

If both phases are even, their F vectors are zero. If both are odd, their H
vectors have exactly their zeroth entry true. Conversely F equality cannot
identify an odd phase with an even phase: an odd p has its unique true entry
at (p-1)/2. H equality cannot do so either. Its odd phase has only the wrap
entry true; an even phase has either a zero wrap entry (at 0 or 2m), or an
additional true entry at p/2. This proves (2) for all finite m>=1.

Two original product vertices coincide iff their endpoint parities agree
in every axis. Apply (2) independently in each axis. For each coordinate
select a resolution witnessing its equality, giving **one simultaneous
resolution** in which these two full product vertices coincide. Conversely,
a collision in any simultaneous resolution reflects endpoint parity equality
in every original axis. Therefore

    original collision at s,t iff SOME resolution collides at s,t.

Negating over unequal departure indices proves the first equivalence in (1).
The choice can depend on the candidate pair s,t. This is why injectivity of
all resolutions is required, rather than injectivity of one chosen resolution
or merely the two constant choice vectors. The Lean proof constructs the
choice by finite decidable equality of coordinate vectors; it does not use
an axiom of choice.

For a resolved word, every axis has two events. Equality of departure vertices
means precisely that the intervening proper interval contains zero or two
events of every resolved axis. The established connected-pairing criterion
identifies absence of such an interval with connectivity of the chord
intersection graph. This gives the second equivalence in (1). Wrapped
intervals introduce no missing case: their complements are linear intervals
with the same parity. All graphs and index families in the argument are finite.

## Exact coefficient for arbitrary even edge multiplicities

Let n_d be the number of original axes with multiplicity d. Let U(D) count
partitions of {0,...,L-1} into **unlabeled** blocks with size multiset D,
accepted exactly when every simultaneous alternating resolution is connected.
Implement this without label overcounting by grouping blocks by size and
ordering equal-size blocks by their least event position. Then

    E(D) = 2^q * (product_d n_d!) * U(D) / (2L).           (3)

For fixed labeled host axes G_1,...,G_q, the ordinary-cycle contribution whose
coordinate projections each use exactly one selected edge is

    E(D) * product_a e(G_a),                              (4)

times the vertex counts of inactive factors. This is a sector of the full
formula when host factors have other motifs or permit odd projections.
It is the entire fixed-profile count when every active factor is K2.

To prove (3), each unlabeled block partition has exactly product n_d!
assignments to the original labeled axes of the specified profile. Every
accepted word has 2^q choices of initial edge endpoints. Those choices
preserve the collision relation and produce all rooted directed traversals
in this selected-edge class. Each ordinary injective L-cycle has exactly 2L
representations. The fixed-trace multiplicity theorem already proved in
RootedCycle supplies that standard factor; full graph-inventory cardinality
transport remains a prose component. Combine all classes before division.
Equation (1) makes the accepted objects simple cycles, not merely closed walks.
Selected edges are recovered uniquely from projections, proving (4), with no
induced-copy condition or restriction on extra host edges.

For D=(4,2^r), U(D) is the existing J_r and (3) is precisely the earlier
A_r=2^r*r!*J_r/(2r+4). For all d=2, this evaluates the source-owned top
coefficient using established connected pairings; that specialization is
only a regression, not a newly owned top-support theorem.

`kernels/even_edge_resolutions.py` enumerates finite block partitions and
intersection graphs. It constructs no graph product and imports no shuffle
or literal collision kernel. It is exponential enumeration, not an efficient
scalar recurrence. Formal enumeration completeness and efficiency improvements
remain open.

## Cube specialization and new finite lower-support checks

All coordinate projections in Q_d are selected-edge projections. For a
multiset D of q active even multiplicities, the ordinary-cycle total over
all distinct coordinate allocations and inactive fibers is

    2^(d-q) * d! / ((d-q)! product n_s!) * E(D).           (5)

Summing (5) over positive even multisets of total L and q<=d therefore gives
all ordinary L-cycles in Q_d. This is a finite enumeration identity, not a
new assertion about the known numerical cube counts.

| Fixed labeled profile D | U(D) | E(D) | Independent product-adjacency DFS |
|---|---:|---:|---:|
| (4,2,2) | 2 | 2 | 2 |
| (4,2,2,2) | 110 | 528 | 528 |
| (6,2,2,2) | 8 | 32 | 32 |
| (4,4,2,2) | 306 | 816 | 816 |

The final two rows are twelve-cycle strata using four coordinates: support
two below the maximum, beyond the previous k-1-support formula. They are
finite observations, each checked independently on product adjacency. They
do not supply the omitted wedge/square or six-step-motif terms for arbitrary
host factors.

A twelve-cycle in Q4 cannot use three or fewer coordinates, since such a
subcube has at most 8 vertices. Four positive even multiplicities summing to 12
have just the last two displayed shapes. Consequently the independent DFS
strata and (5) both give

    C_12(Q4) = 4*32 + 6*816 = 5024.

The receipt also recovers Q3 c8=6, the immutable Q4 c8=696 with its 648+48
split, and Q4 c10=2112. All six earlier receipts are retained unchanged.
The cube counts are known specializations, not numerical novelty claims.

### Negative controls

For blocks

    (1,6), (0,2,4,8), (3,5,7,9),

the four choices in the last two axes, in order 00,01,10,11, give connectedness

    true, true, false, true.

Thus testing only choices 00 and 11 accepts a nonsimple folded closed walk.
The receipt records the literal axis word and checks its collision separately.
The general Lean finite control similarly gives two equal original product
vertices separated by each constant resolution, but identified by a mixed
choice. This demonstrates the quantifier issue in (1).

Top-support-only and top-plus-next-support-only formulas both return zero
for c12 in Q4, since Q4 has neither six nor five coordinates. The actual count
5024 is entirely lower support. Also, the selected-edge sector in K3 square K3
at length 8 is zero (two fixed edge projections provide at most 4 vertices),
while its original ordinary total is 81. Thus (4) cannot be promoted to a full
arbitrary-factor cycle formula.

## Formal verification and remaining obligations

`EvenResolutionPhase.lean` proves eleven general finite statements, including
(2), collision reflection, an explicit witnessing simultaneous choice, and
injectivity iff every choice is injective. Four controls cover six-event state
vectors, empty-vector behavior, phases beyond the stated bound and the failure
of constant choices. Empty-vector behavior is not a claim that positivity is
a logically minimal assumption when both phase bounds are also imposed.
Constructive finite function equality avoids classical choice. The general
statements and mixed-choice control have exactly propext/Quot.sound;
six-event vectors use no axioms, and the other two controls use exactly
Quot.sound.

`ResolvedWords.lean` additionally closes the earlier four-event prefix gap.
For arbitrary finite Option(Fin r) words it defines the actual 0011 and 0110
resolutions and Boolean replays; proves length and take-prefix preservation,
monotone prefix budgets, original/resolved replay formulas, pointwise collision
and injectivity equivalences; and transports the exact (4,2^r) event inventory
to two-event inventories. Sixteen general declarations and three controls are
checked. This is an all-r literal-word component, beyond a finite phase table.

The actual event-pair-to-prefix-vector instantiation for arbitrary m, connected
matching characterization/enumeration, unlabeled block-partition cardinalities,
selected-motif extraction and global ordinary-cycle quotient are still prose
components. The formal general-phase theorem does not by itself certify the
Python coefficient evaluator. The full graph formula, independent mathematical
acceptance and priority remain open; numerical checks do not close those gates.

## Literature boundary

Franz Lehner's [Free cumulants and enumeration of connected partitions](https://arxiv.org/abs/math/0110030),
European Journal of Combinatorics23(2002),1025-1031, defines connected
partitions by exclusion of proper block intervals and attributes that subject
to earlier work. We use only its finite combinatorial context here. The
source-owned graph-product-ring results supply top support and symbols.
Known cube cycle enumerations are comparison targets, not candidate novelty.

Targeted searches on 2026-10-30 for repeated-coordinate cube cycles, alternating
pairings and joint-connected chord diagrams did not establish priority for
(1)-(4). A broader literature comparison and independent review of this
factor-sector translation remain necessary. Searches finding no exact match
are not acceptance evidence.
