# Repeated-edge resolutions and complete next-to-top support

Internal research note, 2026-10-30. **Working general finite identities**,
with exact finite evaluations and a formal collision component. The candidate
contribution is the two-resolution translation and its factor-motif assembly.
Priority and independent mathematical acceptance remain open. Source-owned
support bounds and top-support coefficients retain their pinned ownership.

## Finite matching formula

Fix an integer r>=0 and L=2r+4. In profile (4,2^r), let A_r be the coefficient
for a selected edge traversed four times in the distinguished coordinate,
with each other selected edge traversed twice. All edges are selected
noninduced copies. Define J_r by the following finite sum:

1. Choose four positions F={a<b<c<d} in {0,...,L-1}.
2. Choose a perfect matching M of the remaining 2r positions, without labels.
3. Count (F,M) precisely when **both** chord intersection graphs are connected:

       M union {(a,b),(c,d)},     M union {(a,d),(b,c)}.

Chords (u,v) and (x,y), with smaller endpoint first, intersect precisely when
u<x<v<y or x<u<y<v. Then

    A_r = 2^r r! J_r / (2r+4).                              (1)

This is an exact finite sum, not a closed scalar recurrence or an efficient
large-r algorithm. The implementation examines binomial(2r+4,4)(2r-1)!!
diagrams; the empty matching count at r=0 is one. It avoids enumerating the
r! labelings of the remaining axes, and constructs no product graph.

## Collision proof

Start with a labeled axis word of multiplicities (4,2^r). The distinguished
coordinate follows the departure template 0101; its four events alternate
the endpoints of a single edge. Replace those four events, in occurrence
order, by 0011 for the first resolution and 0110 for the second. Every new
axis then occurs twice. Keep the original other axes distinct from both
new axes.

For a position before a step, p in {0,1,2,3,4} is the number of preceding
distinguished events. Its folded coordinate and resolved parity pairs are:

| p | Folded edge state | First resolution | Second resolution |
|---:|---:|---|---|
| 0 | 0 | (0,0) | (0,0) |
| 1 | 1 | (1,0) | (1,0) |
| 2 | 0 | (0,0) | (1,1) |
| 3 | 1 | (0,1) | (1,0) |
| 4 | 0 | (0,0) | (0,0) |

Direct inspection gives, for any two phases p,q,

    folded(p)=folded(q)
       iff first(p)=first(q) OR second(p)=second(q).       (2)

The rest of the product vertex is identical in the three traces. Thus two
departure vertices coincide in the original trace iff they coincide in at
least one resolution. Negating over distinct departure positions proves

    original injective iff first injective AND second injective. (3)

Closure is automatic from the step budgets, and each step follows its
selected edge. Only departure positions 0,...,L-1 are tested; the final return
to the root is not an additional cycle vertex. Consequently (3) distinguishes
simple cycles from closed walks exactly, including cyclic intervals across
the chosen root. A fixed initial coordinate assignment does not affect
collisions.

For a word with each axis twice, a collision occurs precisely when a nonempty
proper consecutive interval contains zero or two endpoints of every chord.
The established connected-pairing characterization identifies absence of
such an interval with connectivity of the chord intersection graph. One
direction is immediate: a whole-chord interval disconnects those chords
from its complement. Conversely, distinct noncrossing components of the
intersection graph have a nonempty component together with its enclosed
components occupying a proper consecutive endpoint interval. This is the
usual connected-partition decomposition; it is not a new chord-diagram
connectivity theorem here. Tests independently compare intersection
connectivity with every proper endpoint interval through five chords.

The four distinguished positions and unlabeled matching determine an original
axis word up to r! assignments of the other labeled axes. Hence the accepted
word count is exactly r! J_r. Each word admits 2^(r+1) initial endpoint choices.
An injective length-L cycle has exactly 2L rooted directed traversals. Dividing
2^(r+1) r! J_r by 2L proves (1). Root-dependent word classes are combined
before division; no individual resolution or wedge category is divided
separately. The fixed-trace root/direction representation theorem is already
formalized in RootedCycle; global inventory transport remains prose.

## Complete sector one below maximum support

Reuse the source support bound for ordinary C_(2k): at most k coordinates
can be active, since a nonconstant closed projection in a simple graph has
at least two steps. Exactly k-1 active coordinates leave two excess steps.
There are only two multiplicity shapes:

- (4,2^(k-2));
- (3,3,2^(k-3)), the latter when k>=3.

A closed four-step projection has exactly the equality patterns 0101,
0102, 0121, 0123. They use a selected edge, a selected wedge (both middle
patterns together), or a selected square. The odd three-step projection is
necessarily a selected triangle, not an edge backtrack. Reuse the established
simple-sector coefficient S_r and paired-triangle coefficient B_s from
`simple-projection-sectors.md`, and the wedge coefficient W_r from
`wedge-coarsening.md`. For arbitrary finite simple undirected factors:

    F_(4,2^r)(G;H_1,...,H_r)
      = [A_r e(G) + W_r w(G) + S_r s(G)] product_i e(H_i),  (4)

    F_(3,3,2^s)(G,H;J_1,...,J_s)
      = B_s t(G)t(H) product_i e(J_i).                    (5)

Here r=k-2 and s=k-3; W_r=(T_(r+2)-S_r)/4 retains upstream
ownership of T. Sum over every allocation of active coordinates and multiply
by the vertex count of every inactive factor. `near_top_profiles` implements
exactly this sector, including the boundary k=2 where only a single selected
square contributes. Extra host edges do not invalidate selected copies.

Every product cycle recovers its local selected projected edge sets uniquely.
Replacing those finite selected motifs by abstract copies preserves and
reflects all product vertex equalities. Their disjoint classes therefore
justify summing (4) and (5). This completes a **working all-length formula
for exactly k-1 support**, not all smaller support and not a new top-symbol
result. A rational expression with a proved exact denominator is used only
for the finite integer cardinality quotient in (1).

## Exact observations and controls

| r | L | J_r | A_r |
|---:|---:|---:|---:|
| 0 | 4 | 0 | 0 |
| 1 | 6 | 0 | 0 |
| 2 | 8 | 2 | 2 |
| 3 | 10 | 110 | 528 |
| 4 | 12 | 3381 | 108192 |
| 5 | 14 | 89782 | 24625920 |

These are finite evaluations, not an extrapolated recurrence. Literal
alternating-edge collision tests compare **every word**, including rejected
words, through r=3. Independent product-adjacency DFS verifies A_r for r=0..4,
including 108192 distinguished-profile twelve-cycles in Q5. The r=5 entry is
not an independent product enumeration. The receipt records both kinds of
evidence separately. All original c8 support-three strata and the existing
c10 support-four corpus agree profile by profile with the assembled formula.

For example the resulting length-twelve formula is

    F_(4,2,2,2,2) = (108192e + 663168w + 2780928s) e e e e,
    F_(3,3,2,2,2) = 9337536 t t e e e.

Independent adjacency DFS also gives 879552 for the same repeated-coordinate
profile in P3 square Q4, 5866368 in C4 square Q4, and 9337536 for the paired
profile in K3 square K3 square Q3. P3 has two edges and one wedge; C4 has
four edges, four wedges and one square. Thus these observations independently
isolate W_4=879552-2A_4=663168 and
S_4=5866368-4A_4-4W_4=2780928, while the paired product isolates B_3.
These are finite corroboration of every coefficient in this row, separate
from the all-length proofs.

The DFS remains independent of motifs, matching diagrams and axis words.
It prunes a step when it exhausts that coordinate's budget without returning
the coordinate to its root value: no later step can repair that coordinate.
This preserves exactly the closed walks under consideration. The mandatory
replay checks all earlier receipt bytes again after this optimization.

The receipt supplies explicit words accepted by only one resolution but
rejected by the literal folded collision test. A first-resolution-only count
and a second-resolution-only count are both invalid. Existing controls also
retain Q4 c8=696 rather than the top-only648, c10 Q4=2112 rather than zero,
and the failure of unfiltered paired-triangle walks divided by20.

## Formal and literature boundaries

`formal/RepeatedEdge.lean` proves (2), its product-state form, and (3) for
arbitrary finite traces, using no axioms in these three declarations. Four
finite controls (exact propext audit) certify that either single resolution
can miss collisions, the full endpoint returns, and unequal remaining
coordinates prevent a collision. The subsequent [literal-word bridge](even-edge-resolutions.md) now formalizes
the four-event word-prefix instantiation and exact inventory transport.
Connected matching characterization/enumeration, selected-motif classification
and the all-graph cardinality quotient remain prose components. They remain explicit prose
components, not consequences of the seven declaration audits alone.

Connected pairings and connected partitions are prior work: Franz Lehner,
[Free cumulants and enumeration of connected partitions](https://arxiv.org/abs/math/0110030),
European Journal of Combinatorics23(2002),1025-1031. Related chord-diagram
bijections are developed by Courtiel, Yeats and Zeilberger,
[Connected Chord Diagrams and Bridgeless Maps](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v26i4p37),
Electronic Journal of Combinatorics26(4)(2019),P4.37. Their established
connectivity machinery is context, not a claimed new result. Hypercube
specializations also require prior-art attribution; these numerical values
are not claimed new. Searches for the two-resolution translation and mixed
factor-motif formulas have not established priority. Independent review of
(1), (3)-(5), and a broader literature comparison remain open.
