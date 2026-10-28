# Complete c8 lower-support decomposition

Working mathematical derivation, 2026-10-27. Exact finite coefficients have
replayable certificates. The [coordinate collision bridge](coordinate-collision-bridge.md)
formally verifies the specified finite graph-level decoding components; the
complete extraction/counting bijection below remains a prose proof. This is
not a novelty claim, external mathematical acceptance, or a formalization of
the full graph theorem. Shared support and top-symbol authority stays at
[`graph-product-ring-research@28d0224`](https://github.com/larsbx/graph-product-ring-research/blob/28d022402037274a9fe85c1fd64ecda2532dceb9/proof/even-cycle-order-symbol.md).

## Conventions and notation

Graphs are finite simple undirected graphs, possibly empty or disconnected.
Every motif count below is `inj(H,G)/|Aut(H)|`: ordinary selected-edge copies,
with no inducedness requirement. A path of three edges need not be induced;
a diamond in K4 is counted once for each of its six omitted edges.

| Symbol | Motif | Automorphism order |
| --- | --- | ---: |
| n | vertex | 1 |
| e | edge | 2 |
| w | two-edge path (wedge), equivalently sum_v binom(deg(v),2) | 2 |
| t | triangle | 6 |
| s | square C4 | 8 |
| p | three-edge path P4 | 2 |
| l | C4 with one pendant edge, five vertices | 2 |
| d | diamond K4 minus one edge | 4 |
| b | two triangles sharing exactly one vertex (bowtie) | 8 |
| h | hexagon C6 | 12 |
| a | triangle with one pendant edge (paw) | 2 |
| z | pentagon C5 | 10 |

Symbols with argument G refer to counts in G. Motif edges and exact
automorphism checks are in `kernels/eight_cycles.py` and `tests/`.
Projected walks can backtrack, even when the product cycle is simple.

## Exact profile formulas

Let F_(r1,...,rq)(G1,...,Gq) count ordinary eight-cycles with exactly ri
steps in coordinate i. Each listed coordinate is used. Then:

```
F_(6,2)(G,H) = e(H) [p(G) + 6 l(G) + 2 d(G) + 16 b(G) + 30 h(G)]

F_(3,5)(G,H) = t(G) [18 t(H) + 54 a(H) + 180 z(H)]

F_(4,4)(G,H) = 2 [e(G)s(H) + s(G)e(H)] + 5 w(G)w(H)
                + 40 [w(G)s(H) + s(G)w(H)] + 248 s(G)s(H)

F_(4,2,2)(G,H,J) = [2 e(G) + 60 w(G) + 408 s(G)] e(H)e(J)

F_(2,3,3)(G,H,J) = 1404 e(G)t(H)t(J).
```

Coordinate permutations give F_(2,6), F_(5,3), and the other ordered
three-coordinate profiles. In particular three-step projections are triangles;
an even total length does **not** require each coordinate length to be even.

For a finite family G1,...,Gq, the full ordinary count is

```
c8(product_i Gi)
 = sum_i c8(Gi) product_(j != i) n(Gj)
 + sum_(i<j) [F_(6,2)(Gi,Gj) + F_(6,2)(Gj,Gi)
              + F_(3,5)(Gi,Gj) + F_(3,5)(Gj,Gi) + F_(4,4)(Gi,Gj)]
             product_(k outside {i,j}) n(Gk)
 + sum_(i<j<k) sum_(a in {i,j,k})
       [F_(4,2,2)(Ga,Gb,Gc) + F_(2,3,3)(Ga,Gb,Gc)]
             product_(d outside {i,j,k}) n(Gd)
 + 648 sum_(i<j<k<l) e(Gi)e(Gj)e(Gk)e(Gl)
             product_(d outside {i,j,k,l}) n(Gd).
```

In the triple sum {b,c} is the complement of {a} in {i,j,k}; order does
not matter because both expressions are symmetric in b,c. The last line
is **reused from the pinned source**, not a new theorem owned here. The empty
product has one vertex and contributes zero cycles. Empty factors also give
zero, including all fixed-coordinate multiplicities.

## Projection/shuffle bijection and collision proof

1. Root and orient a simple eight-cycle and label its step positions 0,...,7.
   Each product edge changes exactly one coordinate. Deleting stationary
   steps in coordinate a gives a rooted directed closed walk of length ra.
   A used coordinate cannot have length one, because there are no loops.
   Thus there are at most four used coordinates. The positive profiles are
   (8); permutations of (6,2),(5,3),(4,4); permutations of (4,2,2),(3,3,2);
   and (2,2,2,2). This list uses no bipartiteness assumption.
2. Encode the equalities among the ra projected vertex positions by a
   restricted-growth string pi_a: label new vertices in order of first
   appearance. Adjacent cyclic positions have different labels. Its quotient
   graph H(pi_a) has one vertex per label and one edge per distinct consecutive
   label pair. An injective edge-preserving map H(pi_a) -> Ga recovers
   exactly one projected walk of that equality type. Conversely every such
   walk recovers exactly this pattern and this injection. Extra graph edges
   impose no restrictions. Importantly, a noninjective map from H would
   change the equality pattern and must not be counted here. The
   [canonical extraction component](canonical-coordinate-extraction.md)
   now kernel-checks the first-occurrence representation of coordinate
   equality classes. [Ordinal compression](ordinal-rank-compression.md) also
   checks the contiguous label bijection and enumerator append bound;
   [event projection and replay](coordinate-event-shuffle.md) check deletion
   of stationary-coordinate steps for coherent transitions. Closing/edge and
   endpoint conventions and full executable correspondence remain open.
3. The coordinate word w is a shuffle with ra copies of a. Before step u,
   let qa(u) be the number of a's in the preceding u positions. The product
   vertex at u has labels
   `(pi_a[qa(u) mod ra])_a`. Because each quotient map is injective, two
   product vertices at u,v coincide **if and only if** all these labels
   agree. The general typed-coordinate statement is now kernel-checked as
   `ECC.CollisionBridge.decode_equal_iff` and `trace_injective_iff`; the
   connection from the executable shuffle encoding to the typed shape remains
   a separate formal obligation. Let K(pi_1,...,pi_q) be the number of shuffles for which the eight
   label tuples at times 0,...,7 are pairwise distinct. The final vertex
   at time 8 equals the root by coordinate closure.
4. Therefore decoding the patterns, their injections, and a K-admissible
   shuffle gives a rooted directed simple eight-cycle. Extraction and
   decoding are inverse: both the coordinate word and the projected vertices
   are recovered from the product traversal. There is no edge-selection
   overcount, even in graphs with chords. Consequently

```
16 F_r(G1,...,Gq)
  = sum_(pi_a proper restricted-growth strings of length ra)
      K(pi_1,...,pi_q) product_a inj(H(pi_a),Ga).
```

   The action changing root and direction is free: an injective length-eight
   cycle has eight distinct roots and two distinct directions. This proves
   the factor 16. Dividing *noninjective* walks by 16 would not prove an
   ordinary-cycle count.
5. Unused coordinates are arbitrary fixed vertices, so multiply by their
   vertex counts. Every ordinary cycle has exactly one support and profile.
   This proves the assembly formula once the following finite coefficients
   are evaluated. This also agrees with, and does not re-own, the source
   support-defect theorem.

## Finite coefficient evaluation

For a length-four projection the complete pattern list is
`A=0101`, `B=0102`, `C=0121`, `D=0123`. Their injection counts are
`2e, 2w, 2w, 8s`. The two wedge root positions have different K-values,
so they must be distinguished until after collision testing.

For profile (4,2,2), the K-values are respectively **4,44,76,204**.
For (2,3,3), the only tuple is `(01,012,012)` with K=**312**.
For (4,4), rows and columns in A,B,C,D order give:

| K | A | B | C | D |
| --- | ---: | ---: | ---: | ---: |
| A | 0 | 0 | 0 | 2 |
| B | 0 | 2 | 5 | 15 |
| C | 0 | 5 | 8 | 25 |
| D | 2 | 15 | 25 | 62 |

There are 41 proper restricted-growth strings of length six and 11 of length
five. Summing K by the isomorphism class of their quotient graph gives:

| Profile | Projection motif tuple | Sum of K |
| --- | --- | ---: |
| (6,2) | (P4, edge) | 4 |
| (6,2) | (C4 with pendant edge, edge) | 24 |
| (6,2) | (diamond, edge) | 4 |
| (6,2) | (bowtie, edge) | 16 |
| (6,2) | (C6, edge) | 20 |
| (3,5) | (triangle, triangle) | 8 |
| (3,5) | (triangle, paw) | 72 |
| (3,5) | (triangle, C5) | 48 |

All other pattern tuples have K=0. These are complete finite sums, not fits
to the five product counts. Replacing each injection count by its
automorphism order times its ordinary count and dividing by 16 gives the
displayed formulas. For example `(2,3,3)` has coefficient
`312*2*6*6/16 = 1404`, while the two wedge cases in `(4,2,2)` combine to
`(44+76)*2*2*2/16 = 60`.

The derivation algorithm enumerates restricted-growth strings by appending
each label from 0 through one plus the previous maximum, excluding equal
neighbors and excluding equal first/last labels. This enumerates every
cyclic proper equality partition exactly once by its defining first-appearance
rule. The shuffle recursion chooses any coordinate with positive remaining
multiplicity and decrements it; induction on the remaining length proves
that every word of that multiplicity occurs exactly once. The collision test
uses precisely the label tuples in step 3. Thus the finite sums above have
exhaustive certificates, rather than relying on sampled graph inputs.

`conformance/lower-support.json` lists every **nonzero** pattern tuple and
its K, together with aggregate coefficients. Zero terms are recomputed by
`derive`; all 41/11 patterns participate. Independent brute-force generation
checks pattern and shuffle completeness. `formal/Shuffle.lean` certifies the
five finite coefficient tables by kernel evaluation; it does not formalize
the general graph bijection or the length-five/six classification.

## Evaluations and falsified shortcuts

| Product | Support-two | Support-three | Support-four | Total |
| --- | ---: | ---: | ---: | ---: |
| C4 square K2 | 6 | 0 | 0 | 6 |
| K3 square K3 | 81 | 0 | 0 | 81 |
| P3 square K3 | 15 | 0 | 0 | 15 |
| K2 square K3 square K3 | 162 | 2,538 | 0 | 2,700 |
| Q4 | 0 | 48 | 648 | 696 |

For K2 square K3 square K3, the three-coordinate profiles are
`(4,2,2):18`, `(2,4,2):558`, `(2,2,4):558`, `(2,3,3):1404`.
The two-coordinate contribution 162 lies in the two fixed K2 fibers of
K3 square K3. A repeated-edge four-step projection in K2 already contributes
18 cycles, so counting only simple projected squares fails.

Q4's 48 lower-support cycles are eight Q3 fibers with six cycles each;
using just its top symbol loses them. Two triangle projections are mandatory
for `(2,3,3)`. All 560 coordinate shuffles with rooted projected walks give
40,320 closed traversals in K2 square K3 square K3; collision testing removes
17,856, leaving 22,464 = 16*1,404. The naive quotient 40,320/16=2,520 is
wrong for ordinary cycles.

The original corpus is reproduced without altering its bytes. Additional
motif products, Q5, empty/disconnected graphs, unused-coordinate fibers,
relabelings, coordinate permutations, and all 144 ordered pairs of labeled
simple graphs of orders 0,...,3 are separate exact finite checks. They
support the implementation and expose convention errors; they are not a
substitute for the general bijection or external mathematical acceptance.
