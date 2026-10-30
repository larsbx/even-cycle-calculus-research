# All-length wedge coefficient from coordinate coarsening

Internal research note, 2026-10-30. This is a **working general identity** with
a finite combinatorial proof and exact tests. The factor-motif translation is
a candidate contribution; mathematical priority and independent review remain
open. The top-support theorem remains owned by the pinned graph-product-ring
source. Neither a new top-symbol proof nor a claim of novelty for the
connected-partition enumeration is made here.

## Statement

Fix r>=0 and L=2r+4. Let T_(r+2) denote the ordinary L-cycle coefficient with
r+2 labeled edge coordinates, each used exactly twice. Let S_r be the
coefficient for a selected square traversed once and r selected edge
backtracks. The source top-support result supplies T; section 3 of
`simple-projection-sectors.md` supplies S through connected partitions.

Let W_r count the ordinary product cycles whose four-step coordinate
projection uses exactly the two selected edges of a wedge, with r other
selected edge coordinates each used twice. Then

    T_(r+2) = 4 W_r + S_r,
    W_r = (T_(r+2) - S_r) / 4.                              (1)

For any finite simple undirected factors G,H_1,...,H_r, the wedge contribution
to the profile (4,2,...,2) is exactly

    W_r * w(G) * product_i e(H_i),                          (2)

times the vertex counts of inactive factors. Wedges are selected edge copies,
not induced copies. Formula (2) is one term of that profile. Its repeated-edge
and square projection terms are not silently included.

## Proof by grouping coordinates

Consider the same finite product of r+2 selected edges, with every coordinate
used twice. Group the first two edge coordinates as their Cartesian square
C4. This is a vertex and edge bijection of the same product graph; it changes
only the coordinate labels used to describe the cycle. Ordinary cycles and
product-vertex injectivity are unchanged.

After deleting stationary steps, the projection onto the grouped C4 has four
steps and uses each of its two internal directions twice. A closed four-step
walk in a simple graph has one of the canonical equality patterns
0101, 0102, 0121, 0123. The first is impossible here: staying on one selected
edge of C4 would use only one of the two original coordinate directions.

In either middle case the projection uses a selected wedge of C4. Its two
edges have different internal directions, each traversed twice. Conversely
every such wedge projection satisfies precisely the original two-coordinate
step budget. The final case traverses the selected square once; its four
edges again use each direction twice.

C4 has exactly four selected wedges and one selected square. Every product
cycle recovers its selected projected edge set, so those five classes are
disjoint. For each wedge, replacing its three vertices by the vertices of
an abstract P3 gives a bijection with the cycles counted by W_r. The simple
square class is exactly S_r. This proves the first identity in (1), before
any rooted-count division. It also proves nonnegativity and divisibility by
four of T_(r+2)-S_r.

For arbitrary factors, the same projection extraction recovers a unique
selected wedge and selected edges. Injective edge-preserving assignments
preserve and reflect product-vertex equality; extra host edges impose no
restriction. Relabeling a selected wedge therefore gives the same universal
coefficient W_r for every copy. Summing the disjoint selected-copy classes
and inactive vertex fibers proves (2).

Both root-dependent wedge patterns 0102 and 0121 are included in W_r.
Their rooted counts need not agree, and individual categories need not admit
division by 2L. Grouping by the selected wedge edge set avoids that mistake.

Equivalently, let K_pair be the connected labeled-axis word count for r+2
period-two coordinates, K_square the count for (4,2^r), and K_B,K_C the
collision-filtered counts for the two wedge templates. Their rooted traversal
multipliers give the finite-word identity

    K_pair = 2 K_square + 2(K_B + K_C),
    W_r = 2^r (K_pair - 2 K_square) / (2L).                 (3)

In particular K_pair>=2 K_square, and their difference is even. These are
consequences of the same coarsening bijection, not assumptions about numerical
interpolation. The tests compare the direct B/C sum with (1) through r=3.

## Finite evaluations and scope

`wedge_projection_coefficient(r)` evaluates T and S using the existing finite
connected-word routine, then performs the exact division in (1). This is an
evaluator for the source-owned top coefficient, not a replacement ownership
claim. No product adjacency or direct B/C shuffle enumeration enters that
evaluation.

| r | Length | T_(r+2) | S_r | W_r |
|---|---:|---:|---:|---:|
| 0 | 4 | 1 | 1 | 0 |
| 1 | 6 | 16 | 12 | 1 |
| 2 | 8 | 648 | 408 | 60 |
| 3 | 10 | 47616 | 26592 | 5256 |
| 4 | 12 | 5433600 | 2780928 | 663168 |
| 5 | 14 | 880865280 | 422138880 | 114681600 |
| 6 | 16 | 191555159040 | 87258885120 | 26074068480 |

The r=2 and r=3 rows recover the existing c8/c10 wedge coefficients. Direct
B/C collision sums independently check r=0..3. Product-adjacency DFS gives a
second check for r=1..3: subtract twice the distinguished repeated-edge
profile in K2 square Q_r from that profile in P3 square Q_r. P3 has two edge
copies, one wedge and no square, so the subtraction isolates W_r. Higher
rows are exact recurrence evaluations, not independently enumerated graph
observations. The r=0 wedge sector is empty, as the formula requires.

The separate [two-resolution continuation](repeated-edge-resolutions.md) now
determines the all-length repeated-edge coefficient in profile (4,2,...,2).
Complete formulas for still smaller support at longer lengths remain open.
The coarsening bijection and identity (1) remain prose proofs, separate from
the kernel c10 certificates and fixed-cycle representation lemmas.

Targeted searches on 2026-10-30 for Cartesian-cycle wedge counts, projection
formulas and the existing mixed coefficients did not locate this identity.
That limited search is not evidence of priority; related cube cycle counts,
connected partitions and the source top theorem are established baselines.
