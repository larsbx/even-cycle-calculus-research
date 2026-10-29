# Independent profile comparison by partition-lattice inversion

## Status and attribution

The inversion identity is established literature, not a new result of this
repository. Lovász, *Large Networks and Graph Limits*, §5.2.3, equation (5.18),
states the injective-homomorphism expansion through partitions. His §6.1
explicitly retains edge multiplicities under quotienting. Sources:

- [Author-hosted book PDF](https://lovasz.web.elte.hu/bookxx/hombook-almost.final.pdf),
  equation (5.18) and the discussion preceding (6.2).
- Curticapean, Dell and Marx,
  [Homomorphisms Are a Good Basis for Counting Small Subgraphs](https://arxiv.org/abs/1705.01595)
  (2017), for the broader homomorphism/subgraph basis context.

Both sources were retrieved on 2026-10-29. The profile refinement below follows
by assigning one formal variable to each host-edge axis; its elementary
cancellation argument is given explicitly. No novelty is claimed for this
weighted specialization. The new artifact is an independently implemented,
exact corpus comparison, registered as **computed**. It does not promote
`C8-LOWER-SUPPORT` beyond **working**, close the formal counting bijection,
or establish external mathematical acceptance.

## Finite identity and profile refinement

Let X be a finite simple undirected graph with each edge assigned one of q
axis colors. In a Cartesian product, the color is the unique changing
coordinate. Let C_m have indexed departure vertices 0,...,m-1 and its m
selected cyclic edges, with m >= 3.

For each partition P of these indexed vertices, form the quotient multigraph
C_m/P. Preserve every original edge occurrence: if several selected edges
merge to a single pair of blocks, give that quotient edge its multiplicity.
If an original cyclic edge has both ends in one block, the quotient has a
loop and contributes zero into a loopless host.

Define H_P(z) by summing over **all** edge-preserving maps f from the quotient
to X, with no inequality requirement between distinct quotient vertices.
An edge of multiplicity w mapped to host-axis a contributes z_a^w. The
product over quotient edges is the map's weight. Thus every term has total
degree m. Put

\[
\mu(P)=\prod_{B\in P}(-1)^{|B|-1}(|B|-1)!.
\]

For each profile s=(s_1,...,s_q) of total degree m,

\[
2m\,c_{m,s}(X)
=[z_1^{s_1}\cdots z_q^{s_q}]
\sum_{P\in\Pi(\{0,\ldots,m-1\})}\mu(P)H_P(z).
\tag{1}
\]

Here c_{m,s} counts ordinary unoriented, unrooted cycles with their selected
edges, regardless of extra host chords. There is no evenness condition on
an individual s_a, and no inducedness condition.

To verify (1), fix one homomorphism h:C_m -> X and let R be its equality
partition. It factors through C_m/P exactly when P refines R. All such
factorizations have the same edge-weight monomial because quotient edge
multiplicities retain all m selected occurrences. Its signed coefficient is

\[
\sum_{P\le R}\mu(P)
=\prod_{B\in R}\left(\sum_{Q\in\Pi(B)}\mu(Q)\right)
=\begin{cases}1&\text{if every block of R is a singleton},\\
0&\text{otherwise}.\end{cases}
\]

For completeness, the inner sum is 1 for a singleton and 0 when |B|>=2:
partition B into the cycles of a permutation. Each block contributes
(|B'|-1)! cyclic orders and sign (-1)^{|B'|-1}; the sum is therefore the sum
of signs of all permutations of B. Multiplication by a fixed transposition
pairs opposite signs. Only globally injective homomorphisms survive.

Every selected ordinary m-cycle has exactly m starting vertices and two
orientations, all with the same axis multiplicities. With m>=3 and distinct
departure vertices these 2m presentations are distinct. Division gives (1).
This is a finite prose verification of the standard identity and its profile
refinement; it is not an additional Lean cardinality/orbit theorem.

## Independent executable route

`kernels/partition_inversion.py` imports only Python's standard library. It
does not import the existing axis-word or coordinate-pattern generators,
collision filter, motif counts, DFS, or pinned source constructors.

1. Enumerate partitions by inserting each next indexed vertex into every
   existing block or into a new block. This enumeration includes adjacent
   identifications; it does not call the proper-coordinate-pattern generator.
2. Construct the weighted quotient, discard looped quotients, and sum Möbius
   coefficients for isomorphic **weighted** graphs by finite relabeling.
3. Construct the host's axis-colored Cartesian adjacency directly.
4. Count arbitrary quotient homomorphisms by frontier dynamic programming.
   An assignment state retains the images of earlier quotient vertices needed
   by future edges. Choose a new image from the intersection of its assigned
   neighbors' adjacency sets; distinct nonadjacent blocks may have equal
   images. Multiply by the profile monomial of all newly checked edges.
5. Sum with signed integer coefficients, check nonnegativity and divisibility
   by 2m, and divide **only after** the complete signed sum.

The polynomial exponent vector is packed in base m+1. Every exponent is at
most m, so adding the contributions of the m selected edges causes no carry.
Packing is only an integer encoding of monomials.

For m=8, there are 4,140 partitions, 715 loopless partitions and 44 nonzero
isomorphism-grouped weighted-quotient terms. The receipt lists all 44 terms,
their edge multiplicities and their signed coefficients. This finite count
concerns weighted quotients, not 44 factor motifs or a new minimal basis claim.

The comparison driver shares **input motif definitions** with the existing
experiments and loads their recorded results, but the quotient oracle itself
does not use them. The driver compares its answers with both the selected-edge
motif formulas and the existing vertex-simple DFS. A finite input/configuration
mistake shared between the fixtures is therefore still possible; independent
algorithms do not amount to an external proof review.

## Exact observed agreement

Every coordinate-step profile agrees, rather than only the displayed totals.

| Original product | Ordinary eight-cycles |
|---|---:|
| C4 square K2 | 6 |
| K3 square K3 | 81 |
| P3 square K3 | 15 |
| K2 square K3 square K3 | 2,700 |
| Q4 | 696 |

The same agreement holds for all 19 additional products and all 144 ordered
pairs of labeled simple graphs of order at most three in the earlier corpus.
Five further boundary inputs cover no axes, an empty factor, isolated fibers
and disconnected factors. These are 173 checks, not 173 distinct isomorphism
classes. The first two receipts remain byte-for-byte unchanged, with their
SHA-256 digests recorded in the new receipt.

For K2 square K3 square K3, profile (2,3,3) gives:

| Quantity | Count |
|---|---:|
| Rooted oriented closed walks (discrete partition term) | 40,320 |
| Signed contribution from the other partitions | -17,856 |
| Rooted oriented injective traversals | 22,464 |
| Ordinary cycles after division by 16 | 1,404 |
| Incorrect division of unrestricted closed walks by 16 | 2,520 |

The raw walk count allows collisions. Q4 also reconfirms the earlier negative
control: retaining only its 648 full-support cycles omits 48 ordinary cycles.
Neither specialization is claimed as novel.

## Reproduction and controls

Run `python3 experiments/partition_inversion.py` and compare its deterministic
output to `conformance/partition-inversion.json`. `python3 tools/validate.py`
replays all three receipts and all 13 regression tests, including the six new
oracle tests. The new tests check:

- Bell partition inventories through eight vertices, duplicate-free exact
  partitions, and cancellation for every possible eight-vertex equality kernel.
- A quotient consisting of one edge of multiplicity eight: its two-axis
  homomorphism polynomial has degree eight, not degree one. Adjacent-block
  identification must instead produce a loop and be discarded.
- The frontier algorithm against direct enumeration of every map for all
  loopless cyclic quotients of lengths three, four and five into K2 square K3.
- Complete hosts, including K8's 8!/16=2,520 selected eight-cycles despite its
  extra chords, and zero eight-cycles for every simple host of order at most four.
- Empty, edgeless and malformed inputs and the ordinary-cycle length bound.

No Lean source or declaration audit is changed by this comparison. The existing
230 declaration audits remain their specified component proofs. Arbitrary
template normalization inverses, product-wide assembly, motif classification
and the formal counting quotient remain open. The next proof increment can
use this independent oracle while continuing those obligations.
