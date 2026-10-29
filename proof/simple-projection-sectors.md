# Simple-projection sectors and complete c10 support four

Internal research note, 2026-10-29. General identities below are **working**
mathematical results with proofs; finite evaluations are **computed**. The
interval-collision component is kernel-checked. Neither full formal counting
acceptance nor external novelty/priority is claimed.

## Contribution and prior-work boundary

The candidate contributions are (i) a factor-motif translation of connected
partitions giving all-length simple-coordinate-projection sectors, including
an explicit paired-triangle family, and (ii) the complete ten-cycle sector
using exactly four coordinates, including nonsimple four-step projections.
These extend the local eight-cycle lower-support calculation. They do not
replace the source-owned support bound or top-symbol theorem.

The following ingredients are prior work, not new results:

* Füredi and Özkahya, *On 14-Cycle-Free Subgraphs of the Hypercube* (2009),
  section 2.3, explicitly give the coefficients 648 and 6 and hence
  c8(Q4)=648+48=696. [Author PDF](https://web.cs.hacettepe.edu.tr/~ozkahya/pub/C14_2009.pdf),
  [DOI](https://doi.org/10.1017/S0963548309009985).
* Lehner, *Free Cumulants and Enumeration of Connected Partitions* (2002),
  introduction and Theorem 4.1, defines connected partitions by absence of a
  proper interval made of whole blocks, and counts them through the
  noncrossing-component transformation. [Author preprint](https://arxiv.org/abs/math/0110030),
  [DOI](https://doi.org/10.1006/eujc.2002.0619). We use only finite partitions
  and integer recurrences. No probability, infinite series or analytic tools
  are used here.
* Lovasz, *Large Networks and Graph Limits*, equation 5.18, and Curticapean,
  Dell and Marx (2017), equation 2, give injectivity correction by partition
  inversion. [Book](https://lovasz.web.elte.hu/bookxx/hombook-almost.final.pdf),
  [paper](https://arxiv.org/abs/1705.01595).
* Barik and Reddy, *Number of cycles of small length in a graph* (2023),
  provides an explicit general adjacency-entry c8 formula.
  [DOI](https://doi.org/10.1080/09728600.2023.2234421). Publisher-indexed scope
  was checked; the entire formula was not audited in this continuation.
* Asgarli, Krehbiel, Levinson and Russell (2025), *Counting Subgraphs of
  Coloring Graphs*, section 4.3.5, uses coordinate-change partitions for
  **induced** cycles. Those chord-based exclusions do not apply to our ordinary
  cycles. [DOI](https://doi.org/10.1007/s00373-025-02938-1).

Targeted searches for the mixed Cartesian-product coefficients 90288, 5256
and 26592 did not locate a matching formula. This is a research lead, not
proof of novelty. Hypercube numerical specializations and the connected
partition transformation must not be presented as discoveries. A broader
priority search and independent mathematical review remain open.

## 1. Exact interval-collision criterion

Fix labeled active coordinates A, periods d_a >= 2, and L=sum d_a >= 3.
An axis word has exactly d_a occurrences of a. For coordinate a, choose an
injective cyclic template of length d_a. For d_a=2 this is a selected edge
traversed out and back. For d_a>=3 it is a selected ordinary d_a-cycle
traversed once, in either direction. Extra factor edges are permitted.

Let c_t(a) be the number of a's strictly before position t, for 0<=t<=L.
The product vertex at t has coordinate template_a[c_t(a) mod d_a]. For
s<t, injectivity of every template says that the two product vertices agree
iff c_s(a) mod d_a=c_t(a) mod d_a for every a. Since
0<=c_s(a)<=c_t(a)<=d_a, this is equivalent to

    c_t(a)-c_s(a) is either 0 or d_a, for every a.             (1)

Thus a repeated departure vertex exists iff a nonempty proper **linear**
interval of the axis word consists of whole coordinate blocks. Intervals
wrapping past the last position have the same property as their complementary
linear intervals, so no extra cyclic condition is missing. The whole word
is excluded: it is the required final return to the root, not a collision.

Every axis word already supplies factor edges and endpoint closure. Its
departures are distinct exactly when its position partition is connected in
Lehner's sense. Local nonbacktracking is not the criterion. Repeated source
vertices within a nonsimple coordinate projection invalidate the template
injectivity hypothesis; section 4 treats that case separately.

`formal/IntervalCollision.lean` proves the bounded modular equivalence (1),
its vector and injective-assignment versions, and the resulting arbitrary
finite trace injectivity criterion. Prefix monotonicity and bounds are explicit
hypotheses. Actual word prefix-count construction, connected-component
enumeration and ordinary-cycle cardinalities are not formalized in that file.

## 2. A finite labeled-axis recurrence

For a subset S of active coordinates, put

    L(S)=sum_{a in S} d_a,       M(S)=L(S)! / product_{a in S} d_a!,
    M(empty)=1.

M(S) counts all words using the labeled coordinate blocks in S. Let K(S)
count those whose position partition is connected; set K(empty)=0. Define

    P_0(S) = 1 if S is empty, otherwise 0,
    P_k(S) = sum_{T subset S} M(T) P_{k-1}(S minus T).

P_k(S) assigns every whole labeled coordinate to one of k ordered gaps,
then orders each gap's word. In particular empty gaps are permitted.

The recurrence is

    K(S) = M(S) - sum_{empty != T proper subset S}
                          K(T) P_{L(T)}(S minus T).           (2)

Proof. Every position partition has a unique finest noncrossing coarsening:
merge crossing blocks until none remain. Independence from merge order
follows because every noncrossing coarsening must merge any crossing pair;
equivalently take the meet of all noncrossing coarsenings. Its block containing
position zero is a connected component T. Restricted to those positions, the
word is one of K(T). Each remaining coordinate block lies wholly in one of
the L(T) gaps following the component's positions. Otherwise it would cross
that noncrossing component. The word in each gap is unrestricted.

Conversely, a connected T-word with arbitrary words of disjoint labeled
coordinate sets inserted in its gaps has T as its position-zero connected
component. The construction and extraction are inverse. Therefore
M(S)=sum_{empty != T subset S} K(T)P_{L(T)}(S minus T).
The T=S term is K(S), proving (2). This is the labeled-axis form of the
existing connected-partition transformation; it is not a new enumeration
theorem. All subsets, gaps and recurrences are finite.

## 3. Translation to ordinary Cartesian cycles

Write m_2(G)=e(G), and m_d(G)=c_d(G) for d>=3, with ordinary selected-edge
copies, not induced copies. Let rho_2=2 and rho_d=2d for d>=3.
The exact sector with these once-traversed coordinate projections is

    [K(A) product_a rho_{d_a} / (2L)] product_a m_{d_a}(G_a).
                                                               (3)

Multiply by the number of vertices in each inactive coordinate. The sector
condition matters: (3) is not the total profile count when a coordinate of
length >=4 can project to a nonsimple closed walk.

Proof. For each selected motif, rho_d choices give a starting vertex and
direction of traversal (two endpoint choices for an edge). Section 1 leaves
exactly K(A) allowed axis words. Conversely a rooted oriented product cycle
in this sector recovers its axis word and all selected traversals uniquely,
by the existing coordinate extraction/shuffle construction. Removing the root
and orientation divides by exactly 2L: a simple length-L cycle has L distinct
root choices and two distinct directions, with no stabilizer when L>=3.
The chosen coordinate-copy tuple is invariant under this action. This proves
(3) and its integrality. No inducedness assumption enters.

In particular, r selected edge coordinates and two selected triangles give
an exact profile (2 repeated r times,3,3), with universal coefficient B_r:

| r | length | K | B_r=K*2^r*36/(2L) |
|---|---|---|---|
| 0 | 6 | 14 | 42 |
| 1 | 8 | 312 | 1404 |
| 2 | 10 | 12540 | 90288 |
| 3 | 12 | 778128 | 9337536 |
| 4 | 14 | 68251680 | 1404034560 |
| 5 | 16 | 7995853440 | 287850723840 |
| 6 | 18 | 1202585516640 | 76965473064960 |

For this profile every factor projection necessarily is an edge backtrack
or triangle, so (3) is the **entire profile**, not just a simple-projection
subsector. These are evaluations of the proved recurrence; only r=0,1,2
are independently checked here by product adjacency DFS. Higher rows are
not independently enumerated graph observations. The r=1 value matches the
unchanged c8 corpus, including K2 square K3 square K3's 1404 stratum.

## 4. Complete ten-cycle support on four coordinates

Four active coordinates each require at least two steps. At length ten the
only possibilities, up to coordinate permutation, are (4,2,2,2) and
(3,3,2,2). The latter is section 3's r=2 formula.

For the former, the complete canonical four-step coordinate inventory is
A=0101 (edge), B=0102 and C=0121 (wedge), D=0123 (square). The existing
`PatternGenerator.four_patterns_exact` / `NormalizedPattern` interfaces and
the finite restricted-growth derivation supply completeness. All other
coordinates have the unique edge pattern 01.

The exact collision-filtered axis-word sums over the 18900 words of profile
(4,2,2,2) are:

| pattern | valid words | factor-assignment multiplicity |
|---|---|---|
| A | 660 | 2*2^3 |
| B | 2562 | 2*2^3 |
| C | 4008 | 2*2^3 |
| D | 8310 | 8*2^3 |

B and C must both be retained: their rooted phase counts differ. Their
underlying ordinary wedge motif is the same. Applying the rooted oriented
cycle bijection and dividing by 20 gives the working general identities

    F_(4,2,2,2)(G,H,J,K)
      = [528 e(G) + 5256 w(G) + 26592 s(G)] e(H)e(J)e(K),

    F_(3,3,2,2)(G,H,J,K)
      = 90288 t(G)t(H)e(J)e(K).                              (4)

Here w counts ordinary selected P3 copies and s ordinary selected squares.
The square term independently matches (2): K(4,2,2,2)=8310.
The paired-triangle raw sum is 12540 out of 25200 axis words.
Finite complete word sums are computed and regression checked in Python;
their numerical values have not been independently certified in Lean.

For an arbitrary finite factor family, sum the first identity over the
choice of four axes and its distinguished four-step axis, and the second
over the unordered choice of two triangle axes among those four. Multiply
each term by unused-coordinate vertex multiplicities. This exhausts exactly
support four and nothing else. `c10_support_four` implements precisely this
sum. It is not a general total c10 formula: supports one, two, three and five
are outside this increment, and their theorem ownership/status is unchanged.

## 5. Independent checks and negative controls

`experiments/near_top.py` constructs ordinary product adjacency directly and
does DFS with an exact step budget. It uses no equality-pattern generator,
motif counts, connected recurrence or axis-word generator. A cycle is counted
once by its least product vertex and increasing orientation; there is no
post hoc division. Complete K4 is included to detect accidental inducedness.

| product | profile | independent ordinary cycles |
|---|---|---|
| Q4, distinguished axis | (4,2,2,2) | 528 |
| P3 square Q3 | (4,2,2,2) | 6312 |
| C4 square Q3 | (4,2,2,2) | 49728 |
| K3 square Q3 | (4,2,2,2) | 17352 |
| K4 square Q3 | (4,2,2,2) | 146016 |
| Q2 square K3 square K3 | (2,2,3,3) | 90288 |
| K2 square K3 square K3 | (2,3,3) | 1404 |
| K3 square K3 | (3,3) | 42 |

* Counting all paired-triangle closed walks and dividing by 20 gives 181440,
  rather than 90288: collisions remain before the quotient.
* Keeping only square four-step projections in C4 square Q3 gives 26592,
  missing 23136 cycles with edge/wedge projections.
* Keeping only maximal five-coordinate support gives zero for c10(Q4);
  its four possible repeated axes contribute 4*528=2112.
* Word 001010 with profile (4,2) has no proper whole-block interval, but
  the noninjective edge template 0101 creates a repeated product vertex.
  Thus the simple-projection hypothesis cannot be discarded.

Regression also checks exact wordwise equivalence of the modular collision
test and the interval test for nine profiles, coordinate permutations, empty
factors and inactive-coordinate multiplicities. The original c8 receipts
remain byte-identical. General formal graph counting and priority remain open.
