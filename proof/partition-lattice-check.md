# Finite vertex-partition inversion check

Internal research note, 2026-10-29. This is independent finite corroboration
of the existing working factor-motif expansions. General homomorphism /
injectivity inversion is established prior work, explicitly attributed to
Lovasz and Curticapean--Dell--Marx in
[simple-projection-sectors.md](simple-projection-sectors.md). In particular,
see Curticapean, Dell and Marx (2017),
[Homomorphisms Are a Good Basis for Counting Small Subgraphs](https://arxiv.org/abs/1705.01595).
Equation (2), page 6, gives the partition-weighted homomorphism formula;
Definition 3.2 and the subsequent discussion give the quotient/zeta convention.
The primary preprint was checked on 2026-10-29. No novelty or external
mathematical acceptance follows from this check.

## Exact finite identity

Let X be a finite simple undirected Cartesian product, with each product edge
marked by its unique changing coordinate. Label the departure positions of
C_m by 0,...,m-1; the closing endpoint is position 0 again and is **not** an
extra partition element. All arithmetic below is in finite integer sums.

Order the vertex partitions by refinement. Write 0 for the discrete partition.
For a partition rho let H_p(rho) be the number of homomorphisms C_m/rho -> X
with coordinate-step profile p, retaining **every original edge occurrence**.
A loop in the quotient gives zero. Parallel occurrences impose the same
adjacency constraint but each contributes its axis mark; simplifying away
multiplicity would lose the requested profile.

For an unrestricted closed walk t, its kernel kappa identifies precisely the
positions with equal product vertices. The walk factors uniquely through rho
iff rho <= kappa. Therefore, if E_p(kappa) is the unrestricted equality-kernel
histogram,

    H_p(rho) = sum_{kappa >= rho} E_p(kappa),
    mu(0,rho) = product_{B in rho} (-1)^(|B|-1)(|B|-1)!,
    I_p = sum_{rho in Pi_m} mu(0,rho) H_p(rho).                 (1)

Here I_p counts injective rooted directed closed walks. To see cancellation,
expand the last finite sum by individual unrestricted walks. A walk of kernel
kappa has total weight sum_{rho <= kappa} mu(0,rho), equal to 1 exactly for the
discrete kernel and to 0 otherwise. The lower interval factors over kappa's
blocks. On a block of size r, partitions with the factorial weight enumerate
permutations by their cycle partitions, with the permutation sign. The signed
sum is 1 for r=1, and 0 for r>=2: composing with a fixed transposition pairs
opposite signs. This proves the finite cancellation identity without a shuffle
criterion, connected-axis recurrence, analytic tools or an infinite limit.

For m>=3, each ordinary cycle has exactly 2m injective rooted directed
representations. There are m choices of starting vertex and two directions;
injectivity makes these distinct. Conversely the selected consecutive edges
of any representation recover that cycle. Extra chords are allowed. Thus
F_p=I_p/(2m); all profiles p are invariant under rotation and reversal.

## Implementation independence and limits

`experiments/partition_walks.cpp` traverses **unrestricted** product adjacency.
It never rejects a vertex because it has been visited; labels only record
its equality kernel. Roots and both directions are all retained. It records
profiles and, when requested, the normalized four-step projection category.
It contains no motif formula, shuffle generator or connected-partition code.

`kernels/partition_lattice.py` generates finite vertex partitions from scratch,
constructs each quotient-hom count by the zeta sum in (1), and takes the
explicit signed Mobius sum. It never reads the discrete-kernel histogram cell
as the answer. Zero quotient-hom terms are omitted from storage only. Each
receipt records the by-block-count signed terms and a SHA-256 digest of the
sorted nonzero H_p ledger; rerunning `invert` exposes the entire ledger.

This is a histogram-assisted homomorphism inversion implementation, not a
claim that every product quotient is solved separately by a tensor algorithm.
To check the zeta route, `quotient_homs` is a second reference algorithm:
it assigns vertices directly to quotient blocks, allows distinct blocks to
coincide, checks adjacency, and counts the original marked edge occurrences.
It does not enumerate closed walks or use their equality histogram. Replay
compares all 115,975 quotients of C10 on K2, all partitions of C3 through C6
on K3, and up to eight deterministic partition fixtures for every near-top product
profile, including four quotients with positive profile-specific hom counts. Tests additionally check all small quotients on P3. Cancellation is
checked on every partition through Pi_10, using the block-product identity;
tests compare generated refinements to brute refinement order through Pi_6.

Only the **comparison layer** imports the candidate eight-cycle formula for
the 144 small graph pairs. The other comparisons read existing exact receipt
values. Neither supplies a hom count or inversion weight. The CPP input graph
constructors and corpus motif fixtures are independent of the old constructors.

## Reproduced corpus

All five original inventories, including every nonzero coordinate profile,
agree: C4 square K2 = 6, K3 square K3 = 81, P3 square K3 = 15,
K2 square K3 square K3 = 2700, Q4 = 696. Q4 has 648 full-support and 48
lower-support cycles. All 19 additional eight-cycle fixtures and all 144
labeled small graph pairs also agree, including odd projections, isolated
fibers, nonsimple projections and disconnected factors.

| Ten-step distinguished profile / product | Closed rooted directed | Injective rooted directed | Ordinary |
| --- | ---: | ---: | ---: |
| (4,2,2,2), Q4 | 302400 | 10560 | 528 |
| (4,2,2,2), P3 square Q3 | 1209600 | 126240 | 6312 |
| (4,2,2,2), C4 square Q3 | 4838400 | 994560 | 49728 |
| (4,2,2,2), K3 square Q3 | 2721600 | 347040 | 17352 |
| (4,2,2,2), K4 square Q3 | 12700800 | 2920320 | 146016 |
| (2,2,3,3), Q2 square K3 square K3 | 3628800 | 1805760 | 90288 |

The prior six- and eight-step paired-triangle checks also reproduce 42 and
1404 ordinary cycles. The receipt includes all profile ledgers, even zero
cycle strata with nonzero unrestricted closed walks.

For example, grouping the (2,2,3,3) inversion terms by number of blocks gives

    -198720 + 1054080 - 2678400 + 3628800 = 1805760,
    1805760 / 20 = 90288.

For (4,2,2,2) in C4 square Q3 the corresponding sum is

    -445440 + 2814720 - 7265280 + 10498560 - 9446400
      + 4838400 = 994560,
    994560 / 20 = 49728.

## Independent raw coefficients and motif comparison

For each four-step projection pattern, apply the *same inversion* to its
restricted unrestricted-walk histogram. Divide the resulting rooted injective
count by the number of rooted directed factor projections, and by 2^3 for
the three selected edge coordinates. This gives the raw coefficients:

| Projection | Inverted raw coefficient |
| --- | ---: |
| 0101 | 660 |
| 0102 | 2562 |
| 0121 | 4008 |
| 0123 | 8310 |

For a general factor G, those rooted projection embedding counts are
2e(G), 2w(G), 2w(G), 8s(G), respectively. Edges and cycles are selected
edge subgraphs; wedges need not be induced. Summing the rooted categories
before dividing by 20 yields

    (2^3/20)[660(2e) + (2562+4008)(2w) + 8310(8s)]
      = 528e + 5256w + 26592s.

The paired-triangle rooted count divided by 2^2 * 6^2 gives 12540. Consequently
12540 * 2^2 * 6^2 / 20 = 90288 for each selected pair of triangles and pair
of edges. These independently recovered finite coefficients match PR #6's
working general expansions. Coordinate allocations and unused-coordinate
vertex fibers retain the existing conventions. They are not new general
inversion theory, and numerical agreement does not settle expansion priority.

## Negative controls and discrepancy analysis

* **Repeated product vertices:** C4 -> K2 has two unrestricted rooted directed
  walks. The signed partition terms are 2-4+2=0. Keeping only the discrete
  quotient or taking absolute Mobius weights incorrectly returns 2 or 8.
* **Nonsimple projections:** in C4 square Q3, the simple-square category alone
  contributes 26592 ordinary cycles, whereas the actual profile count is
  49728. In P3 square Q3 the 6312 cycles all use nonsimple four-step projections.
* **Ordinary versus induced:** K4 has three ordinary four-cycles and zero
  induced four-cycles. The K4 square Q3 check also exercises noninduced
  four-step selected squares.
* **Rooted quotient:** the paired c10 sector has 1805760 injective rooted
  directed representations. Division by 10 gives the wrong 180576; division
  by 20 gives 90288. Dividing already ordinary copies by 20 fails integrality.
  Dividing unrestricted closed walks by 20 gives the wrong 181440.
* **Root-dependent projection categories:** 0102 and 0121 are not individually
  preserved by changing the starting position. In P3 square Q3 their rooted
  counts are 40992 and 64128, neither divisible by 20. They must be summed
  with all categories before the ordinary-cycle quotient. This is a counting
  convention issue discovered during implementation, not a formula discrepancy.

There are no discrepancies in the final comparisons. No candidate formula
was changed to fit a computation.

## Formal scope and replay

`formal/PartitionInversion.lean` adds twelve audited declarations: quotient
factorization with explicit block representatives, uniqueness, discrete-kernel
injectivity, quotient-loop obstruction, finite signed-sum algebra, conditional
inversion transport, and two finite controls. The cancellation identity is the
**explicit hypothesis** of `finite_inversion`; that theorem does not silently
assert a Lean proof of the factorial partition weights or their completeness.
Actual partition enumeration, the C10 coefficients and the graph-level 2m
cardinality quotient are mathematical/computational components here. Six new
regression tests check the named controls, including relabeling and fibers.
The complete audit has 250 declarations across 23 rebuilt Lean sources, with
exact permitted standard axiom sets and no placeholders or choice axioms.

Run `python3 experiments/partition_histogram.py` and compare its output
byte-for-byte with `conformance/partition-histogram.json`. Python 3.11+ and
g++ C++17 are sufficient; the temporary executable is removed automatically.
The receipt is also mandatory in `tools/validate.py`. The full finite Lean
check uses the same pinned toolchain and official archive digest as before.
Local replay used the documented executable-path environment shim; hosted
acceptance must succeed on the exact final PR head before merge.

## Integration with PR #7

Main independently gained a direct quotient frontier-DP oracle while this
continuation was open. That kernel, experiment, receipt and six tests are
preserved under their original `partition_inversion` names. This continuation's
histogram experiment, receipt and six tests use `partition_histogram` names,
with the separate partition-lattice kernel unchanged. Both inversion routes
remain mandatory alongside the original three receipts: five deterministic
receipts and 25 regressions in the integrated tree. The direct route covers
the full c8 corpus and the histogram route also covers the c10 formulas.
