# Matching-count transport: proof components and remaining assembly

Internal research note, 2026-10-30. Continuation of merged PR #9 at
`7012409a5e422dbab5a4da00b86e81014b4cbee8`; original PR head
`940404eab39faeb57d01d3a862f3e3a541251d70`. The six previous receipts and
source pin are preserved. This increment proves general finite components
independently of the numerical matching counter. **It does not claim a complete
Lean proof of the all-factor coefficient formula.**

## Exact formal boundary

| Component | General Lean result | Remaining connection |
|---|---|---|
| Double-occurrence words | `ChordConnectivity.collision_free_iff_connected` | Words use their ordered occurrence-position representation. Extraction from the literal Python/list word inventory is separate. |
| Two resolutions | `ResolutionMatching.simultaneous_resolutions` | Both diagrams and their parity states are constructed from an endpoint bijection; no connectivity hypothesis is supplied. |
| Labeled multiplicity | `MatchingWord.words_length`, `words_nodup`, `words_membership` | Each fixed matching has exactly r! distinct labelings. The complete canonical matching inventory and its disjoint union over matchings are not yet instantiated. |
| Root/direction quotient | `GlobalCycleCount.graph_ordinary_count` | Complete finite graph trace enumeration and deterministic orbit transversal are provided. Specializing the inventory to the product coordinate-step sector still requires transport. |
| Selected motif assignments | `MotifTransport.selected_copy_factorization`, `motif_automorphisms` | Given a selected copy and an inverse of its vertex labeling, assignments factor uniquely through its automorphisms. The complete projection-to-selected-copy inventory is not constructed. |
| Coordinate and inactive fibers | `FiberCardinality.choices_length`, `choices_membership`, `choices_nodup` | Independent coordinate inventories have an exact product cardinality; one-label inactive coordinates have N assignments. Their full product-cycle extraction is separate. |
| Final arithmetic | `FiberCardinality.repeated_edge_formula` | **Conditional** on `hcount : (2L)C = 2^(r+1) r! J`. This hypothesis is the outstanding assembled bijection, not a proved consequence of the component audits. |

The full formula remains a working general finite derivation. Computational
agreement, a checked conditional theorem, and a complete general machine proof
are recorded separately. All new audited declarations use only subsets of
`{propext, Quot.sound}`; no choice, placeholders, native evaluation, new axioms
or external combinatorial oracle are permitted.

## 1. Double occurrences and connected chord intersections

An occurrence-position word is a diagram with endpoints `lo(a)<hi(a)<L` for
each label a. Every position is covered and endpoints of different labels are
disjoint. This is a finite double-occurrence word: label a occurs at precisely
those two positions. These guards are part of the theorem, not experimental
assumptions.

The departure parity of a at t is

    state(t,a) = [lo(a)<t and t<=hi(a)].

For s<=t, equality of all departure coordinates is equivalent to

    s<=lo(a)<t iff s<=hi(a)<t, for every a.

Thus collisions are exactly nonempty proper intervals consisting of whole
chords. Intervals ending at L are represented by their complementary prefix;
L itself is the returned root, not a departure vertex.

Connectivity is defined by finite graph cuts: every Boolean coloring constant
along crossing edges is constant on all chords. `colors n` explicitly lists
all Boolean colorings. A root component is the intersection of all invariant
cuts that contain that root. Its closure along crossing edges is proved from
this definition.

Here is the constructive converse that was previously only prose. Choose the
component containing the chord incident with position zero. A chord outside
that component cannot enclose a component endpoint. To prove this, color a
component chord by whether it lies inside the outside chord, and all other
chords false. Noncrossing and component closure make this a graph-invariant
coloring. The root chord has color false because its least endpoint is zero;
therefore every component chord has color false. The elementary inequalities
for crossing chords prove both endpoint assertions.

Take the first endpoint s outside the root component, then the first component
endpoint t after s, using L if none exists. Every chord with an endpoint in
[s,t) is outside the component. Its other endpoint cannot precede s by
minimality, or reach past t because it would enclose a component endpoint.
Hence [s,t) consists of whole chords. If t=L, its complementary prefix is a
nonempty proper whole-chord interval. Conversely, any such interval gives a
nonconstant invariant coloring. Bounded minimization is proved without choice.
This establishes the full equivalence for arbitrary finite sizes.

This is an independently formalized instance of **established connected-pairing
combinatorics**, not a novelty claim. The Lehner and Courtiel–Yeats–Zeilberger
references and attribution in `repeated-edge-resolutions.md` remain in force.
No theorem from those papers is imported as an axiom.

## 2. The simultaneous resolution condition

`ResolutionMatching.Matching` supplies a bijection from four distinguished
endpoints plus r pairs to the L positions. The four distinguished endpoints
are ordered, and each remaining pair is ordered. The front and outer diagrams
are constructed by explicit invertible endpoint maps:

    front: (a,b),(c,d);     outer: (a,d),(b,c).

Their cover, endpoint disjointness and order properties are proved. At a
departure t, `phase` counts exactly which distinguished endpoints precede t;
`restState` records the remaining parity coordinates. `resolved_state` proves
the actual diagram states agree with the two rows of the five-phase table.
`resolved_equal` proves equality of diagram vertices agrees with equality of
the resolved pair together with the remaining coordinates.

Combining this construction, the general chord theorem, and the original
five-phase collision identity proves

    folded departures injective
      iff front intersection graph connected
          and outer intersection graph connected.

Neither single condition is sufficient. The independent checker records an
explicit failed folded word for each shortcut.

## 3. Labeled matching multiplicity

For a fixed matching M, assign its r complementary pairs the r distinct
nonzero coordinate labels. `MatchingLabels.labels` chooses a head label and
recurses after removing that label. Its soundness and completeness are proved
against list permutation, its output is duplicate-free, and its cardinality
is the inductive factorial r!. Constructive removal/permutation lemmas are
proved locally because some equivalent standard-library lemmas have a
transitive classical-choice dependency.

`MatchingWord` searches the complete finite endpoint inventory to invert the
position bijection. It proves both inverse identities and reconstructs the
actual position-indexed word. A labeling is recovered by reading each pair's
least endpoint. Consequently the list of words for one matching is complete,
duplicate-free and has cardinality r!, including r=0.

For the global disjoint-union step, use canonical unlabeled data: the ordered
four-set and the set of complementary endpoint pairs, listed in increasing
order of least endpoint. From any word of profile (4,2^r), recover the four
positions bearing the distinguished label and the two positions bearing each
other label. Forget the names and sort the pairs. Conversely, labeling that
canonical matching recovers the word. Equality of words forces equality of
the canonical matching data and of its labeling. This proves, as a finite
bijection argument, the labeled valid-word count r! J_r. **The global canonical
matching extraction and list partition in this paragraph remain a machine
formalization obligation.** The per-matching r! theorem does not silently
assume that partition.

## 4. The global ordinary-cycle quotient

The existing `RootedCycle` theorem counted 2L representations of one trace.
The extension proves composition and inverses of the root/direction action,
and reflexivity, symmetry and transitivity of its orbit relation.
`FiniteQuotient.select` constructs a transversal by selecting the first trace
and removing its orbit. Subset, coverage, separation and uniqueness are proved
for finite inventories. A local constructive membership/cardinality lemma
avoids choice-dependent permutation lemmas.

`graphRooted` enumerates **every** function Fin L -> Fin N and filters by
injectivity and symmetric cyclic adjacency. `graphInventory` constructs its
transversal and proves all inventory hypotheses, using the existing edge and
injectivity transport theorems. Thus, for every finite symmetric graph and
L>=3,

    number of rooted directed simple traces
       = 2L * number of ordinary-cycle orbits.

The empty inventory is included. No vertex-set quotient is used: distinct
cycles on the same vertex set remain distinct when the host has chords.
Length two and noninjective traces are outside the theorem's hypotheses.
The coordinate-profile sector is root invariant, but its full specialization
and identification with the matching/motif inventory remain separate.

## 5. Motifs, selected copies and vertex fibers

Write a closed four-step projection as a,b,c,d,a. Adjacent vertices differ.
The two opposite equalities partition it into exactly four equality patterns:

| Opposite equalities | Pattern | Selected projected motif | Labelings of a selected copy |
|---|---|---|---:|
| a=c, b=d | 0101 | edge | 2 |
| a=c, b!=d | 0102 | wedge, root at middle | 2 |
| a!=c, b=d | 0121 | wedge, root at end | 2 |
| a!=c, b!=d | 0123 | square | 8 |

The square case has four distinct vertices, proved from these inequalities
and the adjacent inequalities. Three closed steps similarly have three
distinct vertices and a selected triangle, with six labelings. The exact
2,2,8,6 automorphism inventory is kernel checked. The inventory of all finite
maps used for these certificates has independent completeness, cardinality
and no-duplicate proofs.

A selected copy has a fixed injective labeling into its host. Given an inverse
of that labeling and any second labeling using exactly that selected copy,
`selected_copy_factorization` recovers its unique abstract automorphism.
This uses the **selected** edge relation; additional host edges are allowed.
The resulting assignment lists have the automorphism cardinalities and no
duplicates. Product decoding preserves and reflects all vertex equalities,
so collision-freeness transports between an abstract product and its selected
host copies.

For q coordinates, `FiberCardinality.choices` enumerates dependent coordinate
assignment inventories. Completeness, no duplicates, and the product of their
cardinalities are proved. An inactive coordinate has one abstract label; its
assignment inventory has exactly the host's vertex count. An edge choice has
two initial endpoints, so r+1 selected edges have 2^(r+1) initial assignments.
The full selected-motif recovery from arbitrary product cycles is still a
separate machine obligation; the generic transport theorem does not establish
that every cycle has been inventoried.

Let K_A,K_B,K_C,K_D be the accepted rooted word counts for the four patterns
with r edge axes, with the abstract initial vertex fixed. Before quotienting,
the exact selected-motif multiplicities are

    edge:   2^(r+1) K_A,
    wedge:  2^(r+1) (K_B+K_C),
    square: 8 * 2^r K_D.

For two triangles and s edges the multiplier is 6*6*2^s. Divide each complete
root-invariant sector by 2L. In particular, K_A=r!J_r gives

    (2L) A_r = 2^(r+1) r! J_r,
    L A_r = 2^r r! J_r,
    A_r = (2^r r! J_r)/L,       L=2r+4.

The cancellation and exact natural-number quotient are checked generally in
Lean **with the first identity as the explicit `hcount` hypothesis**. Wedge
root categories must be combined before division; individual categories need
not be divisible by 2L.

For arbitrary factors, choose each active coordinate subset once; for the
four-step sector choose its distinguished coordinate once; for the odd sector
choose its unordered pair of triangle coordinates once. The other active
coordinates are already labeled by their coordinate identities, so no extra
coordinate permutation factorial is inserted. Multiply by the number of
selected motifs in each active factor and by every inactive vertex count.
Disjoint coordinate profiles and uniquely recovered selected projected edge
sets justify the sum. This is the complete working mathematical assembly;
its global extraction bijection remains the named machine-proof obligation.

## 6. Independent exact checks and negative controls

`experiments/matching_transport.py` imports none of the production matching
counter, axis-word generator, coefficient recurrence or product DFS.

- Restricted-growth double words exhaust 1,3,15,105,945,10395 matching diagrams
  through six chords. Explicit Boolean cuts, literal parity departures and
  proper whole-chord intervals agree on every diagram, including rejections.
- Independent multiset permutations exhaust 1,15,420,18900 labeled folded
  words through r=3. Every matching fiber, accepted or rejected, has size r!;
  J_r=0,0,2,110 and accepted word counts 0,0,4,660 follow independently.
- Direct permutation checks corroborate the four motif automorphism counts.
- Literal word sums recover (A,W,S)=(0,0,1),(0,1,12),(2,60,408) for r=0,1,2.
  They agree with the complementary wedge identity T=4W+S.
- Product adjacency paths enumerate every rooted traversal, then partition
  by rotation/reversal and verify that each orbit has size 2L. Edge, wedge,
  square, chorded K4 and an inactive three-vertex factor check all allocations
  in their length-eight next-to-top sectors. Paired-triangle coefficients
  42 and 1404 are isolated independently at lengths six and eight.
- Controls reject either single-resolution shortcut, counting the final return
  as a new vertex, using L instead of 2L, forgetting inactive fibers, dropping
  endpoint cover/disjointness, or applying simple-trace orbit cardinalities
  to a repeated trace. Eight focused regression tests retain these boundaries.

The seven receipts are byte-replayed by `tools/validate.py`; the six previous
receipt files are unchanged. These bounded observations do not prove the new
general statements. Lean proofs and their exact axiom audits are separate.

## Next reproducible proof obligation

Construct and verify the canonical inventory of ordered four-sets plus
unlabeled complementary matchings, with inverse extraction from every labeled
word of the profile. Prove that its distinct per-matching word fibers partition
the entire accepted word inventory. Then specialize the finite graph orbit
inventory to the selected-product motifs and prove both extraction inverses,
including every inactive coordinate. This supplies `hcount` rather than
assuming it and closes the assembled machine theorem. Preserve the source
ownership and prior-work attributions when doing so.
