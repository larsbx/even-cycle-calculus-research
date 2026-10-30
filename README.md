# even-cycle-calculus-research

Ordinary even-cycle product formulas, beginning with lower-support c8 corrections.

## First milestone

Derive all lower-support c8 terms. Classify four-step projections (including backtracking/collision patterns) and paired triangle projections; compare a proposed formula with the independent vertex-cycle inventory. The bootstrap inventory is diagnostic data, not the completed formula.

The [complete lower-support derivation](proof/c8-lower-support.md) now supplies
explicit motif formulas for every two- and three-coordinate c8 profile,
including odd projections and collision corrections. It is a **working** proof;
external mathematical acceptance and full formalization remain open.
The source-owned four-coordinate coefficient stays pinned and unchanged.

The [simultaneous pairing continuation](proof/even-edge-resolutions.md) extends
the resolution criterion to every positive even coordinate multiplicity when
each coordinate projects to a single selected edge. All independent pairing
choices must yield connected diagrams. Its exact finite coefficient formula
recovers new-to-this-corpus twelve-cycle strata 32 and 816, independently
checked on Q4. It supplies the complete selected-edge sector, with other
factor motifs explicitly excluded. General phase/choice lemmas and the
literal four-event word bridge are now Lean-certified; general enumeration,
cardinality transport, priority and external review remain open.

The [two-resolution formula](proof/repeated-edge-resolutions.md) supplies the
remaining repeated-edge coefficient as an exact finite matching sum. Together
with the wedge, square and paired-triangle identities, it completes a
**working all-length formula for support exactly k-1 at length 2k**.
The new collision equivalence is Lean-certified for arbitrary finite traces;
the matching-count translation and graph-count assembly remain prose.
Independent adjacency DFS checks the repeated-edge family through length
twelve and all four mixed-sector coefficients at length twelve; higher
listed evaluations and novelty review remain separate.

The [all-length wedge correction](proof/wedge-coarsening.md) now gives the
working identity `T_(r+2)=4W_r+S_r`: coarsening two edge coordinates into a
square computes the wedge coefficient from the source-owned top coefficient
and the local simple-square sector. It recovers 60 and 5256 at lengths eight
and ten and gives exact higher-length evaluations. Direct B/C sums and product
DFS check the specified small cases. This candidate contribution has a prose
proof; all-r formalization, independent review and priority remain open.

The [all-length sector continuation](proof/simple-projection-sectors.md) translates
the existing connected-partition transformation into exact simple-coordinate
projection sectors. It yields a paired-triangle family and complete **working**
c10 formulas for support on exactly four coordinates, including nonsimple
four-step projections. New coefficients are 528, 5256, 26592 and 90288;
independent product-adjacency DFS checks eight specified strata. The note
attributes prior work and separates candidate contributions from established
specializations. Priority and external mathematical acceptance remain open.
The [kernel coefficient and root-count continuation](proof/rooted-cycle-counting.md)
certifies all five c10 raw coefficients and their motif-multiplier arithmetic.
For a fixed injective finite trace of length m>=3, its 2m rotation/reversal
representations are now proved distinct, complete and edge-preserving under
symmetric adjacency. The global graph-inventory quotient and full motif-count
assembly remain open. Run `python3 experiments/near_top.py` to replay
[the new receipt](conformance/near-top.json). Five general Lean lemmas and
three finite controls certify the interval-collision component; the connected
recurrence is not yet kernel-certified. The continuation below certifies
the c10 coefficient enumeration separately.

The [formal collision bridge](proof/coordinate-collision-bridge.md) now proves
eight general finite coordinate-decoding lemmas, including collision/support
reflection and recovery of factor assignments for a fully visited fixed shape.
Six formal control declarations certify the required injectivity and label-use
assumptions. The [canonical extraction component](proof/canonical-coordinate-extraction.md)
adds 15 general first-occurrence lemmas and three finite controls. It recovers
coordinate equality classes by a bounded scan; compressed shuffle encoding
and the full counting bijection remain open. Run `python3 formal/check.py`
for all 429 declaration audits. The [ordinal compression component](proof/ordinal-rank-compression.md)
adds 20 general lemmas and three controls: representative labels are now
bijective with `Fin r`, reconstruction is exact, and zero-first/append bounds
match the enumerator. The [coordinate-event component](proof/coordinate-event-shuffle.md)
adds 17 general lemmas and five controls: compatible words and destination
queues have a unique interleaving, and replay reconstructs a coherent vertex
path after stationary-step deletion. The [closed-walk component](proof/closed-coordinate-walks.md)
adds 19 general lemmas and nine controls: compatible closed factor walks
realize a unique closed product walk; endpoint normalization identifies exactly
the departure vertices for collision testing. The [modular cycle criterion](proof/modular-cycle-trace.md)
adds ten general lemmas and seven controls: closed event replays yield exactly
the existing simple-cycle predicate when their departures are distinct and
they follow valid factor steps. The [executable trace bridge](proof/executable-coordinate-trace.md)
adds 16 general lemmas and eight controls: for bounded positive-period templates,
the literal prefix-index vertex list equals encoded departures, and its
Boolean collision test is exactly trace injectivity. The [axis-word generator proof](proof/axis-word-generator.md)
adds 17 general lemmas and seven controls: exact multiplicity completeness,
unique emitted words, collision-filter uniqueness and constructive typed axes.
The [cyclic-pattern generator proof](proof/cyclic-pattern-generator.md) adds
16 general lemmas and seven controls: exact zero-first restricted-growth
conditions, proper closing and unique enumeration. The [canonical membership bridge](proof/canonical-pattern-membership.md)
adds 22 general lemmas and ten controls: proper finite coordinate traces
normalize to generated words exactly once, with injective reconstruction and
fixed-template assignment uniqueness. Arbitrary-template normalization inverses
and the full product-cycle counting composition remain open.

Run `python3 experiments/lower_support.py` for exact symbolic coefficients,
reproduction of all five original cases, 19 additional products, and 144 small
labeled factor pairs. Its deterministic receipt is
[conformance/lower-support.json](conformance/lower-support.json).

The [independent partition-lattice comparison](proof/partition-inversion.md)
checks every existing corpus profile through direct quotient-graph
homomorphisms, retaining parallel-edge multiplicities. It agrees on all five
original cases, 19 additional products and 144 small factor pairs, plus five
boundary cases. Run `python3 experiments/partition_inversion.py`; its receipt is
[conformance/partition-inversion.json](conformance/partition-inversion.json).
The inversion identity is established literature; this is an independent
finite comparison, not a novelty claim or completion of the counting proof.

The reproducible first experiment is `python3 experiments/first.py`; its exact
bounded output is recorded in [conformance/first.json](conformance/first.json).
See [REPRODUCING.md](REPRODUCING.md) for setup and comparison commands, and
[the roadmap](docs/roadmap.md) for remaining proof obligations.

## Initial result

See [the bootstrap results](docs/first-results.md) for exact scope and next gates.

## Mathematical conventions and authority

Finite simple undirected graphs; embeddings are injective edge-preserving maps,
not necessarily induced. An ordinary cycle is unoriented and unrooted, with its
selected edges: divide labeled traversals by 2m for a length-m cycle. Coordinate
support means nonconstant vertex projection. Centered defects use
u_G=G-|V(G)|K1, with no factorial division in the symbol.

[The claim registry](proof/claims.toml) separates source references, local finite
computations, proof obligations, conjectures, and falsified candidates.
The shared graph-ring foundations retain a single authority in
[28d0224](https://github.com/larsbx/graph-product-ring-research/tree/28d022402037274a9fe85c1fd64ecda2532dceb9); source claims labeled **working** remain working.
Lean kernel verification of a specified component, bounded computational evidence,
and independent mathematical acceptance are distinct fields. The bootstrap added
no Lean proof. The subsequent [Lean components](formal/README.md)
cover all five raw coefficient tables and the specified graph-level decoding
lemmas, not the full extraction/counting theorem. No
independent-acceptance or novelty claim is made.

Non-goals: changing publication/manuscript bytes; silently upgrading inherited
claims; treating finite search or a language port as a theorem.

## Source and related programs

- [Pinned ordinary-cycle support/order proof](https://github.com/larsbx/graph-product-ring-research/blob/28d022402037274a9fe85c1fd64ecda2532dceb9/proof/even-cycle-order-symbol.md).
- [Pinned component-and-gap proof candidate](https://github.com/larsbx/graph-product-ring-research/blob/28d022402037274a9fe85c1fd64ecda2532dceb9/docs/research/c2k-chord-symbol-all-k-proof-2026-10-22.md).
- [Pinned source claim registry](https://github.com/larsbx/graph-product-ring-research/blob/28d022402037274a9fe85c1fd64ecda2532dceb9/proof/claims.toml).
- [Central bridge map](https://github.com/larsbx/graph-product-ring-research/blob/main/docs/research/bridge-repositories.md).
- [Provenance and acceptance boundaries](docs/provenance.md).
- [Sibling repositories](docs/bridges.md).

The [existing Vizing program](https://github.com/larsbx/vizing-domination-conjecture-research)
remains independent. Literature and novelty review remain coordinated with
[novelty-lab](https://github.com/larsbx/novelty-lab).

Independent finite verification now also uses explicit vertex-partition Mobius
inversion, separately from the shuffle and connected-axis kernels. It recovers
the full finite c8 corpus and the new c10 coefficients without discrepancies.
See [the inversion note](proof/partition-lattice-check.md) for exact algorithm,
cancellation ledgers, negative controls and formal scope.
