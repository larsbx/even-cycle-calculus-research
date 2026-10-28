# even-cycle-calculus-research

Ordinary even-cycle product formulas, beginning with lower-support c8 corrections.

## First milestone

Derive all lower-support c8 terms. Classify four-step projections (including backtracking/collision patterns) and paired triangle projections; compare a proposed formula with the independent vertex-cycle inventory. The bootstrap inventory is diagnostic data, not the completed formula.

The [complete lower-support derivation](proof/c8-lower-support.md) now supplies
explicit motif formulas for every two- and three-coordinate c8 profile,
including odd projections and collision corrections. It is a **working** proof;
external mathematical acceptance and full formalization remain open.
The source-owned four-coordinate coefficient stays pinned and unchanged.

The [formal collision bridge](proof/coordinate-collision-bridge.md) now proves
eight general finite coordinate-decoding lemmas, including collision/support
reflection and recovery of factor assignments for a fully visited fixed shape.
Six formal control declarations certify the required injectivity and label-use
assumptions. The [canonical extraction component](proof/canonical-coordinate-extraction.md)
adds 15 general first-occurrence lemmas and three finite controls. It recovers
coordinate equality classes by a bounded scan; compressed shuffle encoding
and the full counting bijection remain open. Run `python3 formal/check.py`
for all 82 declaration audits. The [ordinal compression component](proof/ordinal-rank-compression.md)
adds 20 general lemmas and three controls: representative labels are now
bijective with `Fin r`, reconstruction is exact, and zero-first/append bounds
match the enumerator. The [coordinate-event component](proof/coordinate-event-shuffle.md)
adds 17 general lemmas and five controls: compatible words and destination
queues have a unique interleaving, and replay reconstructs a coherent vertex
path after stationary-step deletion. Closed-walk endpoint/edge alignment and
the full counting bijection remain open.

Run `python3 experiments/lower_support.py` for exact symbolic coefficients,
reproduction of all five original cases, 19 additional products, and 144 small
labeled factor pairs. Its deterministic receipt is
[conformance/lower-support.json](conformance/lower-support.json).

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
