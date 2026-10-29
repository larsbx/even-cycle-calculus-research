# Lean coefficients and coordinate decoding

`Shuffle.lean` uses only Lean/Std, pinned to `leanprover/lean4:v4.34.0-rc2`.
From the repository root, run `python3 formal/check.py` with that toolchain.
Set `LEAN_BINARY` to an explicit compiler path when needed. This compiles all
23 Lean sources, rebuilding all local imports in a temporary directory,
and verifies 250 exact named axiom sets. It does not rely on a cached olean.
CI downloads the exact official release archive and checks SHA-256
`3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8`.

Declarations in namespace ECC:

- `paired_triangle_coefficient`: K(01,012,012)=312.
- `four_step_coefficients`: K(A,01,01)=(4,44,76,204), A ranging over
  the four patterns 0101,0102,0121,0123.
- `two_four_step_coefficients`: the complete 4 by 4 K-table for (4,4).
- `six_two_coefficients`: K for all 41 length-six patterns with an edge.
- `three_five_coefficients`: K for all 11 length-five patterns with a triangle.

Each theorem uses `by decide`, which creates a kernel-checked finite reduction
proof. There is no native evaluation axiom and no added axiom. The declarations'
transitive axioms are printed and checked in CI: exactly `[propext]` for
each of the five declarations. Coefficients are defined
through multiplicity-constrained word generation and pairwise distinct
reconstructed label tuples, without hardcoding the acceptable words.

`CollisionBridge.lean` now proves eight general lemmas about finite coordinate
decoding: equality and single-coordinate-step reflection, unique changing axis,
edge preservation, injectivity and support reflection, simple-cycle decoding,
and fixed-shape assignment recovery when every label is used. See the exact
assumptions and declaration table in
[proof/coordinate-collision-bridge.md](../proof/coordinate-collision-bridge.md).
Four declarations use only standard `Quot.sound` via function extensionality;
four use no axioms. Edge preservation requires no nonedge preservation.

`CollisionControls.lean` adds six formal control declarations. They show why
edge preservation cannot replace injectivity and why unseen labels defeat
assignment recovery. Five use standard `propext` and `Quot.sound`; one uses no
axioms. The audit permits no choice, placeholders, added axioms or native
evaluation axioms. Existing coefficient audits remain unchanged.

`IntervalCollision.lean` adds five general lemmas and three finite controls.
For monotone coordinate prefix counters bounded by their positive periods,
equal injective periodic product states are exactly intervals containing
zero or a full period in every coordinate. Absence of such intervals is
equivalent to trace injectivity. The proof reuses `CollisionBridge` for
injective assignments. Five declarations have exactly `propext/Quot.sound`;
three finite controls have no axioms. The all-length connected recurrence,
c10 numerical coefficients, word-prefix instantiation and counting quotient
remain separate prose/computational components; see
[the sector note](../proof/simple-projection-sectors.md).

`CanonicalTrace.lean` adds 15 general bounded first-occurrence extraction
lemmas. They prove reconstruction, injective realization, visited-label
surjectivity, equality-pattern invariance and uniqueness of normalized
first-position shapes. `CanonicalControls.lean` adds three finite controls
distinguishing first-position labels from contiguous ordinal labels and
showing failure under noninjective relabeling. All 18 use exactly standard
`propext` and `Quot.sound`. See
[the exact scope](../proof/canonical-coordinate-extraction.md).

The complete projection/extraction and shuffle bijection is **not** formalized.
`RankCompression.lean` now proves 20 general lemmas giving an order-preserving
bijection from representative subtypes to `Fin r`, exact reconstruction,
injective decoding, label surjectivity and the literal restricted-growth
candidate bound. `RankControls.lean` checks the finite representative list,
compressed ordinal word and inverse lookup. All 23 audits use exactly standard
`propext` and `Quot.sound`, without choice. See
[the rank-compression scope](../proof/ordinal-rank-compression.md).

`EventShuffle.lean` adds 17 general lemmas proving an exact finite bijection
between event lists and compatible coordinate words/destination queues, and
conditional replay of coherent vertex paths after stationary-step deletion.
`EventControls.lean` adds five formal controls, including the recorded prism
eight-cycle path, exhausted/leftover queues and nonstationary coordinates.
Their exact hypotheses and axiom sets are in the audit and
[proof/coordinate-event-shuffle.md](../proof/coordinate-event-shuffle.md).

`ClosedWalk.lean` adds 19 general lemmas for factor-edge validity, exact
coordinate/product closure, closed-walk realization, endpoint normalization and
departure-list injectivity. `ClosedControls.lean` adds nine controls for the
prism, colliding interleavings, missing edges and paired triangle projections.
See [the closed-walk scope](../proof/closed-coordinate-walks.md).

`CycleTrace.lean` adds ten general lemmas proving modular adjacency for the
list-derived trace and an exact simple-cycle criterion in terms of length,
departure injectivity, factor walks and closure. `CycleControls.lean` adds
seven controls, including necessity of closure and the minimum cycle length.
See [the modular cycle scope](../proof/modular-cycle-trace.md).

`ExecutableTrace.lean` adds 16 general lemmas identifying the literal
Shuffle.vertices output with encoded typed departures, proving the collision
test equivalent to trace injectivity and closure from period-divisible step
counts. `ExecutableControls.lean` adds eight controls, including malformed
default inputs. See [the executable bridge](../proof/executable-coordinate-trace.md).

`WordGenerator.lean` adds 17 general lemmas proving exact multiplicity
soundness/completeness and duplicate-free enumeration for the literal axis-word
generator, filtered-list uniqueness and constructive typed axes.
`WordControls.lean` adds seven controls. See [the generator proof](../proof/axis-word-generator.md).

`PatternGenerator.lean` adds 16 general lemmas proving exact positionwise
prefix/closing semantics, cyclic-pattern completeness and unique enumeration
for the literal restricted-growth generator. `PatternControls.lean` adds seven
controls. See [the cyclic-pattern proof](../proof/cyclic-pattern-generator.md).

`NormalizedPattern.lean` adds 22 general lemmas connecting canonical ordinal
traces to exact generated-pattern membership, source equality patterns,
injective assignment reconstruction and selected-step preservation.
`NormalizedControls.lean` adds ten controls. See
[the canonical membership scope](../proof/canonical-pattern-membership.md).

Normalization inverses for arbitrary generated bounded templates, complete
product-cycle composition, quotient-motif classification, the cardinality
identity and the free 16-to-1
orbit quotient remain open. The full graph formula and source-owned graph-ring
theorems are not promoted. Kernel checks of the specified components do not
establish external mathematical acceptance or novelty.

`PartitionInversion.lean` adds twelve declarations independent of the shuffle
bridge: quotient factorization with explicit representatives, uniqueness,
discrete-kernel injectivity, a quotient-loop obstruction, finite integer sum
algebra, conditional finite inversion transport and two controls. The actual
Mobius cancellation identity is an explicit hypothesis of `finite_inversion`,
not a fully formalized factorial-weight theorem. The independent computation
checks it through Pi_10; numerical C10 coefficients and the ordinary-cycle
cardinality quotient remain outside this formal component. Six declarations
have no axioms, five have exactly propext, and uniqueness has exactly Quot.sound.
See `proof/partition-lattice-check.md` for computation and claim boundaries.
